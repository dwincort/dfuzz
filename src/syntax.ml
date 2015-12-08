(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Format
open Support.FileInfo

(* ---------------------------------------------------------------------- *)
(* Abstract Syntax Tree for sensitivities, terms and types                *)
(* ---------------------------------------------------------------------- *)

(* TODO: Modularize. TyLollipop -> Type.Lollipop, etc... *)

(* Binders are represented using Debruijn notation *)

(* Different types of variable binding, for debug purposes *)
type fuzz_binding =
    BiVar    (* Regular varible *)
  | BiTyVar  (* Type variable   *)

type var_info = {
  (* Indexes start a 0 *)
  v_index : int;

  (* Debug fields *)
  v_name  : string; (* The name is printed on screen, but it is ignored for all purposes *)
  v_size  : int;
  v_type  : fuzz_binding;
}

(* Helper to modify the index
var_shift : int         -- all variables with index greater than or equal to this value will be shifted
         -> int         -- the amount to shift by
         -> var_info    -- var_info to shift
         -> var_info    -- Updated var_info *)
let var_shift o n v = { v with
  v_index = if o <= v.v_index then v.v_index + n else v.v_index;
  v_size  = v.v_size  + n;
}

(* All of the fields are debug information *)
type binder_info = {
  b_name : string;       (* Name of the binder *)
  b_size : int;          (* How many outside binders we had when this binded was found *)
  b_type : fuzz_binding; (* What kind of binding this is *)
  b_prim : bool;         (* Is this a primitive *)
}

(* Kinds for type variables *)
type kind =
    Star
  | Size
  | Sens

(* Part 1: Sizes and Sensitivities *)

(* Sensitivities *)
type si =
  | SiZero
  | SiSucc  of si
  | SiInfty
  | SiConst of float
  | SiVar   of var_info
  | SiAdd   of si * si
  | SiMult  of si * si
  | SiLub   of si * si
  (* We only allow to sup to happen over the first variable *)
  | SiSup   of binder_info * kind * si

(* Map over the variables of a sensitivity type *)
let rec si_map n f si =
  let smf = si_map n f     in
  let smb = si_map (n+1) f in
  match si with
    SiVar   v       -> f n v
  | SiZero          -> SiZero
  | SiSucc  s       -> SiSucc (smf s)
  | SiConst c       -> SiConst c
  | SiAdd  (x, y)   -> SiAdd (smf x, smf y)
  | SiMult (x, y)   -> SiMult(smf x, smf y)
  | SiInfty         -> SiInfty
  | SiLub  (s1, s2) -> SiLub (smf s1, smf s2)
  | SiSup  (bi, k, s)      -> SiSup (bi, k, smb s)

(* Shifts all the variables greater or equal than o by n *)
let si_shift o n si =
  let f o v  = SiVar (var_shift o n v) in
  si_map o f si

type si_cs = SiEq of (si * si)

let cs_shift n d cs = match cs with
  | SiEq (s1, s2) -> SiEq (si_shift n d s1, si_shift n d s2)

(* Types *)

(* Primitive types *)
type ty_prim =
    PrimNum
  | PrimInt
  | PrimUnit
  | PrimBool
  | PrimString
  | PrimClipped
  | PrimDBS

(* Types with one argument *)
(* XXX: Extend to types with n-ary arguments *)
type ty_prim1 =
    Prim1Set
  | Prim1Bag
  | Prim1Fuzzy

(* Strings in the binders just for debug purposes *)
type ty =
  (* variables used in bindings *)
    TyVar  of var_info

  (* Primitive types *)
  | TyPrim  of ty_prim
  | TyPrim1 of (ty_prim1 * ty)

  (* ADT *)
  | TyUnion     of ty * ty
  | TyTensor    of ty * ty
  | TyAmpersand of ty * ty

  (* Functional type *)
  | TyLollipop of ty * si * ty

  (* Fixpoint type *)
  | TyMu of binder_info * ty

  (* Quantified types *)
  | TyForall of binder_info * kind * ty


(* map over types, first argument: action on vars, second argument
   action on evars, third argument action on sensitivities, 4th on sizes *)
let rec ty_map n fv fsi ty = match ty with
    TyVar v                 -> fv n v
  | TyPrim tp               -> TyPrim tp
  | TyPrim1 (tp, ty)        -> TyPrim1 (tp, ty_map n fv fsi ty)
  (* ADT *)
  | TyUnion(ty1, ty2)       -> TyUnion    (ty_map n fv fsi ty1, ty_map n fv fsi ty2)
  | TyTensor(ty1, ty2)      -> TyTensor   (ty_map n fv fsi ty1, ty_map n fv fsi ty2)
  | TyAmpersand(ty1, ty2)   -> TyAmpersand(ty_map n fv fsi ty1, ty_map n fv fsi ty2)
  (* *)
  | TyLollipop(ty1, s, ty2) -> TyLollipop(ty_map n fv fsi ty1, fsi n s, ty_map n fv fsi ty2)

  | TyMu(b, ty)             -> TyMu(b, ty_map (n+1) fv fsi ty)
  (* *)
  | TyForall(b, k, ty)      -> TyForall(b, k, ty_map (n+1) fv fsi ty)

let ty_shift o n ty =
  let fv  k v  = TyVar (var_shift k n v)      in
  let fsi k si = si_shift k n si              in
  ty_map o fv fsi ty

let ty_subst_shift x t k v =
  if (x+k) = v.v_index then
    (ty_shift 0 k t)
  else
    TyVar (var_shift (x+k) (-1) v)

(* Substitution ty[t/x] for type vars *)
let ty_subst x t ty =
  let f_si k si = si_shift (x + k) (-1) si in
  let f_ty      = ty_subst_shift x t       in
  ty_map 0 f_ty f_si ty

let ty_unfold ty = match ty with
  | TyMu(b, ty_i) -> ty_subst 0 (TyMu (b, ty_i)) ty_i
  | _             -> ty

(*********************************************************************)
(* Terms                                                             *)

(* Primitive Terms *)
type term_prim =
    PrimTUnit
  | PrimTNum    of float
  | PrimTInt    of int
  | PrimTBool   of bool
  | PrimTString of string
  | PrimTFun    of string * ty
  | PrimTDBS    of string

let type_of_prim t = match t with
    PrimTUnit       -> TyPrim PrimUnit
  | PrimTNum _      -> TyPrim PrimNum
  | PrimTInt _      -> TyPrim PrimInt
  | PrimTBool _     -> TyPrim PrimBool
  | PrimTString  _  -> TyPrim PrimString
  | PrimTFun(_, ty) -> ty
  | PrimTDBS _      -> TyPrim PrimDBS

type term =
  | TmVar of info * var_info
  (* Primitive terms *)
  | TmPrim     of info * term_prim

  | TmPair      of info * term * term
  | TmTensDest  of info * binder_info * binder_info * term * term
  (* & constructor *)
  | TmAmpersand of info * term * term
  | TmUnionCase of info * term * binder_info * term * binder_info * term
  (*                      t  of { inl(x)     => tm1  | inl(y)     => tm2  } *)

  (* Regular Abstraction and Applicacion *)
  | TmApp of info * term * term
  | TmAbs of info * binder_info * (si * ty) * ty option * term

  (* Recursive data types *)
  | TmFold    of info * ty * term
  | TmUnfold  of info * term

  (* Bindings *)
  | TmLet      of info * binder_info * si * term * term
  | TmLetRec   of info * binder_info * ty * term * term
  | TmSample   of info * binder_info * term * term

  (* Type Abstraction and Applicacion *)
  | TmTyAbs of info * binder_info * kind * term
  | TmTyApp of info * term * ty

  (* Type definitions *)
  | TmTypedef of info * binder_info * ty * term


let map_prim_ty n f p =
  match p with
    PrimTUnit       -> p
  | PrimTNum(_)     -> p
  | PrimTInt(_)     -> p
  | PrimTBool(_)    -> p
  | PrimTString(_)  -> p
  | PrimTFun(s, ty) -> PrimTFun(s, f n ty)
  | PrimTDBS _      -> p

let rec map_term_ty_aux n ft fsi tm =
  let tf n = map_term_ty_aux n ft fsi                  in
  let opf  = Option.map (ft n)                         in
  let psf = (fun (si, ty) -> (fsi n si, ft n ty))      in
  (* let opsf = Option.map (fun (si, ty) -> (si, f n ty)) in *)
  match tm with
    TmVar(i, v)                -> TmVar (i, v)
  | TmPrim(i, p)               -> TmPrim(i, map_prim_ty n ft p)

  (* Will die soon *)
  | TmPair(i,      tm1,      tm2)    ->
    TmPair(i, tf n tm1, tf n tm2)

  | TmTensDest(i, bi_x, bi_y,      tm,      tm_i) ->
    TmTensDest(i, bi_x, bi_y, tf n tm, tf n tm_i)

  | TmAmpersand(i,      tm1,      tm2)    ->
    TmAmpersand(i, tf n tm1, tf n tm2)

  | TmUnionCase(i,      tm, bi_l,      tm_l, bi_r,      tm_r)  ->
    TmUnionCase(i, tf n tm, bi_l, tf n tm_l, bi_r, tf n tm_r)

  (* Abstraction and application *)
  | TmAbs(i, bi,      osity,     orty,      tm)           ->
    TmAbs(i, bi,  psf osity, opf orty, tf n tm)

  | TmApp(i,      tm1,      tm2)          ->
    TmApp(i, tf n tm1, tf n tm2)

  (*  *)
  | TmLet(i, bi,       si,      tm,      tm_i)      ->
    TmLet(i, bi, fsi n si, tf n tm, tf n tm_i)

  | TmLetRec(i, bi,      ty,      tm,      tm_i) ->
    TmLetRec(i, bi, ft n ty, tf n tm, tf n tm_i)

  | TmSample(i, bi,      tm,      tm_i) ->
    TmSample(i, bi, tf n tm, tf n tm_i)

  (* Recursive datatypes *)
  | TmFold(i,      ty,      tm)           ->
    TmFold(i, ft n ty, tf n tm)

  | TmUnfold(i,      tm) ->
    TmUnfold(i, tf n tm)

  (* Type definition! *)
  | TmTypedef(i, bi,          ty,          tm)        ->
    TmTypedef(i, bi, ft (n+1) ty, tf (n+1) tm)

  (* Type abstraction and application *)
  | TmTyApp (i,      tm,      ty)     ->
    TmTyApp (i, tf n tm, ft n ty)

  | TmTyAbs (i, bi, k,          tm)  ->
    TmTyAbs (i, bi, k, tf (n+1) tm)


let map_term_ty fty fsi tm = map_term_ty_aux 0 fty fsi tm

(* Substitution of annotations in expressions *)

(* tm[t/x] *)
let term_ty_subst x t tm =
  let tsub  k = ty_subst (x+k) (ty_shift 0 (k-1) t) in
  let sisub k = si_shift k (-1)  in
  map_term_ty tsub sisub tm

(************************************************************************)
(* File info extraction *)

let tmInfo t = match t with
    TmVar(fi, _)                -> fi
  | TmPrim(fi, _)               -> fi

  | TmPair(fi, _, _)            -> fi
  | TmTensDest(fi,_,_,_,_)      -> fi

  | TmAmpersand(fi,_,_)         -> fi
  | TmUnionCase(fi,_,_,_,_,_)   -> fi

  (* Abstraction and application *)
  | TmAbs(fi,_,_,_,_)           -> fi
  | TmApp(fi, _, _)             -> fi

  (* Bindings *)
  | TmLet(fi,_,_,_,_)           -> fi
  | TmLetRec(fi,_,_,_,_)        -> fi
  | TmSample(fi,_,_,_)          -> fi

  (* Recursive datatypes *)
  | TmFold(fi,_,_)              -> fi
  | TmUnfold(fi,_)              -> fi

  (* Type abstraction and application *)
  | TmTyApp (fi, _, _)          -> fi
  | TmTyAbs (fi, _, _, _)       -> fi

  (* Misc *)
  | TmTypedef(fi,_,_,_)         -> fi
