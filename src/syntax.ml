(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Types
(* open Format *)
open Support.FileInfo

(* ---------------------------------------------------------------------- *)
(* Abstract Syntax Tree for sensitivities, terms and types                *)
(* ---------------------------------------------------------------------- *)

(* A helper function to modify the index of a variable.
var_shift : int         -- all variables with index greater than or equal to this value will be shifted
         -> int         -- the amount to shift (add) by
         -> var_info    -- var_info to shift
         -> var_info    -- Updated var_info *)
let var_shift o n v = { v with
  v_index = if o <= v.v_index then v.v_index + n else v.v_index;
  v_size  = v.v_size  + n;
}

let var_from_binder (index : int) (b : binder_info) : var_info = {
  v_index = index;
  v_name  = b.b_name;
  v_size  = b.b_size;
  v_type  = b.b_type;
}


(* ---------------------------------------------------------------------- *)
(* AST Mapping *)

(* Once again because of the potentially cyclic structure of the AST
   (that is, terms can contain sensitivites and sensitivites can contain 
   types), we define our ability to map over the AST in a mutually 
   recursive way.
   Note that these maps keep track of the type level Debruijn indeces. *)

(* Map over the terms of a sensitivity type *)
let rec si_map
  (ftm : term -> term)  (* The action to take on embedded terms *)
  (si : si)             (* The sensitivity to map over *)
  : si =
    match si with
    | SiInfty         -> si
    | SiConst c       -> si
    | SiTerm  t       -> SiTerm (ftm t)
    | SiAdd  (s1, s2) -> SiAdd  (si_map ftm s1, si_map ftm s2)
    | SiMult (s1, s2) -> SiMult (si_map ftm s1, si_map ftm s2)
    | SiLub  (s1, s2) -> SiLub  (si_map ftm s1, si_map ftm s2)

(* Map over types *)
let rec ty_map
  (n   : int)                   (* The number of binders deep we are *)
  (fv  : int -> var_info -> ty) (* The action on type variables *)
  (fsi : int -> si -> si)       (* The action on sesitivities *)
  (ty  : ty)                    (* The type to map over *)
  : ty = 
    let tmap n ty = ty_map n fv fsi ty in
    match ty with
      TyVar v                 -> fv n v
    | TyPrim tp               -> TyPrim tp
    | TyPrim1 (tp, ty)        -> TyPrim1 (tp, tmap n ty)
    (* ADT *)
    | TyUnion(ty1, ty2)       -> TyUnion    (tmap n ty1, tmap n ty2)
    | TyTensor(ty1, ty2)      -> TyTensor   (tmap n ty1, tmap n ty2)
    | TyAmpersand(ty1, ty2)   -> TyAmpersand(tmap n ty1, tmap n ty2)
    (* *)
    | TyLollipop(ty1, s, ty2) -> TyLollipop(tmap n ty1, fsi n s, tmap n ty2)
    
    | TyMu(b, ty)             -> TyMu(b, tmap (n+1) ty)
    (* *)
    | TyForall(b, ty)         -> TyForall(b, tmap (n+1) ty)

let rec tm_map
  (ntm : int)               (* The number of regular variable binders deep we are *)
  (nty : int)               (* The number of type variable binders deep we are *)
  (fv  : int -> int -> info -> var_info -> term) (* The action on regular variables (with the ntm value) *)
  (fty : int -> int -> ty -> ty)   (* Action to take on types *)
  (fsi : int -> int -> si -> si)   (* Action to take on sensitivites *)
  (tm : term)               (* The term to map over *)
  : term = 
  let tf ntm nty tm = tm_map ntm nty fv fty fsi tm in
  match tm with
  | TmVar (i, v)                    ->
    fv ntm nty i v
  
  | TmPrim(i, p) ->
    TmPrim(i, p)
    
  | TmPrimFun(i, s,             ty,                                                            tmtylst)  ->
    TmPrimFun(i, s, fty ntm nty ty, List.map (fun (tm, ty) -> (tf ntm nty tm, fty ntm nty ty)) tmtylst)
  
  | TmBag(i,             ty,                       tmlst) ->
    TmBag(i, fty ntm nty ty, List.map (tf ntm nty) tmlst)
  
  | TmPair(i,            tm1,            tm2)   ->
    TmPair(i, tf ntm nty tm1, tf ntm nty tm2)
  
  | TmTensDest(i, bi_x, bi_y,            tm,                tm_i)   ->
    TmTensDest(i, bi_x, bi_y, tf ntm nty tm, tf (ntm+2) nty tm_i)
  
  | TmAmpersand(i,            tm1,            tm2)  ->
    TmAmpersand(i, tf ntm nty tm1, tf ntm nty tm2)
  
  | TmLeft(i,            tm,             ty)    ->
    TmLeft(i, tf ntm nty tm, fty ntm nty ty)
  
  | TmRight(i,            tm,             ty)   ->
    TmRight(i, tf ntm nty tm, fty ntm nty ty)
  
  | TmUnionCase(i,            tm, bi_l,                tm_l, bi_r,                tm_r)   ->
    TmUnionCase(i, tf ntm nty tm, bi_l, tf (ntm+1) nty tm_l, bi_r, tf (ntm+1) nty tm_r)
  
  (* Abstraction and application *)
  | TmAbs(i, bi, (            si,             ty),                            orty,                tm)  ->
    TmAbs(i, bi, (fsi ntm nty si, fty ntm nty ty), (Option.map (fty ntm nty)) orty, tf (ntm+1) nty tm)
  
  | TmApp(i,            tm1,            tm2)    ->
    TmApp(i, tf ntm nty tm1, tf ntm nty tm2)
  
  (*  *)
  | TmLet(i, bi,             si,            tm,                tm_i)  ->
    TmLet(i, bi, fsi ntm nty si, tf ntm nty tm, tf (ntm+1) nty tm_i)
  
  | TmLetRec(i, bi,                 ty,                tm,                tm_i)   ->
    TmLetRec(i, bi, fty (ntm+1) nty ty, tf (ntm+1) nty tm, tf (ntm+1) nty tm_i)
  
  | TmSample(i, bi,            tm,                tm_i) ->
    TmSample(i, bi, tf ntm nty tm, tf (ntm+1) nty tm_i)
  
  (* Recursive datatypes *)
  | TmFold(i,             ty,            tm)    ->
    TmFold(i, fty ntm nty ty, tf ntm nty tm)
  
  | TmUnfold(i,            tm)    ->
    TmUnfold(i, tf ntm nty tm)
  
  (* Type definition *)
  | TmTypedef(i, bi,                 ty,                tm) ->
    TmTypedef(i, bi, fty ntm (nty+1) ty, tf ntm (nty+1) tm)
  
  (* Type abstraction and application *)
  | TmTyApp (i,            tm,             ty)  ->
    TmTyApp (i, tf ntm nty tm, fty ntm nty ty)
  
  | TmTyAbs (i, bi,                tm)    ->
    TmTyAbs (i, bi, tf ntm (nty+1) tm)
  
  (* Convenience *)
  | TmIfThenElse (i,            b,            t,            e)    ->
    TmIfThenElse (i, tf ntm nty b, tf ntm nty t, tf ntm nty e)




(* ---------------------------------------------------------------------- *)
(* Convenient functions *)



(* Shift all of the type variables by the given amount *)
let rec ty_shiftTy (o : int) (n : int) (ty : ty) : ty = 
  let fv  k v  = TyVar (var_shift k n v)      in
  let fsi k si = si_shiftTy k n si            in
  ty_map o fv fsi ty

and si_shiftTy (o : int) (n : int) (si : si) : si =
  si_map (tm_shiftTy o n) si

and tm_shiftTy (o : int) (n : int) (tm : term) : term = 
  let fv _ _ i v = TmVar(i,v)          in
  let fty _ k ty = ty_shiftTy k n ty in
  let fsi _ k si = si_shiftTy k n si in
  tm_map 0 o fv fty fsi tm


(* Shift all of the regular variables by the given amount *)
let rec tm_shiftTm (o : int) (n : int) (tm : term) : term = 
  let fv  k _ i v = TmVar (i, var_shift k n v) in
  let fty k _ ty = ty_shiftTm k n ty         in
  let fsi k _ si = si_shiftTm k n si         in
  tm_map o 0 fv fty fsi tm

and ty_shiftTm (o : int) (n : int) (ty : ty) : ty = 
  let fv _ v = TyVar v  in
  ty_map o fv (fun _ -> si_shiftTm o n) ty

and si_shiftTm (o : int) (n : int) (si : si) : si =
  si_map (tm_shiftTm o n) si


let rec tm_mapTm (f : info -> var_info -> term) (tm : term) : term = 
  let fv _ _ = f in
  let fty _ _ ty = ty_mapTm f ty in
  let fsi _ _ si = si_mapTm f si in
  tm_map 0 0 fv fty fsi tm
and ty_mapTm f ty = 
  let fv _ v = TyVar v in
  ty_map 0 fv (fun _ -> si_mapTm f) ty
and si_mapTm f si = si_map (tm_mapTm f) si




(* This performs a substitution of the form ty[t/x] for type variables.
   It can be called on types (ty_substTy) or terms (tm_substTy).  *)
let rec ty_substTy
    (t : ty)    (* The type to replace the variable with. *)
    (ktm : int) (* Initially, call with 0. *)
    (x : int)   (* The Debruijn index of the type variable we are replacing. *)
    (ty : ty)   (* The input type over which we are doing the substitution. *)
    : ty =
  let fv kty v = 
    if kty = v.v_index then
      ty_shiftTm 0 ktm (ty_shiftTy 0 kty t)
    else
      TyVar (var_shift kty (-1) v)    in
  let fsi k si = si_substTy t ktm k si  in
  ty_map x fv fsi ty

and si_substTy (t : ty) (ktm : int) (x : int) (si : si) : si =
  si_map (tm_substTy t ktm x) si

and tm_substTy (t : ty) (ktm : int) (x : int) (tm : term) : term =
  let fv _ _ i v = TmVar(i,v) in
  tm_map ktm x fv (ty_substTy t) (si_substTy t) tm



(* ty_unfold is used to unfold mu types *)
let ty_unfold ty = match ty with
  | TyMu(b, ty_i) -> ty_substTy (TyMu (b, ty_i)) 0 0 ty_i
  | _             -> ty


(* This performs a substitution of the form tm[t/x] for variables. *)
let rec tm_substTm
    (t : term)  (* The term to replace the variable with. *)
    (x : int)   (* The Debruijn index of the variable we are replacing. *)
    (kty : int) (* Initially, call with 0. *)
    (tm : term) (* The input term over which we are doing the substitution. *)
    : term =
  let fv ktm kty i v = if ktm = v.v_index
    then tm_shiftTy 0 kty (tm_shiftTm 0 (ktm-x) t)
    else TmVar (i, var_shift ktm (-1) v) in
  let fty k kty ty = ty_substTm t k kty ty  in
  let fsi k kty si = si_substTm t k kty si  in
  tm_map x kty fv fty fsi tm

and ty_substTm (t : term) (x : int) (kty : int) (ty : ty) : ty = 
  let fv _ v = TyVar v in
  ty_map kty fv (si_substTm t x) ty
and si_substTm (t : term) (x : int) (kty : int) (si : si) : si = 
  si_map (tm_substTm t x kty) si




(************************************************************************)
(* Term and type valuation and equality *)

let rec tmEq (t1 : term) (t2 : term) : bool = 
  match t1, t2 with
  | TmVar(_,v1), 
    TmVar(_,v2) -> v1 = v2
  | TmPrim(_,p1), 
    TmPrim(_,p2) -> p1 = p2
  | TmPrimFun(_,_,ty1,tmtyl1), 
    TmPrimFun(_,_,ty2,tmtyl2) -> false
  | TmBag(_, ty1, tml1), 
    TmBag(_, ty2, tml2) -> false
  | TmPair(_, t1a, t1b),
    TmPair(_, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmTensDest(_, _, _, t1a, t1b),
    TmTensDest(_, _, _, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmAmpersand(_, t1a, t1b),
    TmAmpersand(_, t2a, t2b) -> tmEq t1a t2a && tmEq t1b t2b
  | TmLeft(_, tm1, ty1),
    TmLeft(_, tm2, ty2) -> tmEq tm1 tm2
  | TmRight(_, tm1, ty1),
    TmRight(_, tm2, ty2) -> tmEq tm1 tm2
  | TmUnionCase(_, t1a, _, t1b, _, t1c),
    TmUnionCase(_, t2a, _, t2b, _, t2c) -> tmEq t1a t2a && tmEq t1b t2b && tmEq t1c t2c
  | TmFold(_, ty1, tm1),
    TmFold(_, ty2, tm2) -> tmEq tm1 tm2
  | _,_ -> false

let rec tmIsVal (t : term) : bool = match t with
  | TmPrim(_,_)     -> true
  | TmBag(_,_,_)    -> true
  | TmPair(_,t1,t2) -> tmIsVal t1 && tmIsVal t2
  | TmAmpersand(_, t1, t2)  -> tmIsVal t1 && tmIsVal t2
  | TmLeft(_,t,_)   -> tmIsVal t
  | TmRight(_,t,_)  -> tmIsVal t
  | TmAbs(_,_,_,_,_)    -> true
  | TmFold(_,_,_)   -> true
  | TmTyAbs(_,_,_)  -> true
  | _               -> false

let rec tyIsVal (t : ty) : bool = match t with
  | TyVar _             -> false
  | TyPrim  _           -> true
  | TyPrim1(_, t)       -> tyIsVal t
  | TyUnion(t1, t2)     -> tyIsVal t1 && tyIsVal t2
  | TyTensor(t1, t2)    -> tyIsVal t1 && tyIsVal t2
  | TyAmpersand(t1, t2) -> tyIsVal t1 && tyIsVal t2
  | TyLollipop(t1,_,t2) -> tyIsVal t1 && tyIsVal t2
  | TyMu(_,t)           -> true
  | TyForall(_,_)       -> true



(************************************************************************)
(* File info extraction *)

let tmInfo t = match t with
    TmVar(fi, _)                -> fi
  | TmPrim(fi, _)               -> fi
  | TmPrimFun(fi, _, _, _)      -> fi
  
  | TmBag(fi, _, _)             -> fi

  | TmPair(fi, _, _)            -> fi
  | TmTensDest(fi,_,_,_,_)      -> fi

  | TmAmpersand(fi,_,_)         -> fi
  | TmLeft(fi,_,_)              -> fi
  | TmRight(fi,_,_)             -> fi
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
  | TmTyAbs (fi, _, _)          -> fi

  (* Misc *)
  | TmTypedef(fi,_,_,_)         -> fi

  (* Convenience *)
  | TmIfThenElse (fi,_,_,_)     -> fi
