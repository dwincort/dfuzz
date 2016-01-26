(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Types
open Syntax

open Support.FileInfo

module Opt = Support.Options
module P   = Print
module Fmt = Format

(* Type checking and synthesis engine for Fuzz.

*)

(* Errors *)
type ty_error_elem =
| SensError    of si * si
| MoreGeneral  of ty * ty
| TypeMismatch of ty * ty
| TypeInst     of ty * ty
| CannotApply  of ty * ty
| OccursCheck  of var_info * ty
| WrongShape   of ty * string
| NotSubtype   of ty * ty
| UnevalSensTerm of term
| Internal     of string

let ty_seq = ref 0

let pp_tyerr ppf s = match s with
  | SensError (si1, si2)  -> Fmt.fprintf ppf "EEE [%3d] Cannot satisfy constraint %a <= %a" !ty_seq P.pp_si si1 P.pp_si si2
  | MoreGeneral(ty1, ty2) -> Fmt.fprintf ppf "EEE [%3d] %a is not more general than %a"     !ty_seq P.pp_type ty1 P.pp_type ty2
  | TypeInst(ty1, ty2)    -> Fmt.fprintf ppf "EEE [%3d] Type %a is not instance of %a"      !ty_seq P.pp_type ty1 P.pp_type ty2
  | TypeMismatch(ty1, ty2)-> Fmt.fprintf ppf "EEE [%3d] Cannot unify %a with %a"        !ty_seq P.pp_type ty1 P.pp_type ty2
  | CannotApply(ty1, ty2) -> Fmt.fprintf ppf "EEE [%3d] Cannot apply %a to %a"    !ty_seq P.pp_type ty1 P.pp_type ty2
  | OccursCheck(v, ty)    -> Fmt.fprintf ppf "EEE [%3d] Cannot build infinite type %a = %a" !ty_seq P.pp_vinfo v P.pp_type ty
  | WrongShape(ty, sh)    -> Fmt.fprintf ppf "EEE [%3d] Type %a has wrong shape, expected %s type." !ty_seq P.pp_type ty sh
  | NotSubtype(ty1,ty2)   -> Fmt.fprintf ppf "EEE [%3d] %a is not a subtype of %a" !ty_seq P.pp_type ty1 P.pp_type ty2
  | Internal s            -> Fmt.fprintf ppf "EEE [%3d] Internal error: %s" !ty_seq s
  | UnevalSensTerm t      -> Fmt.fprintf ppf "EEE [%3d] Terms in sensitivity are not allowed in the red zone! Found: %a" !ty_seq P.pp_term t

let typing_error fi = Support.Error.error_msg    Opt.TypeChecker fi
let typing_error_pp = Support.Error.error_msg_pp Opt.TypeChecker

let ty_warning fi = Support.Error.message 1 Opt.TypeChecker fi
let ty_info    fi = Support.Error.message 2 Opt.TypeChecker fi
let ty_info2   fi = Support.Error.message 3 Opt.TypeChecker fi
let ty_debug   fi = Support.Error.message 4 Opt.TypeChecker fi
let ty_debug2  fi = Support.Error.message 5 Opt.TypeChecker fi
let ty_debug3  fi = Support.Error.message 6 Opt.TypeChecker fi

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

(* Reader/Error monad for type-checking *)
module TypeCheckMonad = struct
  open Ctx
  
  (* A checker contains both the context as well as a bool that indicates if 
     this check will also check sensitivities (true checks and false does not *)
  type 'a checker = (context * bool) -> ('a, ty_error_elem withinfo) result
  
  let (>>=) (m : 'a checker) (f : 'a -> 'b checker) : 'b checker =
    fun ctx ->
      match m ctx with
      | Ok res  -> f res ctx
      | Error e -> Error e
  
  let (>>) m f = m >>= fun _ -> f
  
  let return (x : 'a) : 'a checker = fun ctx -> Ok x
  
  let rec mapM (f : 'a -> 'b checker) (lst : 'a list) : ('b list) checker = 
    match lst with
      | []    -> return []
      | x::xs -> f x        >>= fun y  ->
                 mapM f xs  >>= fun ys ->
                 return (y::ys)
  
  let rec mapM2 (f : 'a -> 'b -> 'c checker) (lstA : 'a list) (lstB : 'b list) : ('c list) checker = 
    match lstA, lstB with
      | x::xs, y::ys -> f x y         >>= fun z  ->
                        mapM2 f xs ys >>= fun zs ->
                        return (z::zs)
      | _   -> return []
  
  let fail (i : info) (e : ty_error_elem) : 'a checker = fun _ ->
    Error { i = i; v = e }
  
  let get_ctx : context checker =
    fun ctxb -> Ok (fst ctxb)
  
  let should_check_sens : bool checker =
    fun ctxb -> Ok (snd ctxb)
  
  let get_ctx_length : int checker =
    get_ctx                             >>= fun ctx ->
    return @@ List.length ctx.var_ctx
  
  let with_new_ctx (f : context -> context) (m : 'a checker) : 'a checker =
    fun (ctx,b) -> m (f ctx,b)
  
  (* Extend the context with a type binding and run a computation *)
  let with_extended_ty_ctx (v : string) (m : 'a checker) : 'a checker =
    with_new_ctx (extend_ctx_with_tyvar' v) m
  
  (* Extend the context with a value binding and run a computation. The
     computation is assumed to produce a list of results, one for each
     variable in the extended context. That list is destructed, and the
     result corresponding to the new variable is returned separately for
     convenience. *)
  let with_extended_ctx (i : info) (v : string) (ty : ty) (m : ('a * 'b list) checker) :
      ('a * 'b * 'b list) checker =
    with_new_ctx (extend_ctx_with_var' v ty) m >>= fun (res, res_ext_ctx) ->
    match res_ext_ctx with
    | res_v :: res_ctx -> return (res, res_v, res_ctx)
    | [] -> fail i @@ Internal "Computation on extended context didn't produce enough results"
  
  (* Similar to the one above, but with two variables. vx has index 1 in
     the extended context, while vy has index 0. The order of the
     returned results matches those of the arguments. *)
  let with_extended_ctx_2 (i : info)
      (vx : string) (tyx : ty) (vy : string) (tyy : ty)
      (m : ('a * 'b list) checker) : ('a * 'b * 'b * 'b list) checker =
    with_new_ctx (fun ctx -> extend_ctx_with_var' vy tyy
                            (extend_ctx_with_var' vx tyx ctx)) m >>= fun (res, res_ext_ctx) ->
    match res_ext_ctx with
    | res_y :: res_x :: res_ctx -> return (res, res_x, res_y, res_ctx)
    | _ -> fail i @@ Internal "Computation on extended context didn't produce enough results"
  
  (* Get the type of the given variable *)
  let get_var_ty (v : var_info) : ty checker =
    get_ctx >>= fun ctx ->
    return @@ snd (access_var ctx v.v_index)
end

module TypeSens = struct
  open TypeCheckMonad
  
  (* Constants *)
  let si_zero  = SiConst 0.0
  let si_one   = SiConst 1.0
  let si_infty = SiInfty
  
  let rec si_simpl' (si : si) : si checker = match si with
    | SiInfty   -> return @@ si
    | SiConst _ -> return @@ si
    | SiTerm(TmPrim(_, PrimTNum(f)))  -> return @@ SiConst f
    | SiTerm(TmPrim(_, PrimTInt(i)))  -> return @@ SiConst (float_of_int i)
    | SiTerm(TmPrim(_, PrimTBool(b))) -> return @@ if b then si_infty else si_zero
    | SiTerm(t) -> fail (tmInfo t) @@ UnevalSensTerm t
    | SiAdd (si1, si2)  ->
        si_simpl' si1 >>= fun si1 ->
        si_simpl' si2 >>= fun si2 ->
        begin match si1, si2 with
          | SiInfty, _  -> return @@ SiInfty
          | _, SiInfty  -> return @@ SiInfty
          | SiConst x1, SiConst x2 -> return @@ SiConst (x1 +. x2)
          | _   -> fail dummyinfo @@ Internal "Bad state when adding sensitivities"
        end
    | SiMult(si1, si2)  -> 
        si_simpl' si1 >>= fun si1 ->
        si_simpl' si2 >>= fun si2 ->
        begin match si1, si2 with
          | SiConst 0.0, _ -> return @@ si_zero
          | _, SiConst 0.0 -> return @@ si_zero
          | SiInfty, _  -> return @@ SiInfty
          | _, SiInfty  -> return @@ SiInfty
          | SiConst x1, SiConst x2 -> return @@ SiConst (x1 *. x2)
          | _   -> fail dummyinfo @@ Internal "Bad state when multiplying sensitivities"
        end
    | SiLub (si1, si2)  -> 
        si_simpl' si1 >>= fun si1 ->
        si_simpl' si2 >>= fun si2 ->
        begin match si1, si2 with
          | SiInfty, _            -> return @@ SiInfty
          | _, SiInfty            -> return @@ SiInfty
          | SiConst x, SiConst y  -> return @@ SiConst (if x > y then x else y)
          | _   -> fail dummyinfo @@ Internal "Bad state when LUBing sensitivities"
        end
    
  let si_simpl (si : si) : si checker = 
    should_check_sens >>= fun b ->
    if b then si_simpl' si else return si
  
  let rec si_simpl_ty' (ty : ty) : ty checker = 
    match ty with
    | TyVar v                 -> return ty
    | TyPrim tp               -> return ty
    | TyPrim1 (tp, ty)        -> si_simpl_ty' ty  >>= fun ty' -> return @@ TyPrim1 (tp, ty')
    | TyUnion (ty1, ty2)      -> si_simpl_ty' ty1 >>= fun ty1 -> 
                                 si_simpl_ty' ty2 >>= fun ty2 -> return @@ TyUnion    (ty1, ty2)
    | TyTensor(ty1, ty2)      -> si_simpl_ty' ty1 >>= fun ty1 -> 
                                 si_simpl_ty' ty2 >>= fun ty2 -> return @@ TyTensor   (ty1, ty2)
    | TyAmpersand(ty1, ty2)   -> si_simpl_ty' ty1 >>= fun ty1 -> 
                                 si_simpl_ty' ty2 >>= fun ty2 -> return @@ TyAmpersand(ty1, ty2)
    | TyLollipop(ty1, s, ty2) -> si_simpl_ty' ty1 >>= fun ty1 -> 
                                 si_simpl' s     >>= fun s   ->
                                 si_simpl_ty' ty2 >>= fun ty2 -> return @@ TyLollipop(ty1, s, ty2)
    | TyMu(b, ty)             -> si_simpl_ty' ty  >>= fun ty  -> return @@ TyMu(b, ty)
    | TyForall(b, ty)         -> si_simpl_ty' ty  >>= fun ty  -> return @@ TyForall(b, ty)
    
  let si_simpl_ty (ty : ty) : ty checker = 
    should_check_sens >>= fun b ->
    if b then si_simpl_ty' ty else return ty
  
  (* Check that the first sensitivity is less than the second *)
  let check_sens_leq i (sil : si) (sir : si) : unit checker =
    should_check_sens >>= fun b ->
    if (not b) then return () else
    si_simpl' sil >>= fun sil ->
    si_simpl' sir >>= fun sir ->
    let res = match sil, sir with
      | _, SiInfty -> true
      | SiConst l, SiConst r -> (l <= r +. 0.0001)
      | _, _ -> false
    in if res then return () else fail i @@ SensError(sil, sir)
  
  (* A list only with zero sensitivities *)
  let rec zeros (n : int) : si list =
    if n = 0 then [] else si_zero :: zeros (n - 1)
  
  (* A list with zero sensitivities, except for one variable *)
  (* Note that this has to be kept in sync with the actual ctx *)
  let singleton (n : int) (v : var_info) : si list =
    let rec aux n l =
      if n = 0 then l
      else let si = if n = v.v_index + 1 then si_one else si_zero in
           aux (n - 1) (si :: l) in
    aux n []
  
  let si_add  (si1 : si) (si2 : si) : si = SiAdd (si1, si2)
  let si_mult (si1 : si) (si2 : si) : si = SiMult(si1, si2)
  let si_lub  (si1 : si) (si2 : si) : si = SiLub (si1, si2)
  
  let add_sens (sis1 : si list) (sis2 : si list) : (si list) =
    List.map2 si_add sis1 sis2
  
  let scale_sens (si : si) (sis : si list) : (si list) =
    List.map (si_mult si) sis
  
  let lub_sens (sis1 : si list) (sis2 : si list) : (si list) =
    List.map2 si_lub sis1 sis2
  
end

module TypeInf = struct
  (* This is good for return, eq, etc... it should be extended
     systematically instead of the current hack *)
  let infer_tyapp_very_simple (i : info) (ty : ty) (ty_arg : ty) : (ty * si) option =
    match ty with
    | TyLollipop(TyVar v, si, tyb) ->
      if v.v_index = 0 then
        let nt = ty_substTy ty_arg 0 0 tyb in
        ty_debug i "==> [%3d] Inferring type application from @[%a@] to @[%a@]" !ty_seq Print.pp_type tyb Print.pp_type nt;
        Some (nt, si)
      else
        None
    | TyLollipop(TyPrim1 (t, TyVar v), si, tyb) ->
      begin match ty_arg with
      | TyPrim1 (t1, ty_arg') ->
        if v.v_index = 0 && t1 = t then
          let nt = ty_substTy ty_arg' 0 0 tyb in
          ty_debug i "==> [%3d] Inferring container type application from @[%a@] to @[%a@]" !ty_seq Print.pp_type tyb Print.pp_type nt;
          Some (nt, si)
        else
          None
      | _ -> None
      end
    | _ -> None

end

module TypeSub = struct
  open Ctx
  open TypeCheckMonad
  
  let check_prim_sub (i : info) (ty_f : ty_prim) (ty_a : ty_prim) : unit checker =
    match ty_f, ty_a with
    | PrimNum, PrimClipped  -> return ()
    | PrimNum, PrimInt      -> return ()
    | _   when ty_f = ty_a  -> return ()
    | _                     -> fail i @@ NotSubtype (TyPrim ty_f, TyPrim ty_a)

  (* Check whether ty_1 is a subtype of ty_2, generating the necessary
     constraints along the way. *)
  let rec check_type_sub (i : info) (ty_1 : ty) (ty_2 : ty) : unit checker =
    let fail = fail i @@ NotSubtype (ty_1, ty_2) in
    match ty_1, ty_2 with
    | TyVar v1, TyVar v2   ->
      if v1 = v2 then return () else fail

    | TyPrim p1, TyPrim p2 -> check_prim_sub i p1 p2

    | TyPrim1(pl, tyl), TyPrim1(pr, tyr) ->
      if pl = pr then check_type_sub i tyl tyr else fail

    | TyUnion(tyl1, tyl2), TyUnion(tyr1, tyr2) ->
      check_type_sub i tyl1 tyr1 >>
      check_type_sub i tyl2 tyr2

    | TyTensor(tyl1, tyl2), TyTensor(tyr1, tyr2) ->
      check_type_sub i tyl1 tyr1 >>
      check_type_sub i tyl2 tyr2

    | TyAmpersand(tyl1, tyl2), TyAmpersand(tyr1, tyr2) ->
      check_type_sub i tyl1 tyr1 >>
      check_type_sub i tyl2 tyr2

    | TyLollipop(tyl1, sil, tyl2), TyLollipop(tyr1, sir, tyr2) ->
      check_type_sub i tyr1 tyl1 >>
      check_type_sub i tyl2 tyr2 >>
      TypeSens.check_sens_leq i sir sil

    | TyMu(_bl, tyl), TyMu(_br, tyr) ->
      check_type_sub i tyl tyr

    | TyForall(bl, tyl), TyForall(_br, tyr) ->
      with_new_ctx (extend_ctx_with_tyvar' bl.b_name) (check_type_sub i tyl tyr)

    | _, _ -> fail

  (* Check whether ty is compatible (modulo subtyping) with annotation
     ann, returning the resulting type. *)
  let check_type_ann (i : info) (ann : ty option) (ty : ty) : ty checker =
    match ann with
    | Some ty' -> check_type_sub i ty ty' >> return ty'
    | None -> return ty

  (* Check that the type is a type application. Return the type under the 
     forall. *)
  let check_ty_app_shape i ty_arr =
    match ty_arr with
    | TyForall(_b, ty)    -> return ty
    | _                   -> fail i @@ WrongShape(ty_arr, "forall")

  let check_app i ty_arr ty_arg =
    ty_debug i "<-> [%3d] Application of @[%a@] to @[%a@]" !ty_seq Print.pp_type ty_arr Print.pp_type ty_arg;
    match ty_arr with
    (* Here we do inference of type applications *)
    | TyForall(_bi, ty)   ->
      let tso = TypeInf.infer_tyapp_very_simple i ty ty_arg in
      begin match tso with
        | Some ts -> return ts
        | None    -> fail i @@ CannotApply(ty, ty_arg)
      end
    | TyLollipop(tya, si, tyb) ->
      check_type_sub i tya ty_arg >>
      return (tyb, si)
    | _                        -> fail i @@ CannotApply(ty_arr, ty_arg)

  let check_fuzz_shape i ty =
    match ty with
    | TyPrim1 (Prim1Fuzzy, ty) -> return ty
    | _                        -> fail i @@ WrongShape (ty, "fuzzy")

  let check_bag_shape i ty =
    match ty with
    | TyPrim1 (Prim1Bag, ty)   -> return ty
    | _                        -> fail i @@ WrongShape (ty, "bag")

  let check_tensor_shape i ty =
    match ty with
    | TyTensor(ty1, ty2) -> return (ty1, ty2)
    | _                  -> fail i @@ WrongShape (ty, "tensor")

  let check_union_shape i ty =
    match ty with
    | TyUnion(ty1, ty2) -> return (ty1, ty2)
    | _                 -> fail i @@ WrongShape (ty, "union")

  let check_mu_shape i ty =
    match ty with
    | TyMu(_, _)          -> return (ty_unfold ty)
    | _                   -> fail i @@ WrongShape (ty, "mu")

end


(**********************************************************************)
(* Main typing routine                                                *)
(**********************************************************************)
open TypeSens
open TypeSub
open TypeCheckMonad

let reportSensitivity (level : int) (fi : info) (bi : binder_info) (si : si) : si checker =
  should_check_sens >>= fun b ->
  if b then
    si_simpl si >>= fun si ->
    Support.Error.message level Opt.TypeChecker fi
      "### Inferred sensitivity for binder @[%a@] is @[%a@]" P.pp_binfo bi P.pp_si si;
    return si
  else return si


let type_of_prim (t : term_prim) : ty = match t with
    PrimTUnit       -> TyPrim PrimUnit
  | PrimTNum _      -> TyPrim PrimNum
  | PrimTInt _      -> TyPrim PrimInt
  | PrimTBool _     -> TyPrim PrimBool
  | PrimTString  _  -> TyPrim PrimString
  | PrimTClipped _  -> TyPrim PrimClipped


(* Given a term t and a context ctx for that term, check whether t is
   typeable under ctx, returning a type for t, a list of synthesized
   sensitivities for ctx, and a list of constraints that need to be
   satisfied in order for the type to be valid. Raises an error if it
   detects that no typing is possible. *)

let rec type_of (t : term) : (ty * si list) checker  =

  ty_debug (tmInfo t) "--> [%3d] Enter type_of: @[%10a@]" !ty_seq
    (Print.limit_boxes Print.pp_term) t; incr ty_seq;

  (match t with
  (* Variables *)
  | TmVar(i, v)  ->
    get_ctx_length              >>= fun len ->
    get_var_ty v                >>= fun ty  -> 
    return (ty, singleton len v)

  (* Primitive terms *)
  | TmPrim(_, pt) ->
    get_ctx_length >>= fun len ->
    return (type_of_prim pt, zeros len)

  | TmPrimFun(i, s, ty, tmtylst) ->
    ty_debug (tmInfo t) "--> [%3d] Type checking primfun %s" !ty_seq s;
    si_simpl_ty ty >>= fun ty ->
    mapM (fun (tm,ety) -> 
      type_of tm >>= fun (aty, _) ->
      ty_debug (tmInfo t) "--> [%3d] %s Verifying that type %a is a subtype of type %a" !ty_seq s Print.pp_type aty Print.pp_type ety;
      check_type_sub i ety aty) tmtylst >>
    get_ctx_length >>= fun len ->
    return (ty, zeros len)
  
  | TmBag(i, ty, tmlst) -> 
    check_bag_shape i ty >>= fun ity ->
    mapM (fun tm -> 
      type_of tm >>= fun (aty, _) ->
      check_type_sub i aty ity) tmlst >>
    get_ctx_length >>= fun len ->
    return (ty, zeros len)
    
  (************************************************************)
  (* Abstraction and Application *)
  (* λ (x :[si] tya_x) : tya_tm { tm } *)
  | TmAbs(i, b_x, (sia_x, tya_x), otya_tm, tm) ->

    si_simpl sia_x                                    >>= fun sia_x ->
    with_extended_ctx i b_x.b_name tya_x (type_of tm) >>= fun (ty_tm, si_x, sis) ->

    reportSensitivity 4 (tmInfo t) b_x si_x >>= fun si_x ->

    check_type_ann i otya_tm ty_tm                  >>
    check_sens_leq i si_x sia_x                     >>
    return (TyLollipop (tya_x, sia_x, ty_tm), sis)

  (* tm1 !ᵢβ → α, tm2: β *)
  | TmApp(i, tm1, tm2)                              ->

    type_of tm1 >>= fun (ty1, sis1) ->
    type_of tm2 >>= fun (ty2, sis2) ->

    (* Checks that ty1 has shape !ᵢβ → α, and that ty2 is and instance of β.
       Returns α and the sensitivity inside ty1 *)
    check_app i ty1 ty2 >>= fun (tya, r) ->

    (* We scale by the sensitivity in the type, which comes from an annotation *)
    return (tya, add_sens sis1 (scale_sens r sis2))

  (************************************************************)
  (* Identical to app + lam, this rule exists in order to avoid too
     many type annotations! *)
  (* let x [: sia_x] = tm_x in e *)
  | TmLet(i, x, sia_x, tm_x, e)                   ->

    type_of tm_x >>= fun (ty_x, sis_x)  ->

    ty_debug i "### Type of binder %a is %a" Print.pp_binfo x Print.pp_type ty_x;

    with_extended_ctx i x.b_name ty_x (type_of e) >>= fun (ty_e, si_x, sis_e) ->
    reportSensitivity 4 (tmInfo t) x si_x         >>= fun si_x ->
    check_sens_leq i si_x sia_x                   >>
    return (ty_e, add_sens sis_e (scale_sens si_x sis_x))

  (* function x <args ...> : tya_x { tm_x }; e *)
  | TmLetRec(i, x, tya_x, tm_x, e)                      ->

    with_extended_ctx i x.b_name tya_x (type_of tm_x) >>= fun (ty_x, si_x, sis_x) ->

    check_type_sub i ty_x tya_x >>

    with_extended_ctx i x.b_name tya_x (type_of e) >>= fun (ty_e, si_x', sis_e) ->

    ty_debug i "### Type of binder %a is %a" Print.pp_binfo x Print.pp_type ty_x;
    return (ty_e, add_sens sis_e (scale_sens (si_mult si_infty si_x') sis_x))  (* TODO: This is an instance of infinity times (potentially) zero *)

  | TmInfCheck(i, tm) -> type_of tm

  (* sample b_x = tm_x; e *)
  | TmSample(i, b_x, tm_x, e)                              ->

    type_of tm_x            >>= fun (ty_x, sis_x) ->
    check_fuzz_shape i ty_x >>= fun ty_x ->

    with_extended_ctx i b_x.b_name ty_x (type_of e) >>= fun (ty_e, si_x, sis_e) ->

(*     ty_debug (tmInfo t) "### [%3d] Sample for binder @[%a@] with sens @[%a@]" !ty_seq P.pp_binfo b_x P.pp_si si_x; *)
    reportSensitivity 4 (tmInfo t) b_x si_x >>= fun si_x ->

    check_fuzz_shape i ty_e                         >>

    (* The inferred sensitivity of x can be ignored. Once the result
       of a differentially private computation has been published, it
       can be used without any restriction. *)
    return (ty_e, add_sens sis_x sis_e)

  (* Tensor and & *)
  | TmPair(i, e1, e2) ->

    type_of e1 >>= fun (ty1, sis1) ->
    type_of e2 >>= fun (ty2, sis2) ->

    return @@ (TyTensor(ty1, ty2), add_sens sis1 sis2)

  | TmAmpersand(i, tm1, tm2)      ->

    type_of tm1 >>= fun (ty1, sis1) ->
    type_of tm2 >>= fun (ty2, sis2) ->

    return (TyAmpersand(ty1, ty2), lub_sens sis1 sis2)

  (************************************************************)
  (* Data type manipulation *)
  | TmFold(i, ty, tm)               ->

    check_mu_shape i ty             >>= fun ty_unf ->
    type_of tm                      >>= fun (ty_tm, sis_tm) ->
    check_type_sub i ty_unf ty_tm   >>
    check_type_sub i ty_tm ty_unf   >>
    return (ty, sis_tm)

  | TmUnfold (i, tm)                ->

    type_of tm                      >>= fun (ty_tm, sis_tm) ->
    check_mu_shape i ty_tm          >>= fun ty_unf ->
    return (ty_unf, sis_tm)

  (* Type Alias
     typedef n = tdef_ty; tm *)
  | TmTypedef(i, n, tdef_ty, tm)    ->

    ty_debug3 i "Calling typedef %a = %a on term %a" Print.pp_binfo n Print.pp_type tdef_ty Print.pp_term tm;

    (* We just substitute the type for the variable. *)
    type_of (tm_substTy (ty_shiftTy 0 (-1) tdef_ty) 0 0 tm)

  (* let (x,y) = e in e' *)
  | TmTensDest(i, x, y, e, t) ->

    type_of e >>= fun (ty_e, sis_e) ->
    check_tensor_shape i ty_e >>= fun (ty_x, ty_y) ->

    (* Extend context with x and y *)
    with_extended_ctx_2 i x.b_name ty_x y.b_name ty_y (type_of t) >>= fun (ty_t, si_x, si_y, sis_t) ->

    reportSensitivity 4 (tmInfo t) x si_x   >>= fun si_x ->
    reportSensitivity 4 (tmInfo t) y si_y   >>= fun si_y ->

    return (ty_t, add_sens sis_t (scale_sens (si_lub si_x si_y) sis_e))
  
  | TmLeft(i, t, tyr) ->
    type_of t >>= fun (ty_t, sis_t) ->
    return (TyUnion(ty_t, tyr), sis_t)

  | TmRight(i, t, tyl) ->
    type_of t >>= fun (ty_t, sis_t) ->
    return (TyUnion(tyl, ty_t), sis_t)

  (* case e of inl(x) => e_l | inr(y) e_r *)
  | TmUnionCase(i, e, b_x, e_l, b_y, e_r)      ->

    type_of e >>= fun (ty_e, sis_e) ->

    check_union_shape i ty_e >>= fun (ty1, ty2) ->

    with_extended_ctx i b_x.b_name ty1 (type_of e_l) >>= fun (tyl, si_x, sis_l) ->
    with_extended_ctx i b_y.b_name ty2 (type_of e_r) >>= fun (tyr, si_y, sis_r) ->
    
    reportSensitivity 4 (tmInfo t) b_x si_x          >>= fun si_x ->
    reportSensitivity 4 (tmInfo t) b_y si_y          >>= fun si_y ->
    
    (* TODO: Rather than check_type_sub in both directions, we want to find the 
             most general type of tyl and tyr and return that. *)
    check_type_sub i tyr tyl >>
    check_type_sub i tyl tyr >>

    return (tyl, add_sens (lub_sens sis_l sis_r) (scale_sens (si_lub si_x si_y) sis_e))

  (* Type/Sensitivity Abstraction and Application *)
  | TmTyAbs(i, bi, tm) ->

    with_extended_ty_ctx bi.b_name (type_of tm) >>= fun (ty, sis) ->
    return (TyForall(bi, ty), sis)

  | TmTyApp(i, tm, ty_app) ->

    type_of tm                >>= fun (ty_t, sis) ->
    check_ty_app_shape i ty_t >>= fun (ty_i) ->

    return (ty_substTy ty_app 0 0 ty_i, sis)

  (* b must have type bool and the two branches must have matching types *)
  | TmIfThenElse(i, b, thent, elset)    ->

    type_of b >>= fun (tyb, sisb) ->
    type_of thent >>= fun (tythen, sisthen) ->
    type_of elset >>= fun (tyelse, siselse) ->
    
    check_type_sub i tythen tyelse >>
    check_type_sub i tyelse tythen >>
    (match tyb with
      | TyPrim (PrimBool) -> return ()
      | _                 -> fail i @@ TypeMismatch (tyb, TyPrim (PrimBool))) >>

    return (tythen, add_sens (lub_sens sisthen siselse) sisb)

  ) >>= fun (ty, sis) ->

  decr ty_seq;
  (* We limit pp_term *)
  ty_debug (tmInfo t) "<-- [%3d] Exit  type_of: @[%a@] with type @[%a@]" !ty_seq
    (Print.limit_boxes Print.pp_term) t Print.pp_type ty;

  return (ty, sis)

let get_type sensCheck program =
  ty_seq := 0;
  match type_of program (Ctx.empty_context, sensCheck) with
  | Ok (ty, _sis) -> ty
  | Error e -> typing_error_pp e.i pp_tyerr e.v
