(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Ctx
open Syntax
open Constr

open Support.Error
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
| WrongKind    of kind * kind
| NotSubtype   of ty * ty
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
  | WrongKind(k1, k2)     -> Fmt.fprintf ppf "EEE [%3d] Kind mismatch expected %a found %a." !ty_seq P.pp_kind k1 P.pp_kind k2
  | NotSubtype(ty1,ty2)   -> Fmt.fprintf ppf "EEE [%3d] %a is not a subtype of %a" !ty_seq P.pp_type ty1 P.pp_type ty2
  | Internal s            -> Fmt.fprintf ppf "EEE [%3d] Internal error: %s" !ty_seq s

let typing_error fi = error_msg    Opt.TypeChecker fi
let typing_error_pp = error_msg_pp Opt.TypeChecker

let ty_warning fi = message 1 Opt.TypeChecker fi
let ty_info    fi = message 2 Opt.TypeChecker fi
let ty_info2   fi = message 3 Opt.TypeChecker fi
let ty_debug   fi = message 4 Opt.TypeChecker fi
let ty_debug2  fi = message 5 Opt.TypeChecker fi
let ty_debug3  fi = message 6 Opt.TypeChecker fi

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

(* Reader/Error monad for type-checking *)
module TypeCheckMonad = struct
  type 'a ty_error =
    Right of 'a
  | Left  of ty_error_elem withinfo

  type 'a checker = context -> 'a ty_error
  
  let (>>=) (m : 'a checker) (f : 'a -> 'b checker) : 'b checker =
    fun ctx ->
      match m ctx with
      | Right res -> f res ctx
      | Left e    -> Left e
  
  let (>>) m f = m >>= fun _ -> f
  
  let return (x : 'a) : 'a checker = fun ctx -> Right x
  
  let fail (i : info) (e : ty_error_elem) : 'a checker = fun _ ->
    Left { i = i; v = e }
  
  let get_ctx : context checker =
    fun ctx -> Right ctx
  
  let get_ctx_length : int checker =
    get_ctx                             >>= fun ctx ->
    return @@ List.length ctx.var_ctx
  
  let get_ty_ctx_length : int checker =
    get_ctx                             >>= fun ctx ->
    return @@ List.length ctx.tyvar_ctx
  
  let with_new_ctx (f : context -> context) (m : 'a checker) : 'a checker =
    fun ctx -> m (f ctx)
  
  (* Extend the context with a type binding and run a computation *)
  let with_extended_ty_ctx (v : string) (k : kind) (m : 'a checker) : 'a checker =
    with_new_ctx (extend_ty_var v k) m
  
  (* Extend the context with a value binding and run a computation. The
     computation is assumed to produce a list of results, one for each
     variable in the extended context. That list is destructed, and the
     result corresponding to the new variable is returned separately for
     convenience. *)
  let with_extended_ctx (i : info) (v : string) (ty : ty) (m : ('a * 'b list) checker) :
      ('a * 'b * 'b list) checker =
    with_new_ctx (extend_var v ty) m >>= fun (res, res_ext_ctx) ->
    match res_ext_ctx with
    | res_v :: res_ctx -> return (res, res_v, res_ctx)
    | [] -> fail i @@ Internal "Computation on extended context didn't produce enough results"
  
  (* Similar to the one above, but with two variables. vx has index 1 in
     the extended context, while vy has index 0. The order of the
     returned results matches those of the arguments. *)
  let with_extended_ctx_2 (i : info)
      (vx : string) (tyx : ty) (vy : string) (tyy : ty)
      (m : ('a * 'b list) checker) : ('a * 'b * 'b * 'b list) checker =
    with_new_ctx (fun ctx -> extend_var vy tyy (extend_var vx tyx ctx)) m >>= fun (res, res_ext_ctx) ->
    match res_ext_ctx with
    | res_y :: res_x :: res_ctx -> return (res, res_x, res_y, res_ctx)
    | _ -> fail i @@ Internal "Computation on extended context didn't produce enough results"
  
  (* Check that the first sensitivity is less than the second *)
  let check_sens_leq i (sil : si) (sir : si) : unit checker =
    if check_si_leq sil sir then
      return ()
    else
      fail i @@ SensError(sil, sir)
  
  (* Get the type of the given variable *)
  let get_var_ty (v : var_info) : ty checker =
    get_ctx >>= fun ctx ->
    return @@ snd (access_var ctx v.v_index)
end

module TypeSens = struct
  (* Constants *)
  let si_zero  = SiConst 0.0
  let si_one   = SiConst 1.0
  let si_infty = SiInfty
  
  (* Type of sensitivities augmented with □, with corresponding
     functions. In the type-checking algorithm, □ represents a binding
     that doesn't have an assigned sensitivity, which must be
     later on. *)
  type bsi = si option
  
  (* A list only with zero sensitivities *)
  let zeros (n : int) : bsi list =
    let rec aux n l =
      if n = 0 then l else aux (n - 1) (None :: l) in
    aux n []
  
  (* A list with zero sensitivities, except for one variable *)
  (* Note that this has to be kept in sync with the actual ctx *)
  let singleton (n : int) (v : var_info) : bsi list =
    let rec aux n l =
      if n = 0 then l
      else let si = if n = v.v_index + 1 then Some si_one else None in
           aux (n - 1) (si :: l) in
    aux n []
  
  (* Extension of operations on regular sensitivities to augmented
     sensitivities *)
  let add_bsi (bsi1 : bsi) (bsi2 : bsi) : bsi =
    match bsi1, bsi2 with
    | Some si1, Some si2 -> Some (SiAdd (si1, si2))
    | Some si, None
    | None, Some si -> Some si
    | None, None -> None
  
  let mult_bsi (bsi1 : bsi) (bsi2 : bsi) : bsi =
    match bsi1, bsi2 with
    | Some si1, Some si2 -> Some (SiMult (si1, si2))
    | _, _ -> None
  
  let si_of_bsi (bsi : bsi) : si =
    Option.default si_zero bsi
  
  let lub_bsi (bsi1 : bsi) (bsi2 : bsi) : bsi =
    match bsi1, bsi2 with
    | Some si1, Some si2 -> Some (SiLub (si1, si2))
    | Some si, None
    | None, Some si -> Some si
    | None, None -> None
  
  let sup_bsi (bi : binder_info) (k : kind) (bsi : bsi) : bsi =
    Option.map (fun si -> SiSup (bi, k, si)) bsi
  
  let add_sens (bsis1 : bsi list) (bsis2 : bsi list) : bsi list =
    List.map2 add_bsi bsis1 bsis2
  
  let scale_sens (bsi : bsi) (bsis : bsi list) : bsi list =
    List.map (mult_bsi bsi) bsis
  
  let lub_sens (bsis1 : bsi list) (bsis2 : bsi list) : bsi list =
    List.map2 lub_bsi bsis1 bsis2
  
  let sup_sens (bi : binder_info) (k : kind) (bsis : bsi list) : bsi list =
    List.map (sup_bsi bi k) bsis
end

module TypeSub = struct
  open TypeCheckMonad
  
  let check_prim_sub (i : info) (ty_f : ty_prim) (ty_a : ty_prim) : unit checker =
    match ty_f, ty_a with
    | PrimNum, PrimClipped -> return ()
    | _   when ty_f = ty_a -> return ()
    | _                    -> fail i @@ NotSubtype (TyPrim ty_f, TyPrim ty_a)

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
      check_sens_leq i sir sil

    | TyMu(_bl, tyl), TyMu(_br, tyr) ->
      check_type_sub i tyl tyr

    | TyForall(bl, kl, tyl), TyForall(_br, kr, tyr) ->
      if kl = kr then
        with_new_ctx (extend_ty_var bl.b_name kl) begin
          check_type_sub i tyl tyr
        end
      else fail

    | _, _ -> fail

  (* Check whether ty is compatible (modulo subtyping) with annotation
     ann, returning the resulting type. *)
  let check_type_ann (i : info) (ann : ty option) (ty : ty) : ty checker =
    match ann with
    | Some ty' -> check_type_sub i ty ty' >> return ty'
    | None -> return ty

  (* Check that the type is an application and can be applied to
     arg. Return the result and sensitivity of the application *)
  let check_ty_app_shape i ty_arr =
    match ty_arr with
    | TyForall(_b, k, ty) -> return (ty, k)
    | _                   -> fail i @@ CannotApply(ty_arr, ty_arr)

  (* This is good for return, eq, etc... it should be extended
     systematically instead of the current hack *)
  let infer_tyapp_very_simple i ty ty_arg =
    match ty with
    | TyLollipop(TyVar v, si, tyb) ->
      if v.v_index = 0 then
        let nt = ty_subst 0 ty_arg tyb in
        ty_debug i "==> [%3d] Inferring type application from @[%a@] to @[%a@]" !ty_seq Print.pp_type tyb Print.pp_type nt;
        return (nt, si)
      else
        fail i @@ CannotApply(ty, ty_arg)
    | TyLollipop(TyPrim1 (t, TyVar v), si, tyb) ->
      begin match ty_arg with
      | TyPrim1 (t1, ty_arg') ->
        if v.v_index = 0 && t1 = t then
          let nt = ty_subst 0 ty_arg' tyb in
          ty_debug i "==> [%3d] Inferring container type application from @[%a@] to @[%a@]" !ty_seq Print.pp_type tyb Print.pp_type nt;
          return (nt, si)
        else
          fail i @@ CannotApply(ty, ty_arg)
      | _ -> fail i @@ CannotApply(ty, ty_arg)
      end
    | _ -> fail i @@ CannotApply(ty, ty_arg)

  let check_app i ty_arr ty_arg =
    ty_debug i "<-> [%3d] Application of @[%a@] to @[%a@]" !ty_seq Print.pp_type ty_arr Print.pp_type ty_arg;
    match ty_arr with
    (* Here we do inference of type applications *)
    | TyForall(bi, Star, ty)   ->
      infer_tyapp_very_simple i ty ty_arg

    | TyLollipop(tya, si, tyb) ->
      check_type_sub i tya ty_arg >>
      return (tyb, si)
    | _                        -> fail i @@ CannotApply(ty_arr, ty_arg)

  let check_fuzz_shape i ty =
    match ty with
    | TyPrim1 (Prim1Fuzzy, ty) -> return ty
    | _                        -> fail i @@ WrongShape (ty, "fuzzy")

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

(* Given a term t and a context ctx for that term, check whether t is
   typeable under ctx, returning a type for t, a list of synthesized
   sensitivities for ctx, and a list of constraints that need to be
   satisfied in order for the type to be valid. Raises an error if it
   detects that no typing is possible. *)

let rec type_of (t : term) : (ty * bsi list) checker  =

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

  (************************************************************)
  (* Abstraction and Application *)
  (* λ (x :[si] tya_x) : tya_tm { tm } *)
  | TmAbs(i, b_x, (sia_x, tya_x), otya_tm, tm) ->

    with_extended_ctx i b_x.b_name tya_x (type_of tm) >>= fun (ty_tm, si_x, sis) ->

    ty_debug (tmInfo t) "### Inferred sensitivity for binder @[%a@] is @[%a@]" P.pp_binfo b_x P.pp_si (si_of_bsi si_x);

    check_type_ann i otya_tm ty_tm                    >>
      check_sens_leq i (si_of_bsi si_x) sia_x         >>
      return (TyLollipop (tya_x, sia_x, ty_tm), sis)

  (* tm1 !ᵢβ → α, tm2: β *)
  | TmApp(i, tm1, tm2)                             ->

    type_of tm1 >>= fun (ty1, sis1) ->
    type_of tm2 >>= fun (ty2, sis2) ->

    (* Checks that ty1 has shape !ᵢβ → α, and that ty2 is and instance of β.
       Returns α and the sensitivity inside ty1 *)
    check_app i ty1 ty2 >>= fun (tya, r) ->

    (* We scale by the sensitivity in the type, which comes from an annotation *)
    return (tya, add_sens sis1 (scale_sens (Some r) sis2))

  (************************************************************)
  (* Identical to app + lam, this rule exists in order to avoid too
     many type annotations! *)
  (* let x [: sia_x] = tm_x in e *)
  | TmLet(i, x, sia_x, tm_x, e)                   ->

    type_of tm_x >>= fun (ty_x, sis_x)  ->

    ty_debug i "### Type of binder %a is %a" Print.pp_binfo x Print.pp_type ty_x;

    with_extended_ctx i x.b_name ty_x (type_of e) >>= fun (ty_e, si_x, sis_e) ->
    ty_debug i "### Inferred sensitivity for binder @[%a@] is @[%a@]" P.pp_binfo x P.pp_si (si_of_bsi si_x);
    check_sens_leq i (si_of_bsi si_x) sia_x                 >>
    return (ty_e, add_sens sis_e (scale_sens si_x sis_x))

  (* function x <args ...> : tya_x { tm_x }; e *)
  | TmLetRec(i, x, tya_x, tm_x, e)                      ->

    with_extended_ctx i x.b_name tya_x (type_of tm_x) >>= fun (ty_x, si_x, sis_x) ->

    check_type_sub i ty_x tya_x >>

      with_extended_ctx i x.b_name tya_x (type_of e) >>= fun (ty_e, si_x', sis_e) ->

    ty_debug i "### Type of binder %a is %a" Print.pp_binfo x Print.pp_type ty_x;
    return (ty_e, add_sens sis_e (scale_sens (mult_bsi (Some si_infty) si_x') sis_x))

  (* sample b_x = tm_x; e *)
  | TmSample(i, b_x, tm_x, e)                              ->

    type_of tm_x            >>= fun (ty_x, sis_x) ->
    check_fuzz_shape i ty_x >>= fun ty_x ->

    with_extended_ctx i b_x.b_name ty_x (type_of e) >>= fun (ty_e, si_x, sis_e) ->

    ty_debug (tmInfo t) "### [%3d] Sample for binder @[%a@] with sens @[%a@]" !ty_seq P.pp_binfo b_x P.pp_si (si_of_bsi si_x);

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
    let tm'         = term_ty_subst 0 tdef_ty tm   in
    type_of tm'

  (* let (x,y) = e in e' *)
  | TmTensDest(i, x, y, e, t) ->

    type_of e >>= fun (ty_e, sis_e) ->
    check_tensor_shape i ty_e >>= fun (ty_x, ty_y) ->

    (* Extend context with x and y *)
    with_extended_ctx_2 i x.b_name ty_x y.b_name ty_y (type_of t) >>= fun (ty_t, si_x, si_y, sis_t) ->

    let si_x = si_of_bsi si_x in
    let si_y = si_of_bsi si_y in
    ty_debug (tmInfo t) "### Inferred sensitivity for binder @[%a@] is @[%a@]" P.pp_binfo x P.pp_si si_x;
    ty_debug (tmInfo t) "### Inferred sensitivity for binder @[%a@] is @[%a@]" P.pp_binfo y P.pp_si si_y;

    return (ty_t, add_sens sis_t (scale_sens (Some (SiLub (si_x, si_y))) sis_e))

  (* case e of inl(x) => e_l | inr(y) e_r *)
  | TmUnionCase(i, e, b_x, e_l, b_y, e_r)      ->

    type_of e >>= fun (ty_e, sis_e) ->

    check_union_shape i ty_e >>= fun (ty1, ty2) ->

    with_extended_ctx i b_x.b_name ty1 (type_of e_l) >>= fun (tyl, si_x, sis_l) ->
    with_extended_ctx i b_y.b_name ty2 (type_of e_r) >>= fun (tyr, si_y, sis_r) ->
    check_type_sub i tyr tyl >>
    check_type_sub i tyl tyr >>

    let si_x = si_of_bsi si_x in
    let si_y = si_of_bsi si_y in
    ty_debug (tmInfo t) "### Inferred sensitivity for binder @[%a@] is @[%a@]" P.pp_binfo b_x P.pp_si si_x;
    ty_debug (tmInfo t) "### Inferred sensitivity for binder @[%a@] is @[%a@]" P.pp_binfo b_y P.pp_si si_y;

    return (tyl, add_sens (lub_sens sis_l sis_r) (scale_sens (Some (SiLub (si_x, si_y))) sis_e))

  (* Type/Sensitivity Abstraction and Application *)
  | TmTyAbs(i, bi, ki, tm) ->

    with_extended_ty_ctx bi.b_name ki (type_of tm) >>= fun (ty, sis) ->
    return (TyForall(bi, ki, ty), sup_sens bi ki sis)

  | TmTyApp(i, tm, ty_app) ->

    type_of tm                >>= fun (ty_t, sis) ->
    check_ty_app_shape i ty_t >>= fun (ty_i, k) ->

    if k = Star then
      return (ty_subst 0 ty_app ty_i, sis)
    else
      fail i @@ WrongKind(Star, k)

  ) >>= fun (ty, sis) ->

  decr ty_seq;
  (* We limit pp_term *)
  ty_debug (tmInfo t) "<-- [%3d] Exit type_of : @[%a@] with type @[%a@]" !ty_seq
    (Print.limit_boxes Print.pp_term) t Print.pp_type ty;

  return (ty, sis)

(* Equivalent to run *)
let get_type program =
  match type_of program Ctx.empty_context with
  | Right (ty, _sis) -> ty
  | Left e ->
    typing_error_pp e.i pp_tyerr e.v
