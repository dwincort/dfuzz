(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)

(* Pretty printing module. Currently it uses the standard Format facility. *)

open Format

open Types

open Support.Options

(**********************************************************************)
(* Unicode handling *)

module Symbols = struct
  type pp_symbols =
      Inf
    | Forall
    | Exists
    | Arrow
    | DblArrow
    | Lollipop
    | Tensor
    | Union
    | Nat
    | Int
    | Num
    | Bool
    | Mu
    | Lambda
    | BigLambda
    | Fuzzy
    | SubTau
    | Vdash
    | Geq
    | Lub

  let pp_symbol_table s = match s with
      Inf      -> ("inf",     "∞")
    | Forall   -> ("forall ", "∀")
    | Exists   -> ("exits " , "∃")
    | Arrow    -> ("->",      "→")
    | DblArrow -> ("=>",      "⇒")
    | Lollipop -> ("-o",      "⊸")
    | Tensor   -> ("x",       "⊗")
    | Union    -> ("+",       "⊕")
    | Nat      -> ("nat",     "ℕ")
    | Int      -> ("int",     "ℤ")
    | Num      -> ("num",     "ℝ")
    | Bool     -> ("bool",    "𝔹")
    | Mu       -> ("mu",      "μ")
    | Lambda   -> ("\\",      "λ")
    | BigLambda   -> ("\\!",  "Λ")
    | Fuzzy    -> ("circle",  "◯")
    | SubTau   -> ("_t",      "ₜ")
    | Vdash    -> ("|-",      "⊢")
    | Geq      -> (">=",      "≥")
    | Lub      -> ("U",       "⊔")

  let string_of_symbol s =
    let select = if !debug_options.unicode then snd else fst in
    select (pp_symbol_table s)
end

let u_sym x = Symbols.string_of_symbol x

(**********************************************************************)
(* Helper functions for pretty printing *)

let pp_list pp fmt l = 
  let rec inner fmt l = match l with
      []         -> fprintf fmt "]"
    | csx :: []  -> fprintf fmt "%a]" pp csx
    | csx :: csl -> fprintf fmt "%a,@ %a" pp csx inner csl
  in fprintf fmt "[%a" inner l

let pp_pair ppl ppr fmt pair = 
  let (l,r) = pair in fprintf fmt "(%a,@ %a)" ppl l ppr r

(* Not worth it, we usually need very custom printers in option cases *)

(* let pp_option pp fmt o = match o with *)
(*   | None   -> fprintf fmt "" *)
(*   | Some v -> fprintf fmt "%a" pp v *)

(* Study this concept *)

(* Limit a formatter: (limit_boxes 3 pp_type) *)
let limit_boxes ?(n=(!debug_options).pr_level) pp = fun fmt ->
  let mb      = Format.pp_get_max_boxes fmt () in
  let con fmt = Format.pp_set_max_boxes fmt mb in
  (* print_string "eo"; print_string (string_of_int n); print_newline (); *)
  Format.pp_set_max_boxes fmt n;
  kfprintf con fmt "%a" pp

(**********************************************************************)
(* Pretty printing for variables *)

let pp_name fmt (bt, n) =
  let pf = fprintf fmt in
  match bt with
    BiVar    -> pf  "%s" n
  | BiTyVar  -> pf "'%s" n

let pp_vinfo fmt v =
  let vi = (v.v_type, v.v_name) in
  match !debug_options.var_output with
      PrVarName  -> fprintf fmt "%a" pp_name vi
    | PrVarIndex -> fprintf fmt "[%d/%d]" v.v_index v.v_size
    | PrVarBoth  -> fprintf fmt "%a:[%d/%d]" pp_name vi v.v_index v.v_size

let pp_binfo fmt b = pp_name fmt (b.b_type, b.b_name)

(**********************************************************************)
(* Pretty printing for sensitivities *)

let rec pp_si fmt s =
  match s with
  | SiInfty                -> fprintf fmt "%s" (u_sym Symbols.Inf)
  | SiConst flt            -> fprintf fmt "%.3f" flt
  | SiTerm(t)              -> fprintf fmt "SiTerm(%a)" pp_term t
  | SiAdd (si1, si2)       -> fprintf fmt "(%a + %a)" pp_si si1 pp_si si2
  | SiMult(si1, si2)       -> fprintf fmt "(%a * %a)" pp_si si1 pp_si si2
  | SiLub (si1, si2)       -> fprintf fmt "(%a @<1>%s %a)" pp_si si1 (u_sym Symbols.Lub) pp_si si2

and pp_si_op fmt o =
  match o with
  | None    -> fprintf fmt "?"
  | Some si -> pp_si fmt si

(**********************************************************************)
(* Pretty printing for types *)

(* Primitive types *)
and pp_primtype fmt ty = match ty with
  | PrimNum     -> fprintf fmt "@<1>%s" (u_sym Symbols.Num)
  | PrimInt     -> fprintf fmt "@<1>%s" (u_sym Symbols.Int)
  | PrimUnit    -> fprintf fmt "()"
  | PrimBool    -> fprintf fmt "@<1>%s" (u_sym Symbols.Bool)
  | PrimString  -> fprintf fmt "string"
  | PrimClipped -> fprintf fmt "clipped"

and pp_primtype1 fmt ty = match ty with
  | Prim1Bag   -> fprintf fmt "bag"
  | Prim1Fuzzy -> fprintf fmt "@<1>%s" (u_sym Symbols.Fuzzy)

(* Helper for our sensitivity annotated arrows *)
and pp_arrow fmt s = match s with
  | SiConst 1.0      -> fprintf fmt "@<1>%s" (u_sym Symbols.Lollipop)
  | SiInfty          -> fprintf fmt "@<1>%s" (u_sym Symbols.Arrow)
  | si               -> fprintf fmt "@<1>%s[%a]" (u_sym Symbols.Lollipop) pp_si si

(* Main printer *)
and pp_type ppf ty = match ty with
  | TyVar v                  -> pp_vinfo ppf v
  | TyPrim tp                -> fprintf ppf "%a" pp_primtype tp
  (* Weird syntax choices *)
  | TyPrim1 (tp, ty)         -> fprintf ppf "%a(%a)" pp_primtype1 tp pp_type ty
  (* ADT *)
  | TyUnion(ty1, ty2)       -> fprintf ppf "(%a @<1>%s @[<h>%a@])" pp_type ty1 (u_sym Symbols.Union)  pp_type ty2
  | TyTensor(ty1, ty2)      -> fprintf ppf "(%a @<1>%s @[<h>%a@])" pp_type ty1 (u_sym Symbols.Tensor) pp_type ty2
  | TyAmpersand(ty1, ty2)   -> fprintf ppf "(%a & @[<h>%a@])" pp_type ty1 pp_type ty2
  (* Funs *)
  | TyLollipop(ty1, s, ty2) -> fprintf ppf "(@[<hov>%a %a@ %a@])" pp_type ty1 pp_arrow s pp_type ty2
  | TyMu(n, ty)             -> fprintf ppf "@<1>%s %a. @[<hov>(%a)@]" (u_sym Symbols.Mu) pp_binfo n pp_type ty
  (* Abs *)
  | TyForall(n, ty)         -> fprintf ppf "@<1>%s %a.@;(@[%a@])" (u_sym Symbols.Forall) pp_binfo n pp_type ty

and pp_maybe_type ppf oty =
  if !debug_options.pr_ann then
    match oty with
      None    -> fprintf ppf ""
    | Some ty -> fprintf ppf ": %a" pp_type ty
  else
    fprintf ppf ""

(**********************************************************************)
(* Pretty printing for contexts *)

and pp_tyvar_ctx = pp_list pp_vinfo

and pp_var_ctx_elem ppf (v, ty) =
  if !debug_options.full_context then
    fprintf ppf "%-10a : @[%a@]" pp_vinfo v pp_type ty
  else
    fprintf ppf "%a" pp_vinfo v


and pp_context ppf ctx =
  fprintf ppf "Type Context: [@[<v>%a@]]@\nTerm Context: [@[<v>%a@]@]"
    pp_tyvar_ctx              (List.rev ctx.tyvar_ctx)
    (pp_list pp_var_ctx_elem) (List.rev ctx.var_ctx)


(**********************************************************************)
(* Pretty printing for terms *)

(* This will be useful in the future *)

(* Operators *)
and binary_op_table =
  [("op_lor", "||");
   ("op_land", "&&");
   ("op_eq",   "==");
   ("op_neq",  "!=");
   ("op_lt",   "<");
   ("op_gt",   ">");
   ("op_lte",  "<=");
   ("op_gte",  ">=");
   ("op_add",  "+");
   ("op_sub",  "-");
   ("op_mul",  "*");
   ("op_div",  "/")]

and is_binary_op s = List.mem_assoc s binary_op_table

and string_of_op s = List.assoc s binary_op_table

and string_of_term_prim t = match t with
    PrimTUnit         -> "()"
  | PrimTNum f        -> "(num "^string_of_float f^")"
  | PrimTClipped f    -> "(clip "^string_of_float f^")"
  | PrimTInt i        -> "(int "^string_of_int i^")"
  | PrimTBool b       -> string_of_bool b
  | PrimTString s     -> ("\"" ^ s ^ "\"")

and pp_colon ppf s = match s with
    SiConst 1.0      -> fprintf ppf " :[]"
  | SiInfty          -> fprintf ppf " :"
  | si               -> fprintf ppf " :[%a]" pp_si si

and pp_maybe_si_type ppf osity =
  if !debug_options.pr_ann then
    match osity with
    | None         -> fprintf ppf ""
    | Some(si, ty) -> fprintf ppf "%a %a" pp_colon si pp_type ty
  else
    fprintf ppf ""

and pp_si_type ppf (si, ty) =
  if !debug_options.pr_ann then
    fprintf ppf "%a %a" pp_colon si pp_type ty
  else
    fprintf ppf ""

and pp_ttslst ttslst = 
  let pp ppf (tm,ty,si,_) = fprintf ppf "(%a :[%a] %a)" pp_term tm pp_si si pp_type ty in
  pp_list pp ttslst

(* let open_box n =  *)
(*   print_string  *)
(* Term pretty printing *)
and pp_term ppf t =
  match t with
    TmVar(_, v)             -> fprintf ppf "%a" pp_vinfo v
  (* Primitive terms *)
  | TmPrim(_, pt)           -> fprintf ppf "%s" (string_of_term_prim pt)
  | TmPrimFun(_, n, _, ttslst)  -> fprintf ppf "primfun %s with args:@ @[%a@]" n pp_ttslst ttslst
  
  (* Bags *)
  | TmBag(_, ty, tmlst)         -> fprintf ppf "Bag[%a]@ {%a}" pp_type ty (pp_list pp_term) tmlst

  (* Tensor and & *)
  | TmPair(_, tm1, tm2)               -> fprintf ppf "(@[%a@],@ @[%a@])" pp_term tm1 pp_term tm2
  (* | TmTensDest(_, x, y, si, tm, term) -> fprintf ppf "@[<v>let (%a,%a) :[%a] = @[%a@];@,@[%a@]@]" pp_binfo x pp_binfo y pp_si si pp_term tm pp_term term *)
  | TmTensDest(_, x, y, tm, term) -> fprintf ppf "@[<v>let (%a,%a) : = @[%a@];@,@[%a@]@]" pp_binfo x pp_binfo y pp_term tm pp_term term
  | TmAmpersand(_, tm1, tm2)          -> fprintf ppf "(|@[%a@], @[%a@]|)" pp_term tm1 pp_term tm2

  | TmLeft (_, tm, ty)   -> fprintf ppf "Left@ @[<v>%a@]"  pp_term tm
  | TmRight(_, tm, ty)   -> fprintf ppf "Right@ @[<v>%a@]" pp_term tm
  
  (* Data type manipulation *)
  | TmTypedef(_, n, ty, tm)    -> fprintf ppf "@[<v>typedef %a = %a;@,@[%a@]@]" pp_binfo n pp_type ty pp_term tm
  | TmFold(_, ty, tm)          -> fprintf ppf "fold@ [@[<v>%a@]]@, @[%a@]" pp_type ty pp_term tm
  | TmUnfold(_, tm)            -> fprintf ppf "unfold @[<v>%a@]" pp_term tm

  (* Regular Abstraction and Application *)
  | TmAbs(_, a_n, sity, r_ty, tm) ->
    fprintf ppf "@<1>%s (%a%a)%a {@\n@[<hov 1> %a@]@\n}"
      (u_sym Symbols.Lambda) pp_binfo a_n pp_si_type sity pp_maybe_type r_ty pp_term tm

  | TmApp(_, tm1, tm2)         -> print_special_app ppf tm1 tm2

  | TmLet(_, n, si, tm1, tm2) ->
    fprintf ppf "@[<v>@[<hov>%a @[:[%a]@] =@;<1 1>@[%a@]@];@,@[%a@]@]" pp_binfo n pp_si si pp_term tm1 pp_term tm2

  | TmStmt(_, tm1, tm2) ->
    fprintf ppf "@[%a@];@,@[%a@]" pp_term tm1 pp_term tm2

  | TmRecFun(_, n, r_ty, tm, _) ->
    fprintf ppf "@[<v>@[<hov>rec %a : @[%a@] =@;<1 1>@[%a@]@]" pp_binfo n pp_type r_ty pp_term tm
  
  | TmSample(_, n, tm1, tm2) ->
    fprintf ppf "@[<v>@[<hov>sample %a@ =@;<1 1>@[%a@]@];@,@[%a@]@]" pp_binfo n pp_term tm1 pp_term tm2

  (* Case expressions *)
  | TmUnionCase(_, tm, ln, ltm, rn, rtm) ->
    (* Alternative using vertical boxes *)
    fprintf ppf "case @[%a@] of {@\n   inl(%a) @<1>%s @[%a@]@\n | inr(%a) @<1>%s @[%a@]@\n}"
      pp_term tm
      pp_binfo ln (u_sym Symbols.DblArrow) pp_term ltm
      pp_binfo rn (u_sym Symbols.DblArrow) pp_term rtm

  (* Type Abstraction and Application *)
  | TmTyAbs(_, bi, tm)     -> fprintf ppf "@<1>%s %a.@\n@[<hov 1> %a@]" (u_sym Symbols.BigLambda) pp_binfo bi pp_term tm
  | TmTyApp(_, tm, ty)     -> fprintf ppf "(%a@@[@[%a@]])" pp_term tm pp_type ty

  (* Convenience *)
  | TmIfThenElse(_, b, thent, elset) -> fprintf ppf "if @[%a@]@ then@ @[%a@]@ else@ @[%a@]" pp_term b pp_term thent pp_term elset

(* We print some applications in an special way, note that this relies on debug information *)
and print_special_app ppf tm1 tm2 =
  let regular_print tm1 tm2 = fprintf ppf "(%a@;<1 1>@[<hov>%a@])" pp_term tm1 pp_term tm2 in
  match tm1 with
    (* Binary operations *)
    TmApp(_, TmVar(_, v), op1) ->
      if is_binary_op v.v_name then
        fprintf ppf "(@[%a@] %s@ @[%a@])" pp_term op1 (string_of_op v.v_name) pp_term tm2
      else if v.v_name = "tensor_pair" then
        fprintf ppf "(%a, %a)" pp_term op1 pp_term tm2
      else
        regular_print tm1 tm2
  | TmApp(_, TmApp(_, TmVar(_, v), cond), op1) ->
    if v.v_name = "if_then_else" then
      fprintf ppf "@[<v>if @[<hov>%a@] then@ @[<h>%a@]@,else@ @[%a@]@]" pp_term cond pp_term op1 pp_term tm2
    else
      regular_print tm1 tm2
  | _ -> regular_print tm1 tm2

let pp_to_string s = 
  fprintf str_formatter "%s" s;
  kfprintf (fun _ -> Format.flush_str_formatter ()) str_formatter

