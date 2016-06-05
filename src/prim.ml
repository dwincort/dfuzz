(* file name: prim.ml
   created by: Daniel Winograd-Cort
   Last modified: 12/20/2015
   
   Description:
   This file contains code for interpreting SFuzz primitives.
*)

open Types
open Interpreter.InterpMonad
open Support.FileInfo
open Print

(* We create a few helper functions for simplifying the creation of 
   primitive functions.  The main components are the functions fun_of_1arg 
   and fun_of_2args, which make creating 1- or 2-argument primitives easy.  
   These functions require function arguments for extracting values from 
   terms as well as constructing terms from values.  Thus, we also provide 
   a few common extractors and makers in the forms of ex**** and mk**** 
   respectively.  That is, for example, exBool is a function for extracting 
   a boolean value from a term and mkInt is for turning an integer value 
   into a term.  For polymorphic functions that can work on terms directly 
   (e.g. equality, etc.), we provide exAny and mkAny, which are basically 
   identity functions.
   
   There are also some special purpose functions for dealing with the more 
   interesting primitives (the real fuzzy stuff).
   
   Finally, the main (only) export of this module is the list of primitives 
   itself.
*)

let rzFileName = ref "redZoneTemp"

let di = dummyinfo

module Creation = struct
  (* The expectation functions take a term and return an ocaml value *)
  let exBool name tb = match tb with 
    | TmPrim (_i, PrimTBool b) -> return b
    | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a bool but found %a" name pp_term tb
  let exNum name tn = match tn with 
    | TmPrim (_i, PrimTNum n) -> return n
    | TmPrim (_i, PrimTInt n) -> return (float_of_int n)
    | TmPrim (_i, PrimTClipped n) -> return n
    | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a num but found %a" name pp_term tn
  let exInt name tn = match tn with 
    | TmPrim (_i, PrimTInt n) -> return n
    | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected an int but found %a" name pp_term tn
  let exString name ts = match ts with 
    | TmPrim (_i, PrimTString s) -> return s
    | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a string but found %a" name pp_term ts
  let exBag name tb = match tb with 
    | TmBag(_i, _ty, tlst) -> return tlst
    | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a bag but found %a" name pp_term tb
  let exVector name tb = match tb with 
    | TmVector(_i, _ty, tlst) -> return tlst
    | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a vector but found %a" name pp_term tb
  let exPair ex1 ex2 name tp = match tp with 
    | TmPair(_i, t1, t2) -> ex1 name t1 >>= fun v1 ->
                            ex2 name t2 >>= fun v2 ->
                            return (v1, v2)
    | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a pair but found %a" name pp_term tp
  let rec exList exA name tl = match tl with
    | TmFold(_i, _, TmLeft(_,tm,_)) -> return []
    | TmFold(_i, _, TmRight(_,TmPair(_, tx, txs),_)) ->
        exA name tx >>= fun vx ->
        exList exA name txs >>= fun vxs ->
        return (vx :: vxs)
    | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a list but found %a" name pp_term tl
  let exFun _name t = return t (* Theoretically, we could check that it's actually a function, but we don't need to *)
  let exAny _name t = return t
  
  (* The make functions turn an ocaml value into a term *)
  let mkBool i b   = TmPrim (i, PrimTBool b)
  let mkNum i n    = TmPrim (i, PrimTNum n)
  let mkClipped i c = TmPrim (i, PrimTClipped (if c > 1.0 then 1.0 else if c < 0.0 then 0.0 else c))
  let mkInt i n    = TmPrim (i, PrimTInt n)
  let mkString i s = TmPrim (i, PrimTString s)
  let mkBag i (ty, l) = TmBag (i, ty, l)
  let mkVector i (ty, l) = TmVector (i, ty, l)
  let mkPair mk1 mk2 i (t1, t2) = TmPair (i, mk1 i t1, mk2 i t2)
  let mkAny _i t   = t
  let mkUnit i _   = TmPrim (i, PrimTUnit)
  let nb_tyvar n = {b_name = n; b_type = BiTyVar; b_size = -1; b_prim = false;}

  let rec mkList mkA i (ty, lst) = 
    let lsttype = TyMu({b_name = "XX"; b_type = BiTyVar; b_size = -1; b_prim = false;}, TyUnion
            (TyPrim PrimUnit, TyTensor(ty, TyVar
                ({v_index = 0; v_name = "XX"; v_size = -1; v_type = BiTyVar;})))) in
    match lst with
    | [] -> TmFold(i, lsttype, TmLeft(i, TmPrim(i, PrimTUnit), TyTensor(ty, lsttype)))
    | x::xs -> TmFold(i, lsttype, TmRight(i, TmPair(i, mkA i x, mkList mkA i (ty, xs)), TyPrim PrimUnit))
  
  (* The fun_of_*_arg* functions are short hands for making the primitives easily *)
  let fun_of_no_args_with_type_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (mk : info -> 'a -> term)                 (* A maker for the result *)
    (op : ty -> 'a interpreter)               (* The operation to perform *)
    : primfun = 
    PrimFun (fun (ty, tlst) -> match tlst with
      | [] -> op ty >>= fun res -> return (mk di res)
      | _  -> fail @@ pp_to_string "** Primitive ** " "%s expected no arguments but found %a" name (pp_list pp_term) tlst)
  
  let fun_of_1arg_with_type_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (earg : string -> term -> 'a interpreter) (* An extractor for the argument *)
    (mk : info -> 'b -> term)                 (* A maker for the result *)
    (op : ty -> 'a -> 'b interpreter)         (* The operation to perform *)
    : primfun = 
    PrimFun (fun (ty, tlst) -> match tlst with
      | ta :: []
          -> earg name ta >>= fun a ->
             op ty a >>= fun res -> return (mk di res)
      | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected 1 argument but found %a" name (pp_list pp_term) tlst)
  
  let fun_of_1arg_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (earg : string -> term -> 'a interpreter) (* An extractor for the argument *)
    (mk : info -> 'b -> term)                 (* A maker for the result *)
    (op : 'a -> 'b interpreter)               (* The operation to perform *)
    : primfun = fun_of_1arg_with_type_i name earg mk (fun _ty x -> op x)
  
  let fun_of_1arg
    (name : string)                           (* The name of the function - for debug purposes *)
    (earg : string -> term -> 'a interpreter) (* An extractor for the argument *)
    (mk : info -> 'b -> term)               (* A maker for the result *)
    (op : 'a -> 'b)                           (* The operation to perform *)
    : primfun = fun_of_1arg_with_type_i name earg mk (fun _ty x -> return (op x))
  
  let fun_of_2args_with_type_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (mk : info -> 'c -> term)                 (* A maker for the result *)
    (op : ty -> 'a -> 'b -> 'c interpreter)   (* The operation to perform *)
    : primfun = 
    PrimFun (fun (ty, tlst) -> match tlst with
      | ta :: tb :: []
          -> efst name ta >>= fun a ->
             esnd name tb >>= fun b ->
             op ty a b >>= fun res -> return (mk di res)
      | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected 2 arguments but found %a" name (pp_list pp_term) tlst)
  
  let fun_of_2args_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (mk : info -> 'c -> term)                 (* A maker for the result *)
    (op : 'a -> 'b -> 'c interpreter)         (* The operation to perform *)
    : primfun = fun_of_2args_with_type_i name efst esnd mk (fun _ty x y -> op x y)
  
  let fun_of_2args 
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (mk : info -> 'c -> term)                 (* A maker for the result *)
    (op : 'a -> 'b -> 'c)                     (* The operation to perform *)
    : primfun = fun_of_2args_with_type_i name efst esnd mk (fun _ty x y -> return (op x y))
  
  let fun_of_3args_with_type_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (mk : info -> 'd -> term)                 (* A maker for the result *)
    (op : ty -> 'a -> 'b -> 'c -> 'd interpreter) (* The operation to perform *)
    : primfun = 
    PrimFun (fun (ty, tlst) -> match tlst with
      | ta :: tb :: tc :: []
          -> efst name ta >>= fun a ->
             esnd name tb >>= fun b ->
             ethd name tc >>= fun c ->
             op ty a b c >>= fun res -> return (mk di res)
      | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected 3 arguments but found %a" name (pp_list pp_term) tlst)
  
  let fun_of_3args_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (mk : info -> 'd -> term)                 (* A maker for the result *)
    (op : 'a -> 'b -> 'c -> 'd interpreter)   (* The operation to perform *)
    : primfun = fun_of_3args_with_type_i name efst esnd ethd mk (fun _ty x y z -> op x y z)
  
  let fun_of_3args
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (mk : info -> 'd -> term)                 (* A maker for the result *)
    (op : 'a -> 'b -> 'c -> 'd)               (* The operation to perform *)
    : primfun = fun_of_3args_with_type_i name efst esnd ethd mk (fun _ty x y z -> return (op x y z))
  
  
  let fun_of_4args_with_type_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (efth : string -> term -> 'd interpreter) (* An extractor for the fourth argument *)
    (mk : info -> 'e -> term)                 (* A maker for the result *)
    (op : ty -> 'a -> 'b -> 'c -> 'd -> 'e interpreter)   (* The operation to perform *)
    : primfun = 
    PrimFun (fun (ty, tlst) -> match tlst with
      | ta :: tb :: tc :: td :: []
          -> efst name ta >>= fun a ->
             esnd name tb >>= fun b ->
             ethd name tc >>= fun c ->
             efth name td >>= fun d ->
             op ty a b c d >>= fun res -> return (mk di res)
      | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected 4 arguments but found %a" name (pp_list pp_term) tlst)
  
  let fun_of_4args_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (efth : string -> term -> 'd interpreter) (* An extractor for the fourth argument *)
    (mk : info -> 'e -> term)                 (* A maker for the result *)
    (op : 'a -> 'b -> 'c -> 'd -> 'e interpreter) (* The operation to perform *)
    : primfun = fun_of_4args_with_type_i name efst esnd ethd efth mk (fun _ty a b c d -> op a b c d)

  let fun_of_5args_with_type_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (efth : string -> term -> 'd interpreter) (* An extractor for the fourth argument *)
    (efft : string -> term -> 'e interpreter) (* An extractor for the fifth argument *)
    (mk : info -> 'f -> term)                 (* A maker for the result *)
    (op : ty -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f interpreter)   (* The operation to perform *)
    : primfun = 
    PrimFun (fun (ty, tlst) -> match tlst with
      | ta :: tb :: tc :: td :: te :: []
          -> efst name ta >>= fun a ->
             esnd name tb >>= fun b ->
             ethd name tc >>= fun c ->
             efth name td >>= fun d ->
             efft name te >>= fun e ->
             op ty a b c d e >>= fun res -> return (mk di res)
      | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected 5 arguments but found %a" name (pp_list pp_term) tlst)
  
  let fun_of_5args_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (efth : string -> term -> 'd interpreter) (* An extractor for the second argument *)
    (efft : string -> term -> 'e interpreter) (* An extractor for the fifth argument *)
    (mk : info -> 'f -> term)                 (* A maker for the result *)
    (op : 'a -> 'b -> 'c -> 'd -> 'e -> 'f interpreter) (* The operation to perform *)
    : primfun = fun_of_5args_with_type_i name efst esnd ethd efth efft mk (fun _ty -> op)

  let fun_of_7args_with_type_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (efth : string -> term -> 'd interpreter) (* An extractor for the fourth argument *)
    (efft : string -> term -> 'e interpreter) (* An extractor for the fifth argument *)
    (esxh : string -> term -> 'f interpreter) (* An extractor for the sixth argument *)
    (esvh : string -> term -> 'g interpreter) (* An extractor for the seventh argument *)
    (mk : info -> 'h -> term)                 (* A maker for the result *)
    (op : ty -> 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h interpreter)   (* The operation to perform *)
    : primfun = 
    PrimFun (fun (ty, tlst) -> match tlst with
      | ta :: tb :: tc :: td :: te :: tf :: tg :: []
          -> efst name ta >>= fun a ->
             esnd name tb >>= fun b ->
             ethd name tc >>= fun c ->
             efth name td >>= fun d ->
             efft name te >>= fun e ->
             esxh name tf >>= fun f ->
             esvh name tg >>= fun g ->
             op ty a b c d e f g >>= fun res -> return (mk di res)
      | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected 7 arguments but found %a" name (pp_list pp_term) tlst)
  
  let fun_of_7args_i
    (name : string)                           (* The name of the function - for debug purposes *)
    (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
    (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
    (ethd : string -> term -> 'c interpreter) (* An extractor for the third argument *)
    (efth : string -> term -> 'd interpreter) (* An extractor for the second argument *)
    (efft : string -> term -> 'e interpreter) (* An extractor for the fifth argument *)
    (esxh : string -> term -> 'f interpreter) (* An extractor for the sixth argument *)
    (esvh : string -> term -> 'g interpreter) (* An extractor for the seventh argument *)
    (mk : info -> 'h -> term)                 (* A maker for the result *)
    (op : 'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h interpreter)   (* The operation to perform *)
    : primfun = fun_of_7args_with_type_i name efst esnd ethd efth efft esxh esvh mk (fun _ty -> op)

end

open Creation

let message n = Support.Error.message n Support.Options.Interpreter di
let assertionMsg i = Support.Error.message (-1) Support.Options.Assertion i
let printMsg i = Support.Error.message (-1) Support.Options.General i


(*****************************************************************************)
(* Here we have modifying functions *)

(* Makes sure that the given function only evaluates when we are in full 
   evaluation mode (as opposed to partial. *)
let onlyInFullEval (name : string) (f : 'a interpreter) : 'a interpreter = 
  isInPartial >>= fun b ->
  if b then fail (name^" not to be evaluated during partial evaluation") else f


(*****************************************************************************)
(* Here is the primitive for case on integers. *)

let rec intToPeanoFun
  (ty : ty)
  (n : int)
  : term interpreter = 
    if (n <= 0) then
      return @@ TmFold(di, ty, TmLeft(di, mkUnit di (), ty))
    else
      intToPeanoFun ty (n - 1) >>= fun n' ->
      return @@ TmFold(di, ty, TmRight(di, n', TyPrim PrimUnit))


(*****************************************************************************)
(* Here are some helpers for file and string parsing. *)
let fileLines (maxLines : int) (filename : string) = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    for i=1 to maxLines; do
      lines := input_line chan :: !lines
    done;
    close_in chan;
    List.rev !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines


let rec typeToMaker (i : info) (ty : ty) : (string -> term) interpreter = match ty with
  | TyPrim PrimNum  -> return (fun s -> mkNum i (float_of_string s))
  | TyPrim PrimInt  -> return (fun s -> mkInt i (int_of_string s))
  | TyPrim PrimUnit -> return (mkUnit i)
  | TyPrim PrimBool -> return (fun s -> mkBool i (bool_of_string s))
  | TyPrim PrimString   -> return (mkString i)
  | TyPrim PrimClipped  -> return (fun s -> mkClipped i (float_of_string s))
  | TyPrim1 (Prim1Bag, t) -> typeToMaker i t >>= fun mker ->
        return (fun s -> mkBag i (ty, List.map mker (Str.split (Str.regexp "[ \t]+") s)))
  | TyPrim1 (Prim1Vector, t) -> typeToMaker i t >>= fun mker ->
        return (fun s -> mkVector i (ty, List.map mker (Str.split (Str.regexp "[ \t]+") s)))
(*  | TyTensor (t1, t2) ->
        typeToMaker i t1 >>= fun mk1 ->
        typeToMaker i t2 >>= fun mk2 ->
        return (fun s -> mkPair mk1 mk2 i (Str.split (Str.regexp "[ \t]+") s))*)
  | _ -> fail @@ pp_to_string "" "**Primitive** unsupported read type: %a." pp_type ty

(*****************************************************************************)
(* Here we have specific helper functions for specific primitives. *)

let assertFun
  (s : string)
  (b : bool)
  : unit = 
    ignore (assertionMsg di "%s: %s" s (if b then "PASS" else "FAIL"))

let assertEqFun
  (s : string)
  (t1 : term)
  (t2 : term)
  : unit = 
    let res = if Syntax.tmEq t1 t2 
              then "PASS"
              else pp_to_string "FAIL " "(%a != %a)" pp_term t1 pp_term t2
    in ignore (assertionMsg di "%s: %s" s res)

let tyCheckFuzzFun
  (sens : float)
  (f : term)
  : term interpreter =
    onlyInFullEval "tyCheckFuzz" (return ()) >>
    let genFailResult s = return (TmLeft(di, TmPrim(di, PrimTString s), TyPrim PrimUnit)) in
    message 3 "--- tyCheckFuzz: Before Partial evaluation: %a" pp_term f;
    inPartial (Interpreter.goUnderLambda f) >>= fun pf ->
    message 3 "--- tyCheckFuzz: Partial evaluation results in: %a" pp_term pf;
    Tycheck.ty_seq := 0;
    match Tycheck.type_of pf (Ctx.empty_context, true) with 
        | Error e -> genFailResult @@ pp_to_string "TYPE FAIL: " "%a %a" pp_fileinfo e.i Tycheck.pp_tyerr e.v
        | Ok (tyf, _) -> begin
      message 3 "--- tyCheckFuzz: Type checking completed and found type: %a" pp_type tyf;
      (match tyf with
        | TyLollipop(_, si, _) -> begin match si with
              | SiConst n -> if n <= sens then return (Ok n) else return (Error 
                  ("tyCheckFuzz expected a "^string_of_float sens^"-sensitive function but found a "^string_of_float n^"-sensitive function"))
              | SiInfty -> return @@ Error 
                  ("tyCheckFuzz expected a "^string_of_float sens^"-sensitive function but found an infinitely sensitive function")
              | _ -> fail @@ pp_to_string "**Primitive** " "tyCheckFuzz found an unexpected sensitivity: %a" pp_si si
            end
        | _ -> fail @@ pp_to_string "**Primitive** " "tyCheckFuzz's function argument has non-lollipop type: %a" pp_type tyf
      ) >>= fun succ ->
      match succ with
        | Error s -> genFailResult s
        | Ok n -> return (TmRight(di, mkUnit di (), TyPrim PrimString))
    end

let runRedZone
  (ty : ty)
  (sens : float)
  (f : term)
  : term interpreter =
    onlyInFullEval "runRedZone" (return ()) >>
    (match ty with
      | TyUnion(_, aty) -> return aty
      | _ -> fail @@ pp_to_string "**Primitive** " "runRedZone found an unexpected return type: %a" pp_type ty
    ) >>= fun outty ->
    let genFailResult s = return (TmLeft(di, TmPrim(di, PrimTString s), outty)) in
    getDB >>= fun db ->
    message 3 "--- RunRedZone: Before Partial evaluation: %a" pp_term f;
    inPartial (Interpreter.goUnderLambda f) >>= fun pf ->
    message 3 "--- RunRedZone: Partial evaluation results in: %a" pp_term pf;
    Tycheck.ty_seq := 0;
    match Tycheck.type_of pf (Ctx.empty_context, true) with 
        | Error e -> genFailResult @@ pp_to_string "TYPE FAIL: " "%a %a" pp_fileinfo e.i Tycheck.pp_tyerr e.v
        | Ok (tyf, _) -> begin
      message 3 "--- RunRedZone: Type checking completed and found type: %a" pp_type tyf;
      (match tyf with
        | TyLollipop(_, si, _) -> begin match si with
              | SiConst n -> if n <= sens then return (Ok n) else return (Error 
                  ("runRedZone expected a "^string_of_float sens^"-sensitive function but found a "^string_of_float n^"-sensitive function"))
              | SiInfty -> return @@ Error 
                  ("runRedZone expected a "^string_of_float sens^"-sensitive function but found an infinitely sensitive function")
              | _ -> fail @@ pp_to_string "**Primitive** " "runRedZone found an unexpected sensitivity: %a" pp_si si
            end
        | _ -> fail @@ pp_to_string "**Primitive** " "runRedZone's function argument has non-lollipop type: %a" pp_type tyf
      ) >>= fun succ ->
      match succ with
        | Error s -> genFailResult s
        | Ok n -> attemptRedZone n >>= fun succ ->
                  if succ then begin
                    match Fuzztoml.runCompiled (!rzFileName) pf db outty with
                    | Error s -> genFailResult s
                    | Ok res -> typeToMaker di outty >>= fun mker -> 
                                return (TmRight(di, mker res, TyPrim PrimString))
                  end
(*                  if succ then Interpreter.interp (TmApp(di, pf, db)) >>= fun a -> return (TmRight(di, a, TyPrim PrimString))*)
                  else genFailResult "Database is all used up"
    end

(* Here are ones specifically for bag stuff. *)
let showBagFun
  (b : term list)
  : string interpreter =
    mapM (fun t -> Interpreter.interp t >>= exString "showBag") b >>= fun strList ->
    return @@ String.concat "," strList

let bagsumLFun
  (n : int)
  (b : term list)
  : (ty * float list) interpreter =
    let rec sumUp xs ys = match xs,ys with
            | x::xs,y::ys -> (x +. y)::sumUp xs ys
            | xs,[] -> xs
            | [],ys -> ys
    in 
    mapM (fun t -> Interpreter.interp t >>= exList exNum "bagsumL") b >>= fun numlstlst ->
    return @@ (TyPrim PrimNum, List.fold_left sumUp [] numlstlst)

let rec bagfoldlFun
  (f : term)
  (a : term)
  (bbag : term list)
  : term interpreter = 
    match bbag with
    | [] -> return a
    | b::bs -> Interpreter.interp (TmApp(di, TmApp(di, f, a), b)) >>= fun x ->
               bagfoldlFun f x bs

let bagPairOperateFun
  (tyo : ty)
  (f : term)
  (g : term)
  (bag : term list)
  : (term * term) interpreter = 
    mapM (fun t -> Interpreter.interp t >>= exPair exAny exAny "bagPairOperate") bag >>= fun bagp ->
    let (ba, bb) = List.split bagp in
    (match tyo with
      | TyTensor(ta,tb) -> return (ta,tb)
      | _               -> fail "**Primitive** bagPairOperate found a weird type")
      >>= fun (ta,tb) ->
    Interpreter.interp (TmApp(di, f, mkBag di (ta, ba))) >>= fun outA ->
    Interpreter.interp (TmApp(di, g, mkBag di (tb, bb))) >>= fun outB ->
    return (outA, outB)
    

let bagmapFun 
  (ty : ty)
  (f : term)
  (b : term list)
  : (ty * term list) interpreter = 
    mapM (fun t -> Interpreter.interp (TmApp(di, f, t))) b >>= fun tmlst ->
    return (ty, tmlst)
    (*return (ty, List.map (fun tm -> TmApp(di, f, tm)) b)*)

let bagsplitFun
  (oty : ty)
  (f : term)
  (b : term list)
  : ((ty * term list) * (ty * term list)) interpreter = 
    (match oty with
      | TyTensor(ty,_)  -> return ty
      | _               -> fail @@ pp_to_string "** Primitive ** " "bagsplit expected a tensor output but found %a" pp_type oty
    ) >>= fun bty ->
    mapM (fun tm -> Interpreter.interp (TmApp(di, f, tm)) >>= exBool "bagsplit" >>= fun res -> return (tm, res)) b >>= fun lst ->
    let (lst1, lst2) = List.partition snd lst in
    return ((bty, List.map fst lst1), (bty, List.map fst lst2))


(* Here are ones specifically for differential private noise. *)
let addNoiseFun
  (eps : float)
  (n : float)
  : float = n +. Math.lap (1.0 /. eps)


(* expMechFun : num[s] -> num[k] -> (R -> DB -o[k] num) -> R bag -> DB -o[s] fuzzy R *)
let expMechFun
  (eps : float)
  (k : float)
  (quality : term)
  (rbag : term list)
  (db : term)
  : term interpreter = 
    mapM (fun r -> Interpreter.interp (TmApp(di, TmApp(di, quality, r), db)) 
            >>= exNum "expMech"
            >>= fun q -> return (r, q +. Math.lap (k /. eps))) rbag >>= fun problist ->
(*    Support.Error.message 0 Support.Options.Interpreter Support.FileInfo.dummyinfo 
      "--- expMech: Probabilities are: %s" (String.concat "," (List.map (fun x -> string_of_float (snd x)) problist));*)
    let (res, _i) = List.fold_left 
            (fun best r -> if abs_float (snd r) > abs_float (snd best) then r else best)
            (mkUnit di (), 0.0) problist in
    return res

(* expMechWithScoreFun : num[s] -> num[k] -> (R -> DB -o[k] num) -> R bag -> DB -o[s] fuzzy (R, num) *)
let expMechWithScoreFun
  (eps : float)
  (k : float)
  (quality : term)
  (rbag : term list)
  (db : term)
  : (term * float) interpreter = 
    mapM (fun r -> Interpreter.interp (TmApp(di, TmApp(di, quality, r), db)) 
            >>= exNum "expMechWithScore"
            >>= fun q -> return (r, q +. Math.lap (k /. eps))) rbag >>= fun problist ->
(*    Support.Error.message 0 Support.Options.Interpreter Support.FileInfo.dummyinfo 
      "--- expMechWithScore: Probabilities are: %s" (String.concat "," (List.map (fun x -> string_of_float (snd x)) problist));*)
    let (res, i) = List.fold_left 
            (fun best r -> if abs_float (snd r) > abs_float (snd best) then r else best)
            (mkUnit di (), 0.0) problist in
    return (res, i)

let expMechPreWithScoreFun
  (eps : float)
  (j : float)
  (k : float)
  (preprocess : term)
  (quality : term)
  (rbag : term list)
  (db : term)
  : (term * float) interpreter = 
    Interpreter.interp (TmApp(di, preprocess, db)) >>= fun intermediateTerm ->
    mapM (fun r -> Interpreter.interp (TmApp(di, TmApp(di, quality, r), intermediateTerm)) 
            >>= exNum "expMechWithScore"
            >>= fun q -> return (r, q +. Math.lap (j *. k /. eps))) rbag >>= fun problist ->
(*    Support.Error.message 0 Support.Options.Interpreter Support.FileInfo.dummyinfo 
      "--- expMechWithScore: Probabilities are: %s" (String.concat "," (List.map (fun x -> string_of_float (snd x)) problist));*)
    let (res, i) = List.fold_left 
            (fun best r -> if abs_float (snd r) > abs_float (snd best) then r else best)
            (mkUnit di (), 0.0) problist in
    return (res, i)

(* expMechUnsafeFun : num[s] -> num[k] -> int -> (DB -o[k] ((R,num) bag)) -> DB -o[s] fuzzy R *)
(* This function cannot is trying to be a shortcut/simplification of expMech, but it cannot work.  
   We would like to say something like: if we use the DB k times to make a k-length bag, then that 
   means we've used it once for each element of the bag.  However, this does not follow.  Thus, 
   we really should use the regular expMech.  But, expMech can be quite slow, and this version 
   speeds things up.  Thus, it's left around for uses in performing examples, but it is not allowed 
   to be actually released. *)
let expMechUnsafeFun
  (eps : float)
  (k : float)
  (rmod : int)
  (quality : term)
  (db : term)
  : term interpreter = 
    Interpreter.interp (TmApp(di, quality, db)) >>= exBag "expMechUnsafe" >>= fun resbag ->
    mapM (fun t -> Interpreter.interp t >>= exPair exAny exNum "expMechUnsafe") resbag >>= fun rnumlist ->
    let problist = List.map (fun (r,q) -> (r, q +. Math.lap (k /. eps /. (float_of_int rmod)))) rnumlist in
(*    Support.Error.message 0 Support.Options.Interpreter Support.FileInfo.dummyinfo 
      "--- expMechUnsafe: Scores are: %s" (String.concat "," (List.map (fun x -> string_of_float (snd x)) rnumlist));
    Support.Error.message 0 Support.Options.Interpreter Support.FileInfo.dummyinfo 
      "--- expMechUnsafe: Probabilities are: %s" (String.concat "," (List.map (fun x -> string_of_float (snd x)) problist));*)
    let (res, _i) = List.fold_left 
            (fun best r -> if abs_float (snd r) > abs_float (snd best) then r else best)
            (mkUnit di (), 0.0) problist in
    return res


(*****************************************************************************)
(* Here are the *fromFile primitives. *)
let bagFromFileFun
  (oty : ty)
  (maxsize : int)
  (fn : string)
  : (ty * term list) interpreter = 
    let lines = fileLines maxsize fn in
    (match oty with
      | TyPrim1 (Prim1Bag, subty)   -> return subty
      | _   -> fail @@ pp_to_string "" "**Primitive** bagFromFile found a weird type %a." pp_type oty
    ) >>= fun subty ->
    typeToMaker di subty >>= fun lineFun ->
    return (oty, List.map lineFun lines)

let listFromFileFun
  (oty : ty)
  (maxsize : int)
  (fn : string)
  : term interpreter = 
    let lines = fileLines maxsize fn in
    (match oty with
      | TyMu (_, TyUnion (TyPrim PrimUnit, TyTensor (subty, TyVar _))) -> return subty
      | _   -> fail @@ pp_to_string "" "**Primitive** listFromFile found a weird type %a." pp_type oty
    ) >>= fun subty ->
    typeToMaker di subty >>= fun lineFun ->
    return (List.fold_right (fun v fzlst -> TmFold (di, oty, TmRight (di, TmPair (di, v, fzlst), TyPrim PrimUnit)))
                            (List.map lineFun lines) 
                            (TmFold (di, oty, TmLeft (di, TmPrim (di, PrimTUnit), TyTensor(subty, oty)))))

let listbagFromFileFun
  (oty : ty)
  (maxsize : int)
  (fn : string)
  (rexp : string)
  : (ty * term list) interpreter = 
    let lines = fileLines maxsize fn in
    (match oty with
      | TyPrim1 (Prim1Bag, TyMu (_, TyUnion (TyPrim PrimUnit, TyTensor (subty, TyVar _)))) -> return subty
      | _   -> fail @@ pp_to_string "" "**Primitive** listbagFromFile found a weird type %a." pp_type oty
    ) >>= fun subty ->
    typeToMaker di subty >>= fun wordFun ->
    let lineFun line = List.fold_right (fun v fzlst -> TmFold (di, oty, TmRight (di, TmPair (di, v, fzlst), TyPrim PrimUnit)))
                            (List.map wordFun (Str.split (Str.regexp rexp) line))  (*"[ \t]+"*)
                            (TmFold (di, oty, TmLeft (di, TmPrim (di, PrimTUnit), subty)))
    in return (oty, List.map lineFun lines)


let vectorbagFromFileFun
  (oty : ty)
  (maxsize : int)
  (fn : string)
  (rexp : string)
  : (ty * term list) interpreter = 
    let lines = fileLines maxsize fn in
    (match oty with
      | TyPrim1 (Prim1Bag, TyPrim1 (Prim1Vector, subty)) -> return subty
      | _   -> fail @@ pp_to_string "" "**Primitive** vectorbagFromFile found a weird type %a." pp_type oty
    ) >>= fun subty ->
    typeToMaker di subty >>= fun wordFun ->
    let lineFun line = mkVector di (TyPrim1 (Prim1Vector, subty), List.map wordFun (Str.split (Str.regexp rexp) line))
    in return (oty, List.map lineFun lines)



let vindexFun
  (def : term)
  (i : int)
  (v : term list)
  : term = 
    let rec nth i lst = match lst with
            | [] -> def
            | x::xs -> if i <= 0 then x else nth (i-1) xs
    in nth i v

let vunconsFun
  (oty : ty)
  (def : term)
  (v : term list)
  : (term * (ty * term list)) interpreter = 
    match v with
    | [] -> return (def, (oty, []))
    | x::xs -> return (x, (oty, xs))

let listToVectorFun
  (oty : ty)
  (lst : term list)
  : (ty * term list) interpreter = return (oty, lst)

let vectorToListFun
  (oty : ty)
  (lst : term list)
  : (ty * term list) interpreter = 
    (match oty with
      | TyMu (_, TyUnion (TyPrim PrimUnit, TyTensor (subty, TyVar _))) -> return subty
      | _   -> fail @@ pp_to_string "" "**Primitive** vectorToList found a weird type %a." pp_type oty
    ) >>= fun subty -> return (subty, lst)


let bagsumVFun
  (oty : ty)
  (n : int)
  (b : term list)
  : (ty * term list) interpreter =
    let rec sumUp xs ys = match xs,ys with
            | x::xs,y::ys -> (x +. y)::sumUp xs ys
            | xs,[] -> xs
            | [],ys -> ys
    in 
    mapM (fun t -> Interpreter.interp t >>= exVector "bagsumV" >>= mapM 
            (fun t' -> Interpreter.interp t' >>= exNum "bagsumV")) b >>= fun numlstlst ->
    return (oty, List.map (mkNum di) (List.fold_left sumUp [] numlstlst))


let vectorIPFun
  (oty : ty)
  (lst1 : term list)
  (lst2 : term list)
  : float interpreter = 
  mapM (fun t -> Interpreter.interp t >>= exNum "vsum") lst1 >>= fun lst1' -> 
  mapM (fun t -> Interpreter.interp t >>= exNum "vsum") lst2 >>= fun lst2' -> 
  let rec f l1 l2 = match l1, l2 with
                    | x::xs, y::ys -> (x *. y) +. (f xs ys)
                    | _,_   -> 0.0
  in return (f lst1' lst2')

let vperformAtFun
  (oty : ty)
  (i : int)
  (f : term)
  (v : term list)
  : (ty * term list) interpreter =
    if i >= List.length v || i < 0 then
      fail @@ pp_to_string "" "**Primitive** vperformAt had an out-of-bounds list index %a." pp_type oty
    else
      let rec inner i l = match i,l with
        | _,[] -> return []
        | 0,x::xs -> Interpreter.interp (TmApp(di, f, x)) >>= fun x' -> return (x'::xs)
        | _,x::xs -> inner (i-1) xs >>= fun xs' -> return (x::xs')
      in inner i v >>= fun res -> return (oty, res)

let showVecFun
  (v : term list)
  : string interpreter =
    mapM (fun t -> Interpreter.interp t >>= exString "showVec") v >>= fun strList ->
    return @@ String.concat "," strList



(* Core primitive definitions for the runtime *)
let prim_list : (string * primfun) list = [

(* &-pair destruction *)
("_fst", PrimFun (fun (_, t) -> match t with
    | TmAmpersand(i, ta, tb) :: [] -> return ta
    | _ -> fail @@ pp_to_string "** Primitive ** " "fst expected an &-pair but found %a" (pp_list pp_term) t));
("_snd", PrimFun (fun (_, t) -> match t with
    | TmAmpersand(i, ta, tb) :: [] -> return tb
    | _ -> fail @@ pp_to_string "** Primitive ** " "snd expected an &-pair but found %a" (pp_list pp_term) t));

(* Logical Operators *)

("_lor",  fun_of_2args "_lor"  exBool exBool mkBool ( || ));
("_land", fun_of_2args "_land" exBool exBool mkBool ( && ));

("_eq",  fun_of_2args "_eq"  exAny exAny mkBool Syntax.tmEq);

(* Numerical Comparison Operators *)
("_lt",  fun_of_2args "_lt"  exNum exNum mkBool ( < ));
("_gt",  fun_of_2args "_gt"  exNum exNum mkBool ( > ));
("_lte", fun_of_2args "_lte" exNum exNum mkBool ( <= ));
("_gte", fun_of_2args "_gte" exNum exNum mkBool ( >= ));

(* Numerical Computation Operators *)
("_add", fun_of_2args "_add" exNum exNum mkNum ( +. ));
("_sub", fun_of_2args "_sub" exNum exNum mkNum ( -. ));
("_mul", fun_of_2args "_mul" exNum exNum mkNum ( *. ));
("_div", fun_of_2args "_div" exNum exNum mkNum ( /. ));

("_exp", fun_of_1arg "_exp" exNum mkNum ( exp ));
("_abs", fun_of_1arg "_abs" exNum mkNum ( abs_float ));
("cswp", fun_of_1arg "cswp" (exPair exNum exNum) (mkPair mkNum mkNum) (fun (x,y) -> if x < y then (x,y) else (y,x)));

(* Integer primitives *)
("_iadd", fun_of_2args "_iadd" exInt exInt mkInt ( + ));
("_isub", fun_of_2args "_isub" exInt exInt mkInt ( - ));
("_imul", fun_of_2args "_imul" exInt exInt mkInt ( * ));
("_idiv", fun_of_2args "_idiv" exInt exInt mkInt ( / ));
("intToPeano", fun_of_1arg_with_type_i "intToPeano" exInt mkAny intToPeanoFun);

(* clip creation *)
("clip", fun_of_1arg "clip" exNum mkClipped (fun x -> x));
("fromClip", fun_of_1arg "fromClip" exNum mkNum (fun x -> x));

(* String operations *)
("string_cc", fun_of_2args "string_cc" exString exString mkString ( ^ ));

(* Show functions *)
("showNum", fun_of_1arg "showNum" exNum mkString ( fun n -> if n = floor n then string_of_int (truncate n) else string_of_float n ));
("showInt", fun_of_1arg "showInt" exInt mkString ( string_of_int ));
("showBag", fun_of_1arg_i "showBag" exBag mkString showBagFun);
("showVec", fun_of_1arg_i "showVec" exVector mkString showVecFun);

(* Testing Utilities *)
("_assert",   fun_of_2args "_assert"   exString exBool mkUnit assertFun);
("assertEq", fun_of_3args "assertEq" exString exAny exAny mkUnit assertEqFun);
("print",   fun_of_1arg "print"   exString mkUnit (fun s -> ignore (printMsg di "%s" s)));

(* Probability monad operations *)
("_return", fun_of_1arg_i "_return" exAny mkAny (fun x -> onlyInFullEval "return" (return x)));

("loadDB", fun_of_2args_i "loadDB" exFun (exPair exNum exNum) mkUnit storeDB);

(* Red zone activation primitives *)
("tyCheckFuzz", fun_of_2args_i "tyCheckFuzz" exNum exAny mkAny tyCheckFuzzFun);
("runRedZone", fun_of_1arg_with_type_i "runRedZone" exFun mkAny (fun ty tm -> runRedZone ty 1.0 tm));
("runRedZoneS", fun_of_2args_with_type_i "runRedZoneS" exNum exFun mkAny runRedZone);

("getDelta",   fun_of_1arg_i "getDelta"   exAny mkNum (fun _ -> onlyInFullEval "getDelta"   getDelta));
("getEpsilon", fun_of_1arg_i "getEpsilon" exAny mkNum (fun _ -> onlyInFullEval "getEpsilon" getEpsilon));

(* Bag primitives *)
("emptybag", fun_of_no_args_with_type_i "emptybag" mkBag (fun ty -> return (ty,[])));
("addtobag", fun_of_2args_with_type_i "addtobag" exAny exBag mkBag
  (fun ty x xs -> return (ty, x::xs)));
("bagjoin", fun_of_2args_with_type_i "bagjoin" exBag exBag mkBag
  (fun ty b1 b2 -> return (ty, List.append b1 b2)));
("bagsize", fun_of_1arg "bagsize" exBag mkInt ( List.length ));

(* ("bagfoldl", fun_of_4args_i "bagfoldl" exNum exAny exAny exBag mkAny (fun _ -> bagfoldlFun)); *)

("bagmap", fun_of_2args_with_type_i "bagmap" exFun exBag mkBag bagmapFun);

("bagsum", fun_of_1arg_i "bagsum" exBag mkNum 
  (fun l -> mapM (fun t -> Interpreter.interp t >>= exNum "bagsum") l >>= fun l' -> return (List.fold_left (+.) 0.0 l')));
("bagsumL", fun_of_2args_i "bagsumL" exInt exBag (mkList mkNum) bagsumLFun);
("bagPairOperate", fun_of_3args_with_type_i "bagPairOperate" exFun exFun exBag (mkPair mkAny mkAny) bagPairOperateFun);

("bagsplit", fun_of_2args_with_type_i "bagsplit" exFun exBag (mkPair mkBag mkBag) bagsplitFun);


(* Differential Privacy mechanisms *)
("addNoise", fun_of_2args "addNoise" exNum exNum mkNum addNoiseFun);

("expMech", fun_of_5args_i "expMech" exNum exNum exFun exBag exAny mkAny expMechFun);
("expMechWithScore", fun_of_5args_i "expMechWithScore" exNum exNum exFun exBag exAny (mkPair mkAny mkNum) expMechWithScoreFun);
("expMechPreWithScore", fun_of_7args_i "expMechPreWithScore" 
    exNum exNum exNum exFun exFun exBag exAny (mkPair mkAny mkNum) expMechPreWithScoreFun);
("expMechUnsafe", fun_of_5args_i "expMechUnsafe" exNum exNum exInt exFun exAny mkAny expMechUnsafeFun);

(* Load data from external file *)
("bagFromFile",  fun_of_2args_with_type_i "bagFromFile"  exInt exString mkBag bagFromFileFun);
("listFromFile", fun_of_2args_with_type_i "listFromFile" exInt exString mkAny listFromFileFun);
("listbagFromFile", fun_of_3args_with_type_i "listbagFromFile" exInt exString exString mkBag listbagFromFileFun);



("vsize", fun_of_1arg "vsize" exVector mkInt ( List.length ));
("vmap", fun_of_2args_with_type_i "vmap" exFun exVector mkVector bagmapFun);
("vsum", fun_of_1arg_i "vsum" exVector mkNum 
  (fun l -> mapM (fun t -> Interpreter.interp t >>= exNum "vsum") l >>= fun l' -> return (List.fold_left (+.) 0.0 l')));
("vindex",  fun_of_3args "vindex"  exAny exInt exVector mkAny vindexFun);
("vuncons", fun_of_2args_with_type_i "vuncons" exAny exVector (mkPair mkAny mkVector) vunconsFun);
("vectorbagFromFile", fun_of_3args_with_type_i "vectorbagFromFile" exInt exString exString mkBag vectorbagFromFileFun);
("listToVector", fun_of_1arg_with_type_i "listToVector" (exList exAny) mkVector listToVectorFun);
("vectorToList", fun_of_1arg_with_type_i "vectorToList" exVector (mkList mkAny) vectorToListFun);
("bagsumV", fun_of_2args_with_type_i "bagsumV" exInt exBag mkVector bagsumVFun);
("vectorIP", fun_of_2args_with_type_i "vectorIP" exVector exVector mkNum vectorIPFun);
("vperformAt", fun_of_3args_with_type_i "vperformAt" exInt exFun exVector mkVector vperformAtFun);

]



