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

let di = dummyinfo
let message n = Support.Error.message n Support.Options.Interpreter di
let assertionMsg i = Support.Error.message (-1) Support.Options.Assertion i


(* The expectation functions take a term and return an ocaml value *)
let exBool name tb = match tb with 
  | TmPrim (_i, PrimTBool b) -> return b
  | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a bool but found %a" name pp_term tb
let exNum name tn = match tn with 
  | TmPrim (_i, PrimTNum n) -> return n
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
let exPair name ex1 ex2 tp = match tp with 
  | TmPair(_i, t1, t2) -> ex1 name t1 >>= fun v1 ->
                          ex2 name t2 >>= fun v2 ->
                          return (v1, v2)
  | _ -> fail @@ pp_to_string "** Primitive ** " "%s expected a pair but found %a" name pp_term tp
let exFun _name t = return t (* Theoretically, we could check that it's actually a function, but we don't need to *)
let exAny _name t = return t

(* The make functions turn an ocaml value into a term *)
let mkBool i b   = TmPrim (i, PrimTBool b)
let mkNum i n    = TmPrim (i, PrimTNum n)
let mkClipped i c = TmPrim (i, PrimTClipped c)
let mkInt i n    = TmPrim (i, PrimTInt n)
let mkString i s = TmPrim (i, PrimTString s)
let mkBag i (ty, l) = TmBag (i, ty, l)
let mkPair mk1 mk2 i (t1, t2) = TmPair (i, mk1 i t1, mk2 i t2)
let mkAny _i t   = t
let mkUnit i _   = TmPrim (i, PrimTUnit)

(* The fun_of_*_arg* functions are short hands for making the primitives easily *)
let fun_of_no_args_with_type_i
  (name : string)                           (* The name of the function - for debug purposes *)
  (mk : info -> 'a -> term)                 (* A maker for the result *)
  (op : ty -> 'a interpreter)               (* The operation to perform *)
  : primfun = 
  PrimFun (fun (ty, tlst) -> match tlst with
    | [] -> op ty >>= fun res -> return (mk di res)
    | _  -> fail ("** Primitive ** "^name^" expected no arguments but found something else."))

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
    | _ -> fail ("** Primitive ** "^name^" expected 1 argument but found something else."))

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
    | _ -> fail ("** Primitive ** "^name^" expected 2 arguments but found something else."))

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
  (ethd : string -> term -> 'c interpreter) (* An extractor for the second argument *)
  (mk : info -> 'd -> term)                 (* A maker for the result *)
  (op : ty -> 'a -> 'b -> 'c -> 'd interpreter) (* The operation to perform *)
  : primfun = 
  PrimFun (fun (ty, tlst) -> match tlst with
    | ta :: tb :: tc :: []
        -> efst name ta >>= fun a ->
           esnd name tb >>= fun b ->
           ethd name tc >>= fun c ->
           op ty a b c >>= fun res -> return (mk di res)
    | _ -> fail ("** Primitive ** "^name^" expected 3 arguments but found something else."))

let fun_of_3args_i
  (name : string)                           (* The name of the function - for debug purposes *)
  (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
  (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
  (ethd : string -> term -> 'c interpreter) (* An extractor for the second argument *)
  (mk : info -> 'd -> term)                 (* A maker for the result *)
  (op : 'a -> 'b -> 'c -> 'd interpreter)   (* The operation to perform *)
  : primfun = fun_of_3args_with_type_i name efst esnd ethd mk (fun _ty x y z -> op x y z)

let fun_of_3args
  (name : string)                           (* The name of the function - for debug purposes *)
  (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
  (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
  (ethd : string -> term -> 'c interpreter) (* An extractor for the second argument *)
  (mk : info -> 'd -> term)                 (* A maker for the result *)
  (op : 'a -> 'b -> 'c -> 'd)               (* The operation to perform *)
  : primfun = fun_of_3args_with_type_i name efst esnd ethd mk (fun _ty x y z -> return (op x y z))


let fun_of_4args_with_type_i
  (name : string)                           (* The name of the function - for debug purposes *)
  (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
  (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
  (ethd : string -> term -> 'c interpreter) (* An extractor for the second argument *)
  (efth : string -> term -> 'd interpreter) (* An extractor for the second argument *)
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
    | _ -> fail ("** Primitive ** "^name^" expected 4 arguments but found something else."))

let fun_of_4args_i
  (name : string)                           (* The name of the function - for debug purposes *)
  (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
  (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
  (ethd : string -> term -> 'c interpreter) (* An extractor for the second argument *)
  (efth : string -> term -> 'd interpreter) (* An extractor for the second argument *)
  (mk : info -> 'e -> term)                 (* A maker for the result *)
  (op : 'a -> 'b -> 'c -> 'd -> 'e interpreter) (* The operation to perform *)
  : primfun = fun_of_4args_with_type_i name efst esnd ethd efth mk (fun _ty a b c d -> op a b c d)



(*****************************************************************************)
(* Here we have modifying functions *)

(* Makes sure that the given function only evaluates when we are in full 
   evaluation mode (as opposed to partial. *)
let onlyInFullEval (name : string) (f : 'a interpreter) : 'a interpreter = 
  isInPartial >>= fun b ->
  if b then fail (name^" not to be evaluated during partial evaluation") else f


(*****************************************************************************)
(* Here we have specific helper functions for specific primitives. *)

let assertFun
  (s : string)
  (b : bool)
  : unit = 
    assertionMsg di "%s: %s" s (if b then "PASS" else "FAIL"); ()

let assertEqFun
  (s : string)
  (t1 : term)
  (t2 : term)
  : unit = 
    let res = if Syntax.tmEq t1 t2 
              then "PASS"
              else pp_to_string "FAIL " "(%a != %a)" pp_term t1 pp_term t2
    in assertionMsg di "%s: %s" s res; ()

let runRedZone
  (ty : ty)
  (sens : float)
  (f : term)
  : term interpreter =
    onlyInFullEval "runRedZone" (return ()) >>
    let genFailResult s = begin 
        match ty with
            | TyUnion(_, aty) -> return (TmLeft(di, TmPrim(di, PrimTString s), aty))
            | _ -> fail "runRedZone Internal: Weird type in runRedZone return type"
        end in
    getDB >>= fun db ->
    message 3 "--- RunRedZone: Before Partial evaluation: %a" pp_term f;
    inPartial (Interpreter.interp f) >>= fun pf ->
    message 3 "--- RunRedZone: Partial evaluation results in: %a" pp_term pf;
    match Tycheck.type_of pf (Ctx.empty_context, true) with 
        | Error e -> genFailResult @@ pp_to_string "" "%a" Tycheck.pp_tyerr e.v
        | Ok (tyf, _) -> begin
      message 3 "--- RunRedZone: Type checking completed and found type: %a" pp_type tyf;
      (match tyf with
        | TyLollipop(_, si, _) -> begin match si with
              | SiConst n -> if n <= sens then return (Ok n) else return (Error 
                  ("runRedZone expected a "^string_of_float sens^"-sensitive function but found a "^string_of_float n^"-sensitive function"))
              | SiInfty -> return @@ Error 
                  ("runRedZone expected a "^string_of_float sens^"-sensitive function but found an infinitely sensitive function")
              | _ -> fail "runRedZone Internal: The sensitivity of the function argument was unexpected"
            end
        | _ -> fail "runRedZone Internal: The function argument was of the wrong form") >>= fun succ ->
      match succ with
        | Error s -> genFailResult s
        | Ok n -> attemptRedZone n >>= fun succ ->
                  if succ then Interpreter.interp (TmApp(di, pf, db)) >>= fun a -> return (TmRight(di, a, TyPrim PrimString))
                  else genFailResult "Database is all used up"
    end

(* Here are ones specifically for bag stuff. *)
let bagshowFun
  (b : term list)
  : string interpreter =
    mapM (exString "bagshow") b >>= fun strList ->
    return @@ String.concat "," strList

let rec bagfoldlFun
  (f : term)
  (timeout : float)
  (a : term)
  (bbag : term list)
  : term interpreter = 
    match bbag with
    | [] -> return a
    | b::bs -> Interpreter.interp (TmApp(di, f, TmPair(di, a, b))) >>= fun x ->
               bagfoldlFun f timeout x bs

let bagmapFun 
  (ty : ty)
  (f : term)
  (b : term list)
  : (ty * term list) interpreter = 
    mapM Interpreter.interp (List.map (fun tm -> TmApp(di, f, tm)) b) >>= fun lst ->
    return (ty, lst)

let bagsplitFun
  (oty : ty)
  (f : term)
  (b : term list)
  : ((ty * term list) * (ty * term list)) interpreter = 
    (match oty with
      | TyTensor(ty,_)  -> return ty
      | _               -> fail ("** Primitive ** bagmap expected a Tensor output but found something else.")
    ) >>= fun bty ->
    mapM (fun tm -> Interpreter.interp (TmApp(di, f, tm)) >>= exBool "bagsplit" >>= fun res -> return (tm, res)) b >>= fun lst ->
    let (lst1, lst2) = List.partition snd lst in
    return ((bty, List.map fst lst1), (bty, List.map fst lst2))


(* Here are ones specifically for differential private noise. *)
let addNoiseFun
  (eps : float)
  (n : float)
  : float = n +. (Math.lap eps)


(* expMechFun : num[e] -> (R -> DB -o fuzzy num) -> R bag -> DB -o[e] fuzzy R *)
let expMechFun
  (eps : float)
  (quality : term)
  (rbag : term list)
  (db : term)
  : term interpreter = 
    mapM (fun r -> Interpreter.interp (TmApp(di, TmApp(di, quality, r), db)) 
            >>= exNum "expMech"
            >>= fun q -> return (r, q +. Math.lap (2.0 /. eps))) rbag >>= fun problist ->
(*    Support.Error.message 3 Support.Options.Interpreter Support.FileInfo.dummyinfo 
      "--- expMech: Probabilities are: %s" (String.concat "," (List.map (fun x -> string_of_float (snd x)) problist));*)
    let (res, _) = List.fold_left 
            (fun best r -> if snd r > snd best then r else best)
            (mkUnit di (), neg_infinity) problist in
    return res


(* expMechOnePassFun : num[e] -> (DB -o fuzzy ((R,num) bag)) -> DB -o[e] fuzzy R *)
let expMechOnePassFun
  (eps : float)
  (quality : term)
  (db : term)
  : term interpreter = 
    Interpreter.interp (TmApp(di, quality, db)) >>= exBag "expMechOnePass" >>= fun resbag ->
    mapM (exPair "expMechOnePass" exAny exNum) resbag >>= fun rnumlist ->
    let problist = List.map (fun (r,q) -> (r, q +. Math.lap (2.0 /. eps))) rnumlist in
(*    Support.Error.message 3 Support.Options.Interpreter Support.FileInfo.dummyinfo 
      "--- expMech: Probabilities are: %s" (String.concat "," (List.map (fun x -> string_of_float (snd x)) problist));*)
    let (res, _) = List.fold_left 
            (fun best r -> if snd r > snd best then r else best)
            (mkUnit di (), neg_infinity) problist in
    return res


(*****************************************************************************)
(* Here are some helpers for file and string parsing. *)
let fileLines (filename : string) = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines


let typeToMaker (ty : ty) : (string -> term) interpreter = match ty with
  | TyPrim PrimNum  -> return (fun s -> mkNum di (float_of_string s))
  | TyPrim PrimInt  -> return (fun s -> mkInt di (int_of_string s))
  | TyPrim PrimUnit -> return (fun s -> TmPrim (di, PrimTUnit))
  | TyPrim PrimBool -> return (fun s -> mkBool di (bool_of_string s))
  | TyPrim PrimString   -> return (mkString di)
  | TyPrim PrimClipped  -> return (fun s -> mkClipped di (let x = float_of_string s in 
                                                          if x > 1. then 1. else (if x < 0. then 0. else x)))
  | _ -> fail @@ pp_to_string "" "**Primitive** unsupported read type: %a." pp_type ty

(* Here are the *fromFile primitives. *)
let bagFromFileFun
  (oty : ty)
  (fn : string)
  : (ty * term list) interpreter = 
    let lines = fileLines fn in
    (match oty with
      | TyPrim1 (Prim1Bag, subty)   -> return subty
      | _   -> fail @@ pp_to_string "" "**Primitive** bagFromFile found a weird type %a." pp_type oty
    ) >>= fun subty ->
    typeToMaker subty >>= fun lineFun ->
    return (oty, List.map lineFun lines)

let listFromFileFun
  (oty : ty)
  (fn : string)
  : term interpreter = 
    let lines = fileLines fn in
    (match oty with
      | TyMu (_, TyUnion (TyPrim PrimUnit, TyTensor (subty, TyVar _))) -> return subty
      | _   -> fail @@ pp_to_string "" "**Primitive** listFromFile found a weird type %a." pp_type oty
    ) >>= fun subty ->
    typeToMaker subty >>= fun lineFun ->
    return (List.fold_right (fun v fzlst -> TmFold (di, oty, TmRight (di, TmPair (di, v, fzlst), TyPrim PrimUnit)))
                            (List.map lineFun lines) 
                            (TmFold (di, oty, TmLeft (di, TmPrim (di, PrimTUnit), subty))))

let listbagFromFileFun
  (oty : ty)
  (fn : string)
  : (ty * term list) interpreter = 
    let lines = fileLines fn in
    (match oty with
      | TyPrim1 (Prim1Bag, TyMu (_, TyUnion (TyPrim PrimUnit, TyTensor (subty, TyVar _)))) -> return subty
      | _   -> fail @@ pp_to_string "" "**Primitive** baglistFromFile found a weird type %a." pp_type oty
    ) >>= fun subty ->
    typeToMaker subty >>= fun wordFun ->
    let lineFun line = List.fold_right (fun v fzlst -> TmFold (di, oty, TmRight (di, TmPair (di, v, fzlst), TyPrim PrimUnit)))
                            (List.map wordFun (Str.split (Str.regexp "[ \t]+") line))
                            (TmFold (di, oty, TmLeft (di, TmPrim (di, PrimTUnit), subty)))
    in return (oty, List.map lineFun lines)




(* Core primitive definitions for the runtime *)
let prim_list : (string * primfun) list = [

(* &-pair destruction *)
("_fst", PrimFun (fun (_, t) -> match t with
    | TmAmpersand(i, ta, tb) :: [] -> return ta
    | _ -> fail "**Primitive** fst expected an &-pair but didn't find one."));
("_snd", PrimFun (fun (_, t) -> match t with
    | TmAmpersand(i, ta, tb) :: [] -> return tb
    | _ -> fail "**Primitive** snd expected an &-pair but didn't find one."));

(* Logical Operators *)

("_lor",  fun_of_2args "_lor"  exBool exBool mkBool ( || ));
("_land", fun_of_2args "_land" exBool exBool mkBool ( && ));

(* These should be general equality, but right now, I'm not sure they are *)
("_eq",  fun_of_2args "_eq"  exAny exAny mkBool Syntax.tmEq);
("_neq", fun_of_2args "_neq" exAny exAny mkBool ( <> ));

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

("div2", fun_of_1arg "div2" exNum mkNum (fun n -> n /. 2.0));
("div3", fun_of_1arg "div3" exNum mkNum (fun n -> n /. 3.0));
("_exp", fun_of_1arg "_exp" exNum mkNum ( exp ));
("_abs", fun_of_1arg "_abs" exNum mkNum ( abs_float ));

(* Integer primitives *)
("_iadd", fun_of_2args "_iadd" exInt exInt mkInt ( + ));
("_isub", fun_of_2args "_isub" exInt exInt mkInt ( - ));
("_imul", fun_of_2args "_imul" exInt exInt mkInt ( * ));
("_idiv", fun_of_2args "_idiv" exInt exInt mkInt ( / ));

(* clip creation *)
("clip", fun_of_1arg "clip" exNum mkClipped (fun x -> if x > 1.0 then 1.0 else if x < 0.0 then 0.0 else x));
("fromClip", fun_of_1arg "fromClip" exNum mkNum (fun x -> x));

(* String operations *)
("string_cc", fun_of_2args "string_cc" exString exString mkString ( ^ ));

(* Show functions *)
("showNum", fun_of_1arg "showNum" exNum mkString ( string_of_float ));
("showInt", fun_of_1arg "showInt" exInt mkString ( string_of_int ));

(* Testing Utilities *)
("assert",   fun_of_2args "assert"   exString exBool mkUnit assertFun);
("assertEq", fun_of_3args "assertEq" exString exAny exAny mkUnit assertEqFun);

(* Probability monad operations *)
("_return", fun_of_1arg "_return" exAny mkAny (fun x -> x));

("loadDB", fun_of_2args_i "loadDB" exAny exNum mkUnit storeDB);

(* Red zone activation primitives *)
("runRedZone", fun_of_1arg_with_type_i "runRedZone" exFun mkAny (fun ty tm -> runRedZone ty 1.0 tm));
("runRedZoneS", fun_of_2args_with_type_i "runRedZone" exNum exFun mkAny runRedZone);

("getDelta",   fun_of_1arg_i "getDelta"   exAny mkNum (fun _ -> onlyInFullEval "getDelta"   getDelta));
("getEpsilon", fun_of_1arg_i "getEpsilon" exAny mkNum (fun _ -> onlyInFullEval "getEpsilon" getEpsilon));

(* Bag primitives *)
("emptybag", fun_of_no_args_with_type_i "emptybag" mkBag (fun ty -> return (ty,[])));
("addtobag", fun_of_2args_with_type_i "addtobag" exAny exBag mkBag
  (fun ty x xs -> return (ty, x::xs)));
("bagjoin", fun_of_2args_with_type_i "bagjoin" exBag exBag mkBag
  (fun ty b1 b2 -> return (ty, List.append b1 b2)));
("bagsize", fun_of_1arg "bagsize" exBag mkNum (fun l -> float_of_int (List.length l)));
("bagshow", fun_of_1arg_i "bagshow" exBag mkString bagshowFun);

("bagfoldl", fun_of_4args_i "bagfoldl" exAny exNum exAny exBag mkAny bagfoldlFun);

("bagmapins", fun_of_2args_with_type_i "bagmapins" exFun exBag mkBag bagmapFun);
("bagmap", fun_of_3args_with_type_i "bagmap" exFun exNum exBag mkBag 
  (fun ty f _timeout b -> bagmapFun ty f b));

("bagsum", fun_of_1arg_i "bagsum" exBag mkNum 
  (fun l -> mapM (exNum "bagsum") l >>= fun l' -> return (List.fold_left (+.) 0.0 l')));

("bagsplitins", fun_of_2args_with_type_i "bagsplitins" exFun exBag (mkPair mkBag mkBag) bagsplitFun);
("bagsplit", fun_of_3args_with_type_i "bagsplit" exFun exNum exBag (mkPair mkBag mkBag)
  (fun ty f _timeout b -> bagsplitFun ty f b));


(* Differential Privacy mechanisms *)
("addNoise", fun_of_2args "addNoise" exNum exNum mkNum addNoiseFun);

("expMech", fun_of_4args_i "expMech" exNum exFun exBag exAny mkAny expMechFun);
("expMechOnePass", fun_of_3args_i "expMechOnePass" exNum exFun exAny mkAny expMechOnePassFun);

(* Load data from external file *)
("bagFromFile",  fun_of_1arg_with_type_i "bagFromFile"  exString mkBag bagFromFileFun);
("listFromFile", fun_of_1arg_with_type_i "listFromFile" exString mkAny listFromFileFun);
("listbagFromFile", fun_of_1arg_with_type_i "listbagFromFile" exString mkBag listbagFromFileFun);

]



