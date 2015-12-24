(* file name: prim.ml
   created by: Daniel Winograd-Cort
   Last modified: 12/20/2015
   
   Description:
   This file contains code for interpreting SFuzz primitives.
*)

open Types
open Interpreter.InterpMonad
module I = Support.FileInfo

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

let exBool name tb = match tb with 
  | TmPrim (_i, PrimTBool b) -> return b
  | _ -> fail ("** Primitive ** "^name^" expected a bool but found something else.")
let exNum name tn = match tn with 
  | TmPrim (_i, PrimTNum n) -> return n
  | _ -> fail ("** Primitive ** "^name^" expected a num but found something else.")
let exInt name tn = match tn with 
  | TmPrim (_i, PrimTInt n) -> return n
  | _ -> fail ("** Primitive ** "^name^" expected an int but found something else.")
let exString name ts = match ts with 
  | TmPrim (_i, PrimTString s) -> return s
  | _ -> fail ("** Primitive ** "^name^" expected a string but found something else.")
let exBag name ts = match ts with 
  | TmBag(_i, _ty, tlst) -> return tlst
  | _ -> fail ("** Primitive ** "^name^" expected a bag but found something else.")
let exFun _name t = return t (* Theoretically, we could check that it's actually a function, but we don't need to *)
let exAny _name t = return t

let mkBool i b   = TmPrim (i, PrimTBool b)
let mkNum i n    = TmPrim (i, PrimTNum n)
let mkInt i n    = TmPrim (i, PrimTInt n)
let mkString i s = TmPrim (i, PrimTString s)
let mkBag i (ty, l) = TmBag (i, ty, l)
let mkPair mk1 mk2 i (t1, t2) = TmPair (i, mk1 i t1, mk2 i t2)
let mkAny _i t   = t
let mkUnit i _   = TmPrim (i, PrimTUnit)

let di = I.dummyinfo

let fun_of_1arg_with_type_i
  (name : string)                           (* The name of the function - for debug purposes *)
  (earg : string -> term -> 'a interpreter) (* An extractor for the argument *)
  (mk : I.info -> 'b -> term)               (* A maker for the result *)
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
  (mk : I.info -> 'b -> term)               (* A maker for the result *)
  (op : 'a -> 'b interpreter)               (* The operation to perform *)
  : primfun = fun_of_1arg_with_type_i name earg mk (fun _ty x -> op x)

let fun_of_1arg
  (name : string)                           (* The name of the function - for debug purposes *)
  (earg : string -> term -> 'a interpreter) (* An extractor for the argument *)
  (mk : I.info -> 'b -> term)               (* A maker for the result *)
  (op : 'a -> 'b)                           (* The operation to perform *)
  : primfun = fun_of_1arg_with_type_i name earg mk (fun _ty x -> return (op x))

let fun_of_2args_with_type_i
  (name : string)                           (* The name of the function - for debug purposes *)
  (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
  (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
  (mk : I.info -> 'c -> term)               (* A maker for the result *)
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
  (mk : I.info -> 'c -> term)               (* A maker for the result *)
  (op : 'a -> 'b -> 'c interpreter)         (* The operation to perform *)
  : primfun = fun_of_2args_with_type_i name efst esnd mk (fun _ty x y -> op x y)

let fun_of_2args 
  (name : string)                           (* The name of the function - for debug purposes *)
  (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
  (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
  (mk : I.info -> 'c -> term)               (* A maker for the result *)
  (op : 'a -> 'b -> 'c)                     (* The operation to perform *)
  : primfun = fun_of_2args_with_type_i name efst esnd mk (fun _ty x y -> return (op x y))

let fun_of_3args_with_type_i
  (name : string)                           (* The name of the function - for debug purposes *)
  (efst : string -> term -> 'a interpreter) (* An extractor for the first argument *)
  (esnd : string -> term -> 'b interpreter) (* An extractor for the second argument *)
  (ethd : string -> term -> 'c interpreter) (* An extractor for the second argument *)
  (mk : I.info -> 'd -> term)               (* A maker for the result *)
  (op : ty -> 'a -> 'b -> 'c -> 'd interpreter) (* The operation to perform *)
  : primfun = 
  PrimFun (fun (ty, tlst) -> match tlst with
    | ta :: tb :: tc :: []
        -> efst name ta >>= fun a ->
           esnd name tb >>= fun b ->
           ethd name tc >>= fun c ->
           op ty a b c >>= fun res -> return (mk di res)
    | _ -> fail ("** Primitive ** "^name^" expected 3 arguments but found something else."))


let runRedZone
  (ty : ty)
  (f : term)
  : term interpreter =
  getDB >>= fun db ->
  inPartial (Interpreter.interp f) >>= fun pf ->
  Support.Error.message 3 Support.Options.Interpreter Support.FileInfo.dummyinfo 
    "--- RunRedZone: Partial evaluation results in: %a" Print.pp_term pf;
  let tyf = Tycheck.get_type true pf in
  storeRedType tyf >>= fun succ ->
  if succ then Interpreter.interp (TmApp(di, pf, db)) >>= fun a -> return (TmRight(di, a, TyPrim PrimString))
          else begin match ty with
                 | TyUnion(_, aty) -> return (TmLeft(di, TmPrim(di, PrimTString "Fail"), aty))
                 | _ -> fail "Weird type in runRedZone"
               end


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

(* FIXME: Implement this
(* TODO: add epsilon parameter *)
(* expMechFun : (R -> A bag -o num) -> R bag -> A bag -o fuzzy R *)
let expMechFun vquality vrbag vdb = 
  let eps = 0.1 in
  let foldFun (best_i, cur_i, cur_max) n = if n > cur_max then (cur_i, cur_i+1, n) else (best_i, cur_i+1, cur_max) in
  let quality vr = valApp vquality vr         >>= fun vf_intermediate ->
                   valApp vf_intermediate vdb >>= fun vqual ->
                   match vqual with
                     | VNum n -> return n
                     | _      -> fail "**Primitive** expMech's quality function did not produce a num value as expected."
  in match vrbag with
      | VBag rs -> mapM quality rs >>= fun list_qs ->
                   let list_prob = List.map (fun q -> q +. Math.lap (2.0 /. eps)) list_qs in
                   let (i,_,_) = List.fold_left foldFun (-1,0,neg_infinity) list_prob in
                   return (List.nth rs i)
      | _       -> fail "**Primitive** expMech expected a bag value but didn't find one."

*)


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
("_eq",  fun_of_2args "_eq"  exAny exAny mkBool ( = ));
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

(* Careful! Only sound if divisor >= 1. *)
("_ldiv", fun_of_2args "_ldiv" exNum exNum mkNum ( /. ));

(* Integer primitives *)
("_iadd", fun_of_2args "_iadd" exInt exInt mkInt ( + ));
("_isub", fun_of_2args "_isub" exInt exInt mkInt ( - ));
("_imul", fun_of_2args "_imul" exInt exInt mkInt ( * ));
("_idiv", fun_of_2args "_idiv" exInt exInt mkInt ( / ));

(* clip creation *)
("clip", fun_of_1arg "clip" exNum mkNum (fun x -> if x > 1.0 then 1.0 else if x < 0.0 then 0.0 else x));

(* String operations *)
("num2string", fun_of_1arg "num2string" exNum mkString ( string_of_float ));
("string_cc", fun_of_2args "string_cc" exString exString mkString ( ^ ));

(* Probability monad operations *)
("_return", fun_of_1arg "_return" exAny mkAny (fun x -> x));

("loadDB", fun_of_1arg_i "loadDB" exAny mkUnit storeDB);

(* Red zone activation primitives *)
("runRedZone", fun_of_1arg_with_type_i "runRedZone" exFun mkAny runRedZone);

(* Bag primitives *)
("emptybag", fun_of_1arg_with_type_i "emptybag" exAny mkBag (fun ty _ -> return (ty,[])));
("addtobag", fun_of_2args_with_type_i "addtobag" exAny exBag mkBag
  (fun ty x xs -> return (ty, x::xs)));
("bagjoin", fun_of_2args_with_type_i "bagjoin" exBag exBag mkBag
  (fun ty b1 b2 -> return (ty, List.append b1 b2)));
("bagsize", fun_of_1arg "bagsize" exBag mkNum (fun l -> float_of_int (List.length l)));

("bagmapins", fun_of_2args_with_type_i "bagmapins" exFun exBag mkBag bagmapFun);
("bagmap", fun_of_3args_with_type_i "bagmap" exFun exNum exBag mkBag 
  (fun ty f _timeout b -> bagmapFun ty f b));

("bagsum", fun_of_1arg_i "bagsum" exBag mkNum 
  (fun l -> mapM (exNum "bagsum") l >>= fun l' -> return (List.fold_left (+.) 0.0 l')));

("bagsplitins", fun_of_2args_with_type_i "bagsplitins" exFun exBag (mkPair mkBag mkBag) bagsplitFun);
("bagsplit", fun_of_3args_with_type_i "bagsplit" exFun exNum exBag (mkPair mkBag mkBag)
  (fun ty f _timeout b -> bagsplitFun ty f b));

(* FIXME: Implement this

(* Differential Privacy mechanisms *)
("expMech", PrimFun ("expMech", fun vquality -> return (PrimFun ("expMech'", fun vrbag -> return (PrimFun ("expMech''", fun vdb -> 
  expMechFun vquality vrbag vdb))))));

*)
]



