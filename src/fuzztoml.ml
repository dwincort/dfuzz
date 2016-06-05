open Format

open Types
open Print


let header =
"open Primml

let query = "

let dbdef = 
"
let db = "

let toString = 
"
let toString = "

let body noise =
"
let main () =
  Math.noNoise := "^string_of_bool noise^";
  Random.self_init ();
  Printf.printf \"%s\\n\" (toString (query db));
  ()

let res = main ();
"


let fileLines (maxLines : int) chan = 
  let lines = ref [] in
  try
    for i=1 to maxLines; do
      lines := input_line chan :: !lines
    done;
    close_in chan;
    List.rev !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines

(* contains s1 s2 returns the index at the occurence whenever the string s1 contains the string s2 and None otherwise *)
let contains (s1 : string) (s2 : string) : int option =
    let re = Str.regexp_string (Str.quote s2)
    in
        try Some (Str.search_forward re s1 0)
        with Not_found -> None


let rec gen_toString ppf ty = match ty with
  | TyPrim PrimNum  -> fprintf ppf "%s" "string_of_float"
  | TyPrim PrimInt  -> fprintf ppf "%s" "(fun i -> string_of_int (floor i))"
  | TyPrim PrimUnit -> fprintf ppf "%s" "(fun _ -> \"()\")"
  | TyPrim PrimBool -> fprintf ppf "%s" "string_of_bool"
  | TyPrim PrimString   -> fprintf ppf ""
  | TyPrim PrimClipped  -> fprintf ppf "%s" "string_of_float"
  | TyPrim1 (Prim1Bag, t) -> fprintf ppf "(fun lst -> String.concat \" \" (List.map %a lst))"
        gen_toString t
  | TyPrim1 (Prim1Vector, t) -> fprintf ppf "(fun lst -> String.concat \" \" (List.map %a lst))"
        gen_toString t
  | TyTensor (t1, t2) -> fprintf ppf "(fun xy -> \"(\"^(%a (fst xy))^\", \"^(%a (snd xy))^\")\")"
        gen_toString t1 gen_toString t2
  | _ -> failwith "**FuzzToML** unsupported output type"

let pwrap (s : string) : string = "("^s^")"

let gen_primitive (t : term_prim) : string =
  match t with
    PrimTUnit        -> "()"
  | PrimTNum(r)      -> pwrap (string_of_float r)
  | PrimTClipped(r)  -> pwrap (string_of_float r)
  | PrimTInt(n)      -> pwrap (string_of_int   n ^ ".0")
  | PrimTBool(b)     -> string_of_bool  b
  | PrimTString(s)   -> "\""^s^"\""


let rec gen_term ppf t =
  match t with
  | TmVar (_, v)  -> fprintf ppf "__%s" v.v_name

  | TmPrim (_, prim) -> fprintf ppf "%s" (gen_primitive prim)

  | TmPrimFun (_i, s, _, lst) ->
      fprintf ppf "(%s %a)" s (pp_list_generic gen_term "" "" " ") (List.map (fun (t,_,_,_) -> t) lst)
  
  | TmRecFun (_i, bi, _ty, tm, _) ->
      fprintf ppf "(let rec __%s = %a in __%s)" bi.b_name gen_term tm bi.b_name
  
  | TmBag    (_i, _ty, tmlist) -> fprintf ppf "%a" (pp_list_generic gen_term "[" "]" ";") tmlist
  | TmVector (_i, _ty, tmlist) -> fprintf ppf "%a" (pp_list_generic gen_term "[" "]" ";") tmlist
  | TmPair (_i, e1, e2) -> fprintf ppf "(%a,%a)" gen_term e1 gen_term e2
  | TmTensDest (_,  b_x, b_y, tm_e1, tm_e2) ->
      fprintf ppf "(match %a with (__%s,__%s) ->@\n @[%a@])"
        gen_term tm_e1 b_x.b_name b_y.b_name gen_term tm_e2
  | TmAmpersand (_i, e1, e2) -> fprintf ppf "(%a,%a)" gen_term e1 gen_term e2

  | TmLeft  (_i, tm, _ty) -> fprintf ppf "(Left  %a)" gen_term tm
  | TmRight (_i, tm, _ty) -> fprintf ppf "(Right %a)" gen_term tm
  | TmUnionCase (_, tm_e, bi_l, tm_l, bi_r, tm_r) ->
      fprintf ppf "(match %a with @[<v>| Left __%s -> %a @,| Right __%s -> %a)@]"
        gen_term tm_e bi_l.b_name gen_term tm_l bi_r.b_name gen_term tm_r

  (* Regular Abstraction and Applicacion *)
  | TmApp (_, f, a)  -> fprintf ppf "(@[%a@\n%a@])" gen_term f gen_term a
  | TmAbs (_, b, _sty, _t2, body) ->
      fprintf ppf "(fun __%s ->@\n @[%a@])" b.b_name gen_term body

  (* Recursive data types *)
  | TmFold(_i, _, tm) -> fprintf ppf "@[(Obj.magic %a)@]" gen_term tm
  | TmUnfold (_i, tm) -> fprintf ppf "@[(Obj.magic %a)@]" gen_term tm

  (* Bindings *)
  | TmLet (_, bi, _s, e1, e2) -> fprintf ppf "(let __%s = %a in@\n %a)" bi.b_name gen_term e1 gen_term e2
  | TmStmt (_, tm1, tm2) -> fprintf ppf "(%a;@\n %a)" gen_term tm1 gen_term tm2
  | TmSample (_, bi,  e1, e2) -> fprintf ppf "(let __%s = %a in@\n %a)" bi.b_name gen_term e1 gen_term e2

  (* Type Abstraction and Applicacion *)
  | TmTyAbs (_i,_bi,tm) -> gen_term ppf tm
  | TmTyApp (_i,tm,_ty) -> gen_term ppf tm

  (* Type definitions *)
  | TmTypedef (_i,_tn,_ty,tm) -> gen_term ppf tm
  
  (* Convenience *)
  | TmIfThenElse (_, tmb, tmt, tme) -> fprintf ppf "(if %a then %a else %a)" gen_term tmb gen_term tmt gen_term tme


let progToFile (fn : string) (f : term) (db : term) (ty : ty) : unit =
  let oc = open_out fn in
  let ocf = formatter_of_out_channel oc in
  fprintf ocf "%s@\n" header;
  gen_term ocf f;
  fprintf ocf "\n%s@\n" dbdef;
  fprintf ocf "((%a) ())" gen_term db;
(*   gen_term ocf db; *)
  fprintf ocf "\n%s@\n" toString;
  gen_toString ocf ty;
  fprintf ocf "\n%s@." (body (!Math.noNoise));
  close_out oc;
  ()

let runCompiled (fn : string) (f : term) (db : term) (ty : ty) : (string, string) result = 
  let file = "src/"^fn^".ml" in
  let native = "src/"^fn^".native" in
  let exec = "./"^fn^".native" in
  progToFile file f db ty;
  let buildResults,buildOutput = Unix.pipe () in
  ignore (Unix.waitpid [] (Unix.create_process
      "ocamlbuild" [|"ocamlbuild" ; "-use-ocamlfind" ; "-pkg" ; "unix,str" ; native |]
      Unix.stdin buildOutput Unix.stderr));
  Unix.close buildOutput;
  let build_ic = Unix.in_channel_of_descr buildResults in
  let s' = String.concat ";;" (fileLines 100 build_ic) in
  close_in build_ic;
  match (contains s' "Error") with
  | Some n -> Error (String.sub s' n (String.length s' - n))
  | None -> 
    let progResults,progOutput = Unix.pipe () in
    ignore (Unix.waitpid [] (Unix.create_process
        exec [| exec |]
        Unix.stdin progOutput Unix.stderr));
    Unix.close progOutput;
    let ic = Unix.in_channel_of_descr progResults in
    let s = String.concat "" (fileLines 100 ic) in
    close_in ic;
    Ok s

