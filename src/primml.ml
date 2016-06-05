(* file name: primml.ml
   created by: Daniel Winograd-Cort
   Last modified: 12/20/2015
   
   Description:
   This file contains code for interpreting SFuzz primitives as if they were direct ocaml functions.
*)

type ('a,'b) either = | Left of 'a
                      | Right of 'b;;

let hd lst = match lst with
  | x::_ -> x
  | [] -> failwith "hd error"

(* Returns a file as a list of strings in reverse *)
let fileLines (maxLines : int) (filename : string) = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    for i=1 to maxLines; do
      lines := input_line chan :: !lines
    done;
    close_in chan;
    !lines
  with End_of_file ->
    close_in chan;
    !lines


(* &-pair destruction *)
let _fst (x,y) = x
let _snd (x,y) = y

(* Logical Operators *)

let _lor = (||)
let _land = (&&)
let _eq = (=)

(* Numerical Comparison Operators *)
let _lt = ( < )
let _gt = ( > )
let _lte = ( <= )
let _gte = ( >= )

(* Numerical Computation Operators *)
let _add = ( +. )
let _sub = ( -. )
let _mul = ( *. )
let _div = ( /. )

let div2 = (fun n -> n /. 2.0)
let div3 = (fun n -> n /. 3.0)
let _exp = ( exp )
let _abs = ( abs_float )
let cswp = (fun (x,y) -> if x < y then (x,y) else (y,x))

(* Integer primitives *)
let _iadd = ( + )
let _isub = ( - )
let _imul = ( * )
let _idiv = ( / )
let rec intToPeano n = if n <= 0.0 then Obj.magic (Left ()) else Obj.magic (Right (intToPeano (n -. 1.0)))
let rec peanoToInt x = match Obj.magic x with
        | Left () -> 0.
        | Right y -> 1. +. peanoToInt y

(* clip creation *)
let clip c = if c > 1.0 then 1.0 else if c < 0.0 then 0.0 else c
let fromClip c = c

(* String operations *)
let string_cc = (^)

(* Show functions *)
let showNum = fun n -> if n = floor n then string_of_int (truncate n) else string_of_float n
let showInt = string_of_int
let showBag (strList : string list) : string = String.concat "," strList
let showVec (strList : string list) : string = String.concat "," strList

(* Vector and list transform *)
let rec listToVector lst = match Obj.magic lst with
        | Left () -> []
        | Right (x,lst') -> x::(listToVector lst')
let rec vectorToList v = match v with
        | [] -> Obj.magic (Left ())
        | x::xs -> Obj.magic (Right (x, vectorToList xs))

(* Testing Utilities *)
let _assert  _ = failwith "assert not available in Red Zone"
let assertEq _ = failwith "assertEq not available in Red Zone"
let print    s = (*failwith "print not available in Red Zone"*)  Printf.eprintf "%s\n" s 

(* Probability monad operations *)
let _return x = x
let loadDB _ = failwith "loadDB not available in Red Zone"

(* Red zone activation primitives *)
let tyCheckFuzz _ = failwith "tyCheckFuzz not available in Red Zone"
let runRedZone  _ = failwith "runRedZone not available in Red Zone"
let runRedZoneS _ = failwith "runRedZoneS not available in Red Zone"

let getDelta   _ = failwith "getDelta not available in Red Zone"
let getEpsilon _ = failwith "getEpsilon not available in Red Zone"

(* Bag primitives *)
let emptybag = []
let addtobag x b = x::b
let bagjoin = List.append
let bagsize l = float_of_int (List.length l)

let bagmap f b = List.rev (List.rev_map f b)

let bagsum = List.fold_left (+.) 0.0
let bagsumL b = 
    let rec sumUp xs ys = match xs,ys with
            | x::xs,y::ys -> (x +. y)::sumUp xs ys
            | xs,[] -> xs
            | [],ys -> ys
    in 
    List.fold_left sumUp [] (List.rev_map listToVector b)

let bagPairOperate f g b = let (ba, bb) = List.split b in (f ba, g bb)

let bagsplit f b = List.partition

(* Differential Privacy mechanisms *)
let addNoise
  (eps : float)
  (n : float)
  : float = n +. Math.lap (1.0 /. eps)

let expMechWithScore (eps : float) (k : float) (quality : 'r -> 'db -> float) (rbag : 'r list) (db : 'db) : ('r * float) = 
  let problist = List.rev_map (fun r -> (r, quality r db +. Math.lap (k /. eps))) rbag in
  List.fold_left 
        (fun best r -> if abs_float (snd r) > abs_float (snd best) then r else best)
        (hd rbag, 0.0) problist
let expMech (eps : float) (k : float) (quality : 'r -> 'db -> float) (rbag : 'r list) (db : 'db) : 'r = 
  fst (expMechWithScore eps k quality rbag db)

let expMechPreWithScore
  (eps : float)
  (j : float)
  (k : float)
  (preprocess : 'db -> 'p)
  (quality : 'r -> 'p -> float)
  (rbag : 'r list)
  (db : 'db)
  : ('r * float) = 
    let iterm = preprocess db in
    let problist = List.map (fun r -> (r, quality r iterm +. Math.lap (j *. k /. eps))) rbag in
(*    Printf.eprintf
      "--- expMech: Probabilities are: %s" (String.concat ",\n" (List.map (fun x -> "("^string_of_float (Obj.magic (fst x))^","^string_of_float (snd x)^")") problist));*)
    List.fold_left 
          (fun best r -> if abs_float (snd r) > abs_float (snd best) then r else best)
          (hd rbag, 0.0) problist

(* Load data from external file *)
let bagFromFile     _ = failwith "bagFromFile not available in Red Zone"
let listFromFile    _ = failwith "listFromFile not available in Red Zone"
let listbagFromFile _ = failwith "listbagFromFile not available in Red Zone"

(* Vectors *)
let vsize l = float_of_int (List.length l)
let vmap f v = List.rev (List.rev_map f v)
let vsum = List.fold_left (+.) 0.0
let vindex (def : 'a) (i : float) (v : 'a list) : 'a = 
    let rec nth i lst = match lst with
            | [] -> def
            | x::xs -> if i <= 0. then x else nth (i -. 1.) xs
    in nth i v
let vuncons (def : 'a) (v : 'a list) : ('a * 'a list) = 
  match v with
    | [] -> (def, [])
    | x::xs -> (x, xs)

let vectorbagFromFile (maxsize : float) (fn : string) (rexp : string) : float list list = 
    let lines = fileLines (truncate maxsize) fn in
    let lineFun line = List.map (float_of_string) (Str.split (Str.regexp rexp) line)
    in List.rev_map lineFun lines

let bagsumV _i = 
    let rec sumUp xs ys = match xs,ys with
            | x::xs,y::ys -> (x +. y)::sumUp xs ys
            | xs,[] -> xs
            | [],ys -> ys
    in List.fold_left sumUp []
let vectorIP  (lst1 : float list) (lst2 : float list) : float = 
  let rec f l1 l2 = match l1, l2 with
                    | x::xs, y::ys -> (x *. y) +. (f xs ys)
                    | _,_   -> 0.0
  in f lst1 lst2

let vperformAt (i : float) (f : 'a -> 'b) (v : 'a list) : 'b list = 
  let rec inner i l = match l with
    | [] -> []
    | x::xs -> if i < 0.5 then (f x)::xs else x::(inner (i -. 1.) xs)
  in inner i v



