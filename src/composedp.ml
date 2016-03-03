(* file name: composedp.ml
   created by: Daniel Winograd-Cort
   Created: 3/2/2016
   
   Description:
   This file contains implementations of the differential privacy 
   composition theorems as well as an algorithm that attempts to 
   determine the best way to compose a sequence of (delta, epsilon) 
   pairs.
*)

open Types

let pi = 4. *. atan 1.
type composeFun = ed list -> ed

(* Simple composition just adds up the delta and epsilon values. *)
let simpleComp : composeFun = fun edlst ->
  List.fold_left (fun (e1,d1) (e2,d2) -> (e1 +. e2, d1 +. d2)) (0.0,0.0) edlst


(* Advanced adaptive composition *)
let aaComp (d : delta) : (epsilon list -> ed) = fun elst ->
  let k = float_of_int (List.length elst) in
  let sumsquares = List.fold_left (fun accum x -> accum +. (x *. x)) 0.0 elst in
  let part1 = List.fold_left (fun accum e ->
        accum +. (e *. (exp(e) -. 1.0) /. (1.0 +. exp(e)))) 0.0 elst in
  let part2 = (1.0 +. 4.0 *. sumsquares) ** 2.0 in
  let part3 = log ((pi ** 2.0) *. (k ** 2.0) *. part2 /. (6.0 *. d)) in
  let part4 = sqrt (2.0 *. sumsquares *. part3) in
  (part1 +. part4, d)

let minEDWithinBudget (budget : ed) : composeFun = fun edlst ->
  let (ebudget, dbudget) = budget       in
  let (elst, dlst) = List.split edlst   in
  let (e1,d1) = simpleComp edlst        in
  if List.fold_left (+.) 0.0 dlst = 0.0 then begin
    let (e2,d2) = aaComp dbudget elst in
    if e1 < e2 then (e1,d1) else (e2,d2)
  end else (e1,d1)
