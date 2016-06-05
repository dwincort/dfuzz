(* TODO: We may need to do our own math in order to avoid floating
   point related attacks *)

(* Laplace function *)

let noNoise = ref false

(* The generating function for the laplace dist with parameter mu and
   b is X = mu - b sign(U) ln(1-2|U|) where -1/2<=U<1/2
*)
let lap sigma = if !noNoise then 0.0 else
  let u = (Random.float 1.0) -. 0.5 in
  sigma *. (copysign 1.0 u) *. log(1.0 -. 2.0 *. abs_float u)

(*  let s = 2 * (Random.int 2) - 1 in
    float_of_int s *. sigma *. log(Random.float 1.0)*)
