(* TODO: We may need to do our own math in order to avoid floating
   point related attacks *)

(* Laplace function *)

(* The generating function for the laplace dist with parameter mu and
   b is X = mu - b sign(U) ln(1-2|U|) where -1/2<=U<1/2
*)
let lap sigma =
  let s = 2.0 *. float_of_int (Random.int 2) -. 1.0 in
    s *. sigma *. log(Random.float 1.0)
