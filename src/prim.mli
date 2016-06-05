(* file name: prim.mli
   created by: Daniel Winograd-Cort
   Last modified: 12/15/2015
   
   Description:
   This file contains code for interpreting SFuzz primitives.
*)

open Types

val rzFileName : string ref

val prim_list : (string * primfun) list
