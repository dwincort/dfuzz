(* file name: interpreter.mli
   created by: Daniel Winograd-Cort
   Last modified: 12/15/2015
   
   Description:
   This file contains code for interpreting SFuzz terms.
*)
open Types

(* State monad for the context for interpreting *)
module InterpMonad : sig
  val (>>=) : 'a interpreter -> ('a -> 'b interpreter) -> 'b interpreter
  
  val (>>) : 'a interpreter -> 'b interpreter -> 'b interpreter
  
  val return : 'a -> 'a interpreter
  
  val mapM : ('a -> 'b interpreter) -> 'a list -> ('b list) interpreter
  
  (* Failing should never happen.  It is always due to either a type problem, which means the 
     type checker has failed, or a primitive problem. *)
  val fail : string -> 'a interpreter
  
  val withFailTerm : term -> term interpreter -> term interpreter
  
  val inPartial : 'a interpreter -> 'a interpreter
  
  val isInPartial : bool interpreter
  
  val attemptRedZone : epsilon -> bool interpreter
  
  val getDB : term interpreter
  
  val storeDB : term -> epsilon -> unit interpreter
  
  val getDelta : float interpreter
  
  val getEpsilon : epsilon interpreter
  
  val getPrimDefs : ((string * primfun) list) interpreter 
  
  val lookup_prim : string -> (ty * term list -> term interpreter) interpreter
end

open InterpMonad

val interp : term -> term interpreter

val run_interp : term -> (string * primfun) list -> string


