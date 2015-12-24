(* file name: types.ml
   created by: Daniel Winograd-Cort
   Last modified: 12/19/2015
   
   Description:
   This file contains the major types used in fuzz.
   We need to declare them together because they end up being
   cyclically defined in many ways.
*)

open Support.FileInfo

(* The fuzz_binding type allows us to differentiate between different 
   types of variable binding, for debug purposes. *)
type fuzz_binding =
    BiVar    (* Regular varible *)
  | BiTyVar  (* Type variable   *)

(* A var_info provides the Debruijn index for the variable (along with 
   some useful debug fields. *)
type var_info = {
  (* Indexes start at 0 *)
  v_index : int;

  (* Debug fields *)
  v_name  : string; (* The name is printed on screen, but it is ignored for all purposes *)
  v_size  : int;    (* The number of other variables in scope *)
  v_type  : fuzz_binding; (* What type of binding this is (either term or type *)
}

(* The information in a binder is entirely for debug purposes. *)
type binder_info = {
  b_name : string;       (* Name of the binder *)
  b_size : int;          (* How many outside binders we had when this binded was found *)
  b_type : fuzz_binding; (* What kind of binding this is *)
  b_prim : bool;         (* Is this a primitive *)
}

(* An either type, useful for computations that can error. *)
type ('a,'b) result = | Ok of 'a
                      | Error of 'b

(* Sensitivities *)
type si =
  | SiInfty
  | SiConst of float
  | SiTerm  of term
  | SiAdd   of si * si
  | SiMult  of si * si
  | SiLub   of si * si

(* Primitive types *)
and  ty_prim =
  | PrimNum
  | PrimInt
  | PrimUnit
  | PrimBool
  | PrimString
  | PrimClipped

(* Types with one argument *)
and  ty_prim1 =
  | Prim1Bag
  | Prim1Fuzzy

(* General types *)
and  ty =
  (* variables used in bindings *)
  | TyVar  of var_info

  (* Primitive types *)
  | TyPrim  of ty_prim
  | TyPrim1 of (ty_prim1 * ty)

  (* ADT *)
  | TyUnion     of ty * ty
  | TyTensor    of ty * ty
  | TyAmpersand of ty * ty

  (* Functional type *)
  | TyLollipop of ty * si * ty

  (* Fixpoint type *)
  | TyMu of binder_info * ty

  (* Quantified types *)
  | TyForall of binder_info * ty


(* Primitive Terms *)
and  term_prim =
  | PrimTUnit
  | PrimTNum    of float
  | PrimTInt    of int
  | PrimTBool   of bool
  | PrimTString of string

and  term =
  | TmVar of info * var_info
  (* Primitive terms *)
  | TmPrim      of info * term_prim
  (* TODO: Right now, the string in TmPrimFun is necessary, but in the future, I would like 
     to make the type (string * ty * term list * primfun) and have the string be entirely for 
     debug purposes. This will involve passing the primfun list to the parser instead 
     of the interpreter and having the parser look up the strings directly. *)
  | TmPrimFun   of info * string * ty * term list
  
  | TmBag       of info * ty * term list
  | TmPair      of info * term * term
  | TmTensDest  of info * binder_info * binder_info * term * term
  (* & constructor *)
  | TmAmpersand of info * term * term
  | TmLeft      of info * term * ty
  | TmRight     of info * term * ty
  | TmUnionCase of info * term * binder_info * term * binder_info * term
  (*                      t  of { inl(x)     => tm1  | inl(y)     => tm2  } *)

  (* Regular Abstraction and Applicacion *)
  | TmApp of info * term * term
  | TmAbs of info * binder_info * (si * ty) * ty option * term

  (* Recursive data types *)
  | TmFold    of info * ty * term
  | TmUnfold  of info * term

  (* Bindings *)
  | TmLet      of info * binder_info * si * term * term
  | TmLetRec   of info * binder_info * ty * term * term
  | TmSample   of info * binder_info * term * term

  (* Type Abstraction and Applicacion *)
  | TmTyAbs of info * binder_info * term
  | TmTyApp of info * term * ty

  (* Type definitions *)
  | TmTypedef of info * binder_info * ty * term
  
  (* Convenience *)
  | TmIfThenElse of info * term * term * term
  (*                    if b then t1 else t2 *)

(* Primitive functions *)
and  primfun = PrimFun of (ty * term list -> term interpreter)

(* Interpreter monad *)
(* TODO: The primfun list should be handled by the parser *)
and  'a interpreter = 
    ((term option * ty list)    (* The database and list of red zone computations performed so far *)
    * context option            (* The context option represents whether we are in partial 
                                   evaluation mode or not (Some context we are, None we aren't). *)
    * (string * primfun) list)  (* The primfun map is the initial set of primitive function implementations. *)
   -> ((term option * ty list)  (* The database and list of red zone computations as output *)
    * ('a, string) result)      (* the output is either an Ok value or an error with a string. *)

(* Contexts for parsing and type checking *)
and  context =
  {
    var_ctx   : (var_info * ty) list;
    tyvar_ctx : var_info list;
  }

