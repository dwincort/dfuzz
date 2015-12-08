(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Support.FileInfo

(* Different types of variable binding, for debug purposes *)
type fuzz_binding =
    BiVar    (* Regular varible *)
  | BiTyVar  (* Type variable   *)

(* Variables and binders *)
type var_info = {
  v_index : int;

  (* Debug fields *)
  v_name  : string;
  v_size  : int;
  v_type  : fuzz_binding;
}

(* Adds n to a var_info *)
val var_shift : int -> int -> var_info -> var_info

(* All of the fields are debug information *)

type binder_info = {
  b_name : string;
  b_size : int;          (* How many outside binders we had when this binded was found *)
  b_type : fuzz_binding;
  b_prim : bool;
}

(* Types *)

(* Part 0: kinds *)
type kind =
    Star
  | Size
  | Sens

(* Part 1: Sensitivites *)
type si =
  (* Sizes *)
  | SiZero
  | SiSucc  of si
  (* Reals *)
  | SiInfty
  | SiConst of float
  | SiVar   of var_info
  | SiAdd   of si * si
  | SiMult  of si * si
  | SiLub   of si * si
  (* We only allow to sup the first variable *)
  | SiSup   of binder_info * kind * si

(* Shift variable indexes by n *)
val si_shift : int -> int -> si -> si

type si_cs = SiEq of (si * si)

val cs_shift : int -> int -> si_cs -> si_cs

(* Number of binders, index, and sens *)
(* Part 2: Regular "HM" types *)
(* Primitive types *)
type ty_prim =
    PrimNum
  | PrimInt
  | PrimUnit
  | PrimBool
  | PrimString
  | PrimClipped
  | PrimDBS

(* Types with one argument *)
(* XXX: Extend to types with n-ary arguments *)
type ty_prim1 =
    Prim1Set
  | Prim1Bag
  | Prim1Fuzzy

type ty =
  (* variables used in bindings *)
    TyVar  of var_info

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
  | TyForall     of binder_info * kind * ty

(* Shift all the open indexes by n *)
val ty_shift : int -> int -> ty -> ty

(* Capture avoiding sub, the term must be dependent on the number of
   binders under it is replaced *)
val ty_subst     : int -> ty -> ty -> ty

(* Unfold a mu type *)
val ty_unfold : ty -> ty

(* Terms *)

(* Primitive Terms *)
type term_prim =
    PrimTUnit
  | PrimTNum    of float
  | PrimTInt    of int
  | PrimTBool   of bool
  | PrimTString of string
  | PrimTFun    of string * ty
  | PrimTDBS    of string

val type_of_prim : term_prim -> ty

type term =
  | TmVar of info * var_info
  (* Primitive terms *)
  | TmPrim     of info * term_prim

  | TmPair      of info * term * term
  | TmTensDest  of info * binder_info * binder_info * term * term
  (* & constructor *)
  | TmAmpersand of info * term * term
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
  | TmTyAbs of info * binder_info * kind * term
  | TmTyApp of info * term * ty

  (* Type definitions *)
  | TmTypedef of info * binder_info * ty * term

val tmInfo : term -> info

(* Substitution for type annotations *)
(* tm[t/x] *)
val term_ty_subst : int -> ty -> term -> term
