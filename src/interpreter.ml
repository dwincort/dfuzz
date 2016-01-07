(* file name: interpreter.ml
   created by: Daniel Winograd-Cort
   Last modified: 12/15/2015
   
   Description:
   This file contains code for interpreting SFuzz terms.
*)
open Format

open Print
open Types
open Syntax

(* Native @@ is already in ocaml 4.0 *)
let (@@) x y = x y

module Opt = Support.Options
module Err = Support.Error

let interp_error = Err.error_msg Opt.Interpreter Support.FileInfo.dummyinfo

let interp_warning fi = Err.message 1 Opt.Interpreter fi
let interp_info    fi = Err.message 2 Opt.Interpreter fi
let interp_info2   fi = Err.message 3 Opt.Interpreter fi
let interp_debug   fi = Err.message 4 Opt.Interpreter fi
let interp_debug2  fi = Err.message 5 Opt.Interpreter fi
let interp_debug3  fi = Err.message 6 Opt.Interpreter fi
let interp_messageNoFi n = Err.message n Opt.Interpreter Support.FileInfo.dummyinfo



(* State monad for the context for interpreting *)
module InterpMonad = struct
  open Ctx
    
  let (>>=) (m : 'a interpreter) (f : 'a -> 'b interpreter) : 'b interpreter =
    fun ((db, pe, plst) as inp) -> match m inp with
      | (db', Ok a)       -> f a (db', pe, plst)
      | (_, Error _) as e   -> e
  
  let (>>) m f = m >>= fun _ -> f
  
  let return (x : 'a) : 'a interpreter = fun (db, _, _) -> (db, Ok x)
  
  let rec mapM (f : 'a -> 'b interpreter) (lst : 'a list) : ('b list) interpreter = 
    match lst with
      | []    -> return []
      | x::xs -> f x        >>= fun y  ->
                 mapM f xs  >>= fun ys ->
                 return (y::ys)
  
  let rec mapMSi (f : term -> term interpreter) (si : si) : si interpreter = 
    match si with
    | SiInfty         -> return @@ si
    | SiConst c       -> return @@ si
    | SiTerm  t       -> f t >>= fun x -> return @@ SiTerm x
    | SiAdd  (s1, s2) -> mapMSi f s1 >>= fun s1 -> mapMSi f s2 >>= fun s2 -> return @@ SiAdd  (s1, s2)
    | SiMult (s1, s2) -> mapMSi f s1 >>= fun s1 -> mapMSi f s2 >>= fun s2 -> return @@ SiMult (s1, s2)
    | SiLub  (s1, s2) -> mapMSi f s1 >>= fun s1 -> mapMSi f s2 >>= fun s2 -> return @@ SiLub  (s1, s2)
  
  let rec mapMTy (f : term -> term interpreter) (ty : ty) : ty interpreter = 
    match ty with
    | TyVar v                 -> return ty
    | TyPrim tp               -> return ty
    | TyPrim1 (tp, ty)        -> mapMTy f ty >>= fun ty' -> return @@ TyPrim1 (tp, ty')
    | TyUnion (ty1, ty2)      -> mapMTy f ty1 >>= fun ty1 -> mapMTy f ty2 >>= fun ty2 -> return @@ TyUnion    (ty1, ty2)
    | TyTensor(ty1, ty2)      -> mapMTy f ty1 >>= fun ty1 -> mapMTy f ty2 >>= fun ty2 -> return @@ TyTensor   (ty1, ty2)
    | TyAmpersand(ty1, ty2)   -> mapMTy f ty1 >>= fun ty1 -> mapMTy f ty2 >>= fun ty2 -> return @@ TyAmpersand(ty1, ty2)
    | TyLollipop(ty1, s, ty2) -> mapMTy f ty1 >>= fun ty1 -> 
                                 mapMSi f s   >>= fun s   ->
                                 mapMTy f ty2 >>= fun ty2 -> return @@ TyLollipop(ty1, s, ty2)
    | TyMu(b, ty)             -> mapMTy f ty >>= fun ty -> return @@ TyMu(b, ty)
    | TyForall(b, ty)         -> mapMTy f ty >>= fun ty -> return @@ TyForall(b, ty)
  
  (* Failing should never happen.  It is always due to either a type problem, which means the 
     type checker has failed, or a primitive problem. *)
  let fail (message : string) : 'a interpreter = fun (db, _, _) -> (db, Error message)
  
  let withFailTerm (tm : term) (m : term interpreter) : term interpreter = 
    fun ((_, pe, _) as inp) -> match pe, m inp with
      | _, ((_, Ok _) as res) -> res
      | None, ((_, Error _) as res) -> res
      | Some _, (db, Error s) -> begin
        interp_messageNoFi 4 "--- Skipping failure \"%s\"; reverting to state %a." s Print.pp_term tm;
        (db, Ok tm)
        end
  
  let inPartial (m : 'a interpreter) : 'a interpreter = 
    fun (db, _, plst) -> m (db, Some empty_context, plst)
  
  let isInPartial : bool interpreter = 
    fun (db, pe, _) -> match pe with
      | None   -> (db, Ok false)
      | Some _ -> (db, Ok true)
  
  let withAddedPartialCtx (id : string) (ty : ty) (m : 'a interpreter) : 'a interpreter = 
    fun (db, pe, plst) -> match pe with
      | None    -> m (db, pe, plst)
      | Some c  -> m (db, Some (extend_ctx_with_var' id ty c), plst)
  
  let getTyCheckCtx : context interpreter =
    fun (db, pe, _) -> match pe with
      | None    -> (db, Ok empty_context)
      | Some c  -> (db, Ok c)
  
  let attemptRedZone (sens : epsilon) : bool interpreter =
    fun (db, _, _) -> match db with
      | None -> (db, Error "**Interpreter** Tried to store a sensitivity when no DB was loaded")
      | Some (db, eps, silist) -> let sum = List.fold_left (+.) 0. silist in
            if sum +. sens > eps
            then (Some (db, eps, (eps -. sum) :: silist), Ok false)
            else (Some (db, eps, sens :: silist), Ok true)
  
  let getDB : term interpreter = 
    fun (o, _, _) -> match o with
      | None -> (o, Error "**Interpreter** No database loaded")
      | Some (db,_,_) -> (o, Ok db)
  
  let storeDB (db : term) (budget : epsilon) : unit interpreter = 
    fun (db_init, pe, _) -> match pe with
      | None -> (Some (db, budget, []), Ok ())
      | Some _ -> (interp_messageNoFi 1 "Trying to storeDB in red zone.  Quietly skipping ...";
                  (db_init, Ok ()))
  
  let getDelta : float interpreter = 
    return 0.0
  
  let getEpsilon : epsilon interpreter = 
    fun (db, _, _) -> match db with
      | None -> (db, Error "**Interpreter** Tried to get remaining epsilon budget when no DB was loaded")
      | Some (_, eps, silist) -> (db, Ok (eps -. (List.fold_left (+.) 0. silist)))
  
  let getPrimDefs : ((string * primfun) list) interpreter = 
    fun (db, _, plst) -> (db, Ok plst)
  
  let lookup_prim (id : string) : (ty * term list -> term interpreter) interpreter =
    let rec lookup l = match l with
      | []                    -> fail ("**Interpreter** Primitive "^id^" not found")
      | (s, PrimFun t) :: l'  -> if s = id then return t else lookup l'
    in getPrimDefs >>= lookup
    
end

open InterpMonad

(* val interp : term -> value interpreter *)
let rec interp t = withFailTerm t @@ match t with
  | TmPrim(i,pt) -> return t
  
  | TmPrimFun(_i, s, ty, tmlst)  ->
      if List.fold_left (fun b tm -> b && tmIsVal tm) true tmlst
      then begin
        lookup_prim s >>= fun f -> 
        f (ty, tmlst)
      end else fail @@ pp_to_string "**Interpreter** " "Unevaluated arguments in %a." pp_term t
  
  | TmVar(i,v) -> fail @@ "**Interpreter** Unexpected var: "^v.v_name
  
  | TmBag(_,_,_) -> return t
  
  (* Pairs *)
  | TmPair(i,t1,t2) -> 
      interp t1 >>= fun t1' ->
      interp t2 >>= fun t2' ->
      return @@ TmPair (i, t1', t2')
  
  | TmTensDest(i, b1, b2, t, tBody) ->
      interp t >>= fun t' -> 
      withFailTerm (TmTensDest(i, b1, b2, t', tBody))
      begin match t' with
        | TmPair (i', t1', t2') -> interp (tm_substTm t1' 0 0 (tm_substTm t2' 0 0 tBody))
        | _ -> fail @@ pp_to_string "**Interpreter** " "TensDest expected a pair but found %a." pp_term t'
      end
  
  (* & constructor *)
  | TmAmpersand(i, t1, t2) ->
      interp t1 >>= fun t1' ->
      interp t2 >>= fun t2' ->
      return @@ TmAmpersand (i, t1', t2')
  
  | TmLeft (i, t, ty)   -> interp t >>= fun t -> return (TmLeft (i, t, ty))
  | TmRight(i, t, ty)   -> interp t >>= fun t -> return (TmRight(i, t, ty))
  
  | TmUnionCase(i, t, bl, tlBody, br, trBody) ->
      interp t >>= fun t' -> 
      interp_debug i "--- Interpreting a union of: %a" Print.pp_term t';
      withFailTerm (TmUnionCase(i, t', bl, tlBody, br, trBody))
      begin match t' with
        | TmLeft (i',tl,_) -> interp (tm_substTm tl 0 0 tlBody)
        | TmRight(i',tr,_) -> interp (tm_substTm tr 0 0 trBody)
        | _                -> fail @@ pp_to_string "**Interpreter** " "Union expected a sum value but found %a" pp_term t'
      end

  (* Regular Abstraction and Applicacion *)
  (* Application is particularly complicated because of the case of 
     primitive functions.  Consider the case where a primitive function 
     is partially applied and then sent to the red zone.  We would need 
     some way to represent this partial appliaction, so we actually do a 
     little type checking.  It's a little odd, but I believe it's the 
     most elegant solution. *)
  | TmApp(i, tf, ta) -> interp_debug i "--- Entering application interpretation: %a" Print.pp_term t;
      interp ta >>= fun ta -> 
      interp tf >>= fun tf ->
      interp_debug i "--- Interpreting an application of %a with argument %a" Print.pp_term tf Print.pp_term ta;
      withFailTerm (TmApp(i, tf, ta))
      begin if not (tmIsVal ta)
        then fail @@ pp_to_string "**Interpreter** " "Application expected a fully evaluated argument but found %a." pp_term ta
        else begin match tf with
        | TmAbs(_,bi,_, _, t) -> interp (tm_substTm ta 0 0 t) 
        | TmTyAbs(i, bi, tm) ->
          (* The case of inferred application. *)
          interp (TmApp(i, tm, ta))
        | _ -> fail @@ pp_to_string "**Interpreter** " "Application expected a Prim or Lambda value but found %a." pp_term tf
        end
      end
  
  | TmAbs(i, bi, (si, ty), tyo, tm) -> 
    isInPartial >>= fun goUnder ->
    if goUnder then begin
      interp_debug i "%s" "--- Interpreter: Going under a lambda.";
      mapMSi interp si >>= fun si ->
      mapMTy interp ty >>= fun ty ->
      (match tyo with
        | None -> return None
        | Some t -> mapMTy interp t >>= fun x -> return (Some x)
      ) >>= fun tyo ->
      withAddedPartialCtx bi.b_name ty (interp tm) >>= fun tm ->
      interp_debug i "%s" "--- Interpreter: Exiting a lambda.";
      return @@ TmAbs(i, bi, (si, ty), tyo, tm)
      end
    else return t

  (* Recursive data types *)
  | TmFold(i, _, t) -> interp t
  | TmUnfold(i, t)  -> interp t

  (* Bindings *)
  | TmLet(i, b, _, t, tBody) ->
      interp t >>= fun t -> 
      interp_debug i "--- Interpreting let: Replacing %s with %a." b.b_name Print.pp_term t;
      interp_debug i "--- Finishing let.  New term is: %a." Print.pp_term (tm_substTm t 0 0 tBody);
      interp (tm_substTm t 0 0 tBody)
  
  | TmLetRec(i, b, ty, t, tBody) ->
      let t' = tm_substTm (TmLetRec(i, b, ty, t, TmVar(i,var_from_binder 0 b))) 0 0 t in
      interp (tm_substTm t' 0 0 tBody)
  
  | TmSample(i, b, t, tBody) ->
      interp t >>= fun t -> interp (tm_substTm t 0 0 tBody)

  (* Type Abstraction and Applicacion *)
  (* These are essentially no-ops, but because we might do type checking 
     on these later, we do need to properly propogate the types. *)
  | TmTyAbs(_, _, _) -> return t
  | TmTyApp(i, t, ty) ->
      interp t >>= fun t ->
      withFailTerm (TmTyApp(i, t, ty))
      begin if false (*not (tyIsVal ty)*)
        then fail @@ pp_to_string "**Interpreter** " "Type Application expected a fully evaluated type but found %a." pp_type ty
        else begin match t with
        | TmTyAbs(i', bi, tm)       -> interp (tm_substTy ty 0 0 tm)
        | _ -> fail @@ pp_to_string "**Interpreter** " "Type Application expected a Prim or TyLambda found %a." pp_term t
        end
      end

  (* Type definitions *)
  | TmTypedef(i,b,ty,tm) -> 
    interp_debug i "--- Interpreting typedef: New term is %a." Print.pp_term t;
    interp(tm_substTy (ty_shiftTy 0 (-1) ty) 0 0 tm)
  
  | TmIfThenElse(i, test, tterm, eterm) ->
      interp test >>= fun b -> 
      withFailTerm (TmIfThenElse(i, b, tterm, eterm))
      begin match b with
        | TmPrim(_,PrimTBool(b'))   -> interp (if b' then tterm else eterm)
        | _                         -> fail @@ pp_to_string "**Interpreter** " "If statement expected a Bool but found %a." pp_term b
      end


(* Equivalent to run *)
(* val run_interp : term -> (string * primfun) list -> string *)
let run_interp program prims =
  match interp program (None, None, prims) with
  | (_, Ok (TmPrim(_,PrimTString(s))))  -> s
  | (_, Ok _)       -> interp_error "%s" "Interpreter returned a non-string value"
  | (_, Error s)    -> interp_error "%s" s

