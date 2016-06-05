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

let pp_term = limit_boxes pp_term



(* State monad for the context for interpreting *)
module InterpMonad = struct
  open Ctx
  open Composedp
    
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
    | SiZero          -> return @@ si
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
  
  let onPFail (todo : term interpreter) (m : term interpreter) : term interpreter = 
    fun ((_, pe, plst) as inp) -> match m inp with
      | (_, Ok _) as res -> res
      | (db, Error s) as res -> if Option.is_some pe
        then begin
          interp_messageNoFi 4 "--- Skipping failure \"%s\"; Performing failure operation..." s;
          todo (db, pe, plst)
        end else res
  
  let withFailTerm (tm : term) (m : term interpreter) : term interpreter = 
    fun ((_, pe, _) as inp) -> match m inp with
      | (_, Ok _) as res -> res
      | (db, Error s) as res -> if Option.is_some pe
        then begin
          interp_messageNoFi 4 "--- Skipping failure \"%s\";@ reverting to state %a." s pp_term tm;
          (db, Ok tm)
        end else res
  
  let inPartial (m : 'a interpreter) : 'a interpreter = 
    fun (db, _, plst) -> m (db, Some (Ctx.empty_context, false), plst)
  
  let isInPartial : bool interpreter = 
    fun (db, pe, _) -> (db, Ok (Option.is_some pe))
  
  let underBranchPartial (m : 'a interpreter) : 'a interpreter = 
    fun (db, pe, plst) -> m (db, Option.map (fun (ctx,_) -> (ctx,true)) pe, plst)
  
  let isUnderBranchPartial : bool interpreter = 
    fun (db, pe, _) -> (db, Ok (Option.map_default (fun (_,u) -> u) false pe))
  
  let withExtendedPContext (v : string) (ty : ty) (m : 'a interpreter) : 'a interpreter =
    fun (db, pe, plst) -> m (db, Option.map (fun (c,u) -> (Ctx.extend_ctx_with_var' v ty c, u)) pe, plst)
  
  let getPContext : context interpreter =
    fun (db, pe, _) -> (db, Ok (Option.map_default fst Ctx.empty_context pe))
  
  let attemptRedZone (sens : epsilon) : bool interpreter =
    fun (db, _, _) -> match db with
      | None -> (db, Error "**Interpreter** Tried to store a sensitivity when no DB was loaded")
      | Some (db, ((ebudget,dbudget) as budget), _, silist) -> 
          let silist' = (sens, 0.0) :: silist           in
          let (e,d) = minEDWithinBudget budget silist'  in
          let eRemain = max 0.0 (ebudget -. e)          in
          let dRemain = max 0.0 (dbudget -. d)          in
          (Some (db, budget, (eRemain,dRemain), silist'), Ok (e <= ebudget && d <= dbudget))
  
  let getDB : term interpreter = 
    fun (o, _, _) -> match o with
      | None -> (o, Error "**Interpreter** No database loaded")
      | Some (db,_,_,_) -> (o, Ok db)
  
  let storeDB (db : term) (budget : ed) : unit interpreter = 
    fun (db_init, pe, _) -> if Option.is_some pe
      then begin interp_messageNoFi 1 "Trying to storeDB in red zone.  Quietly skipping ...";
                 (db_init, Ok ())
      end else (Some (db, budget, budget, []), Ok ())
  
  let getDelta : float interpreter = 
    fun (db, _, _) -> match db with
      | None -> (db, Error "**Interpreter** Tried to get remaining epsilon budget when no DB was loaded")
      | Some (_, _, (_, del), _) -> (db, Ok del)
  
  let getEpsilon : epsilon interpreter = 
    fun (db, _, _) -> match db with
      | None -> (db, Error "**Interpreter** Tried to get remaining epsilon budget when no DB was loaded")
      | Some (_, _, (eps, _), _) -> (db, Ok eps)
  
  let getPrimDefs : ((string * primfun) list) interpreter = 
    fun (db, _, plst) -> (db, Ok plst)
  
  let lookup_prim (id : string) : (ty * term list -> term interpreter) interpreter =
    let rec lookup l = match l with
      | []                    -> fail ("**Interpreter** Primitive "^id^" not found")
      | (s, PrimFun t) :: l'  -> if s = id then return t else lookup l'
    in getPrimDefs >>= lookup
    
  let checkerToInterpreter (c : 'a Tycheck.TypeCheckMonad.checker) : 'a interpreter = 
    getPContext >>= fun ctx ->
    Tycheck.ty_seq := 0;
    match c (ctx, false) with 
      | Error e -> fail @@ pp_to_string "TYPE FAIL: " "%a %a" Support.FileInfo.pp_fileinfo e.Support.FileInfo.i 
                                                              Tycheck.pp_tyerr e.Support.FileInfo.v
      | Ok res -> return res

end

open InterpMonad

  

(* This function does some simple type inference.
   We expect the term f to be an abstraction with one free type variable, 
   and we return a term with that variable filled in such that the argument 
   is now applicable to the abstraction.
   Note that for this simple version, we demand that f be a value 
   abstraction (NOT a type abstraction) and that its argument must fully 
   determine the type variable immediately. *)
let appTypeInfer (f : term) (arg : term) : term interpreter = 
  checkerToInterpreter (Tycheck.type_of arg) >>= fun (ty_arg,_) ->
  match f with
  | TmAbs(_,_,(_,expectedTy),_,tm) -> begin match expectedTy, ty_arg with
      | TyVar v, _ -> if v.v_index = 0 then return (tm_substTy ty_arg 0 0 f)
                      else fail "**Interpreter** Bad type inference"
      | TyPrim1 (t, TyVar v), TyPrim1 (t', ty_arg') ->
            if v.v_index = 0 && t' = t then return (tm_substTy ty_arg' 0 0 f)
                      else fail "**Interpreter** Bad type inference"
      | _,_ -> fail "**Interpreter** Bad type inference"
      end
  | _ -> fail "**Interpreter** Bad type inference"


(* val interp : term -> value interpreter *)
let rec interp t = 
  isInPartial >>= fun partial ->
  (if partial then interp_debug3 (tmInfo t) "--> Enter interp of: @[%10a@]" pp_term t);
  withFailTerm t (match t with
  (* A primitive term is fully evaluated.  Do nothing. *)
  | TmPrim(i,pt) -> return t
  
  (* When we come to a primitive function, we have a list of terms (and their 
     types) that are the arguments.  If all of these arguments are values 
     (as should be the case all the time in regular evaluation), then we 
     look up and execute the primitive with its arguments.  However, if we 
     are in partial evaluation mode, they may not all be values, in which 
     case, we fail, but we deeply evaluate (go under lambdas) the arguments 
     to make sure all function arguments are partially evaluated. *)
  | TmPrimFun(i, s, ty, ttslst)  ->
      mapM (fun (tm,ty,si,b) -> interp tm >>= fun tm -> 
                                return (tm,ty,si,b)) ttslst >>= fun ttslst ->
      let tmlst = List.map (fun (tm,_,_,_) -> tm) ttslst in
      if List.for_all tmIsVal tmlst then
        lookup_prim s >>= fun f -> 
        f (ty, tmlst)
      else 
        isInPartial >>= fun partial ->
        if partial then
          mapM (fun (tm,ty,si,b) -> if b then return (tm,ty,si,b)
                                    else (goDeepUnderLambda tm >>= fun tm -> 
                                          mapMTy interp ty >>= fun ty -> 
                                          mapMSi interp si >>= fun si ->
                                          return (tm,ty,si,true))
          ) ttslst >>= fun ttslst ->
          return @@ TmPrimFun(i, s, ty, ttslst)
        else fail @@ pp_to_string "**Interpreter** " "Unevaluated arguments in %a." pp_term t
  
  (* Variables always fail (which will get caught during partial evaluation). *)
  | TmVar(i,v) -> fail @@ "**Interpreter** Unexpected var: "^v.v_name
  
  (* Bags are essentially primitives. *)
  (* There are certain cases where bags can have unevaluated terms in them.  Realistically, 
     this should be addressed so that it cannot happen, but an easy (although expensive 
     performance-wise) fix would be to interp each element of a bag whenever we see one. *)
  | TmBag(_,_,_) -> return t
  | TmVector(i,ty,tmlst) -> mapM interp tmlst >>= fun tmlst -> return (TmVector(i, ty, tmlst))
  
  (* Pairs.  Interpret both parts and return them as a pair. *)
  | TmPair(i,t1,t2) -> 
      interp t1 >>= fun t1' ->
      interp t2 >>= fun t2' ->
      return @@ TmPair (i, t1', t2')
  
  (* Tensor Desctruction.  Interpret the argument expression.  If it is a 
     pair, substitute its constituent values for the variables in the body 
     and interpret that.  If not, fail.  However, if we are in partial mode, 
     first interpret the body (without and substitutions). *)
  | TmTensDest(i, b1, b2, tm, tBody) ->
      interp tm >>= fun tm -> 
      (*withFailTerm (TmTensDest(i, b1, b2, tm, tBody))*)
      begin match tm with
        | TmPair (i', t1, t2) -> interp (tm_substTm t1 0 0 (tm_substTm t2 0 0 tBody))
        | _ -> isInPartial >>= fun partial ->
               if partial then begin
(*                  interp_debug3 i "%s" "--- Doing type checking to extend ctx for TensDest"; *)
                 checkerToInterpreter (Tycheck.type_of tm) >>= fun (ty,_) ->
                 checkerToInterpreter (Tycheck.TypeSub.check_tensor_shape (tmInfo tm) ty) >>= fun (ty1, ty2) ->
                 withExtendedPContext b1.b_name ty1 (withExtendedPContext b2.b_name ty2
                    (interp tBody)) >>= fun tBody -> 
                 return @@ TmTensDest(i, b1, b2, tm, tBody)
               end else
                 fail @@ pp_to_string "**Interpreter** " "TensDest expected a pair but found %a." pp_term tm
      end
  
  (* & constructor.  Interpret both parts and return them as a pair. *)
  | TmAmpersand(i, t1, t2) ->
      interp t1 >>= fun t1' ->
      interp t2 >>= fun t2' ->
      return @@ TmAmpersand (i, t1', t2')
  
  (* Left and Right constructors for sum.  Interpret the body. *)
  | TmLeft (i, t, ty)   -> interp t >>= fun t -> return (TmLeft (i, t, ty))
  | TmRight(i, t, ty)   -> interp t >>= fun t -> return (TmRight(i, t, ty))
  
  (* Interpret the scrutinee.  If it is a Left or Right value, do the proper 
     substitution into the body and interpret that.  Otherwise, fail.  If we 
     are in partial mode, interpret both branches, but do so in under-branch 
     mode (in which we do not unfold terms or make recursive calls. *)
  | TmUnionCase(i, tm, bl, tlBody, br, trBody) ->
      interp tm >>= fun tm -> 
      (*interp_debug3 i "--- Interpreting a union of: %a" pp_term tm;*)
      begin match tm with
        | TmLeft (i',tl,_) -> interp (tm_substTm tl 0 0 tlBody)
        | TmRight(i',tr,_) -> interp (tm_substTm tr 0 0 trBody)
        | _ -> isInPartial >>= fun partial ->
               if partial then 
                 (underBranchPartial 
                  ((*interp_debug3 i "%s" "--- Doing type checking to extend ctx for union";*)
                   checkerToInterpreter (Tycheck.type_of tm) >>= fun (ty,_) ->
                   checkerToInterpreter (Tycheck.TypeSub.check_union_shape (tmInfo tm) ty) >>= fun (tyl, tyr) ->
                   (*interp_debug3 i "%s" "--- Got the right shape";*)
                   withExtendedPContext bl.b_name tyl (interp tlBody) >>= fun tlBody -> 
                   withExtendedPContext br.b_name tyr (interp trBody) >>= fun trBody -> 
                   return @@ TmUnionCase(i, tm, bl, tlBody, br, trBody)))
               else
                 fail @@ pp_to_string "**Interpreter** " "Union expected a sum value but found %a" pp_term tm
      end

  (* Function Application.  Interpret the argument and then the function 
     in standard strict style.  Then, match the function.  If it is an 
     abstraction, perform the substitution.  However, take care when 
     performing because, if we are in partial evaluation mode, the argument 
     may not be *really* fully evaluated, and any variables therein need 
     their indexes properly updated.
     If it is a type abstraction, then we are in a position where type 
     inference needs to be performed.  This is kind of hacky right now 
     (because type inference itself is a bit of a hack).
     Otherwise, fail. *)
  | TmApp(i, tf, ta) -> 
      interp ta >>= fun ta ->
      interp tf >>= fun tf ->
      onPFail (return @@ TmApp(i, tf, ta))
      begin match tf with
      | TmAbs(_,_,_,_,tm)   -> interp (tm_substTm ta 0 0 tm) 
      | TmTyAbs(i', bi, tm) -> onPFail (goUnderLambda tm >>= fun tm -> return (TmApp(i, TmTyAbs(i, bi, tm), ta)))
                               (appTypeInfer tm ta >>= fun tm -> interp (TmApp(i, tm, ta)))
      | _ ->    fail @@ pp_to_string "**Interpreter** " "Application expected a Lambda value but found %a." pp_term tf
      end
  
  (* Abstractions are values, but because there may be terms in their 
     types or sensitivity annotations, we do interpret those. *)
  | TmAbs(i, bi, (si, ty), tyo, tm) -> 
    mapMSi interp si >>= fun si ->
    mapMTy interp ty >>= fun ty ->
    (match tyo with
      | None -> return None
      | Some t -> mapMTy interp t >>= fun x -> return (Some x)
    ) >>= fun tyo ->
    return @@ TmAbs(i, bi, (si, ty), tyo, tm)

  (* Recursive data types.  
     Always interpret under a fold.
     For unfolds, if we are in under-branch mode, then simply do not 
     look at the underlying term or expand.  In all other cases, 
     interpret the underlying term and expand. *)
  | TmFold(i, ty, tm) ->
    interp tm >>= fun tm -> 
    return @@ TmFold(i, ty, tm)
  | TmUnfold(i, tm)   ->
    isUnderBranchPartial >>= fun underBranch ->
    if underBranch then
      (interp_debug3 i "%s" "--- Not diving into an unfold.";
      return t)
    else
      interp tm >>= fun tm -> 
      begin match tm with 
      | TmFold(_,_,tm') -> return tm'
      | _ -> fail @@ pp_to_string "**Interpreter** " "Tried to unfold a non-folded term: %a" pp_term t
      end

  (* Bindings should always be propagated, but just like with 
     substitutions in abstractions, care needs to be taken to 
     deal with unevaluated terms due to partial evaluation. *)
  | TmLet(i, b, si, tm, tBody) ->
      interp tm >>= fun tm -> 
      interp (tm_substTm tm 0 0 tBody)
  
  (* Statement bodies can be evaluated during partial evaluation, but the
     statement itself should not be removed. *)
  | TmStmt(i, tm1, tm2) ->
      interp tm1 >>= fun tm1 -> 
      interp tm2 >>= fun tm2 ->
      isInPartial >>= fun partial ->
      if partial then
        return @@ TmStmt(i, tm1, tm2)
      else
        return tm2
  
  (* A recursive function should always be expanded except if we are in 
     the case where we are both in under-branch mode and this is a 
     recursive call.  To expand, substitute this recfun itself into 
     itself (but setting that it is now internally a recursive call). *)
  | TmRecFun(i, bi, ty, tm, isRec) ->
      isUnderBranchPartial >>= fun underBranch ->
      if underBranch && isRec then
        withExtendedPContext bi.b_name ty (goDeepUnderLambda tm) >>= fun tm ->
        return @@ TmRecFun (i, bi, ty, tm, isRec)
      else
        let tm = tm_substTm (TmRecFun(i, bi, ty, tm, true)) 0 0 tm in
        interp tm
  
  (* Sample is the bind of our probability monad.  No probability monadic 
     operations can be performed during partial evaluation, so if we 
     find we are in partial evaluation mode, we interpret the the sampled 
     expression and the body and then return a TmSample of those.  In 
     regular evaluation, this is treated exactly as a let. *)
  | TmSample(i, b, tm, tBody) ->
    (* Do not interpret sample during partial application *)
    isInPartial >>= fun partial ->
    if partial then begin
      interp tm >>= fun tm ->
      (*interp_debug3 i "%s" "--- Doing type checking to extend ctx for sample";*)
      checkerToInterpreter (Tycheck.type_of tm) >>= fun (ty,_) ->
      checkerToInterpreter (Tycheck.TypeSub.check_fuzz_shape (tmInfo tm) ty) >>= fun ty' ->
      withExtendedPContext b.b_name ty' (interp tBody) >>= fun tBody ->
      return @@ TmSample(i, b, tm, tBody)
      end
    else interp tm >>= fun tm -> interp (tm_substTm tm 0 0 tBody)

  (* Type Abstraction and Applicacion.  In a regular evaluator, these 
     could be resolved as no-ops, but because of partial evaluation and 
     a potential for mid-execution type checking, these need to be 
     properly resolved.  Type abstractions are just abstractions and 
     remain as values.  Type application performs the type substitution 
     (or fails). *)
  | TmTyAbs(_, _, _) -> return t
  | TmTyApp(i, tm, ty) ->
      interp tm >>= fun tm ->
      withFailTerm (TmTyApp(i, tm, ty))
      begin if not (tyIsVal ty)
        then fail @@ pp_to_string "**Interpreter** " "Type Application expected a fully evaluated type but found %a." pp_type ty
        else begin match tm with
        | TmTyAbs(i', bi, tm')  -> interp (tm_substTy ty 0 0 tm')
        | _ -> fail @@ pp_to_string "**Interpreter** " "Type Application expected a TyLambda but found %a." pp_term tm
        end
      end

  (* Similar to type abstraction and application, this could be a no-op 
     if not for the potiential for mid-execution type checking.  Instead, 
     we perform a type substition just as we would in the type checker. *)
  | TmTypedef(i,b,ty,tm) -> 
    interp(tm_substTy (ty_shiftTy 0 (-1) ty) 0 0 tm)
  
  (* IfThenElse terms are just a special syntax case of case expressions. *)
  | TmIfThenElse(i, test, tterm, eterm) ->
      interp test >>= fun b -> 
      withFailTerm (TmIfThenElse(i, b, tterm, eterm))
      begin match b with
        | TmPrim(_,PrimTBool(b'))   -> interp (if b' then tterm else eterm)
        | _ -> isInPartial >>= fun partial ->
               if partial then underBranchPartial 
                 (interp tterm >>= fun tterm -> 
                  interp eterm >>= fun eterm -> 
                  return @@ TmIfThenElse(i, b, tterm, eterm))
               else
                 fail @@ pp_to_string "**Interpreter** " "If statement expected a Bool but found %a." pp_term b
      end
  
  ) >>= fun res ->
  (if partial then interp_debug3 (tmInfo t) "--> Exit  interp of: @[%a@]@ ------- with result: @[%a@]" pp_term t pp_term res);
  return res

(* This function interprets a lambda expression in the particular case 
   where we would like to interpret its body. *)
and goUnderLambda (t : term) : term interpreter = match t with
  | TmAbs(i, bi, (si, ty), tyo, tm) -> 
      interp_debug3 i "%s" "--- Interpreter: Going under a lambda.";
      mapMSi interp si >>= fun si ->
      mapMTy interp ty >>= fun ty ->
      (match tyo with
        | None -> return None
        | Some t -> mapMTy interp t >>= fun x -> return (Some x)
      ) >>= fun tyo ->
      withExtendedPContext bi.b_name ty (interp tm) >>= fun tm ->
      let result = TmAbs(i, bi, (si, ty), tyo, tm) in
      interp_debug3 i "--- Interpreter: Exiting a lambda. Now at: %a" pp_term result;
      return result
  | _ -> return t

(* This is a version of goUnderLambda that will keep going under lambdas 
   until it finds a body that is not itself an abstraction.
   FIXME: This won't cover all cases, so I'm really not sure if it's even 
          worth having. *)
and goDeepUnderLambda (t : term) : term interpreter = match t with
  | TmAbs(i, bi, (si, ty), tyo, tm) -> 
      interp_debug3 i "%s" "--- Interpreter: Going under a lambda.";
      mapMSi interp si >>= fun si ->
      mapMTy interp ty >>= fun ty ->
      (match tyo with
        | None -> return None
        | Some t -> mapMTy interp t >>= fun x -> return (Some x)
      ) >>= fun tyo ->
      withExtendedPContext bi.b_name ty (goDeepUnderLambda tm) >>= fun tm ->
      let result = TmAbs(i, bi, (si, ty), tyo, tm) in
      interp_debug3 i "--- Interpreter: Exiting a lambda. Now at: %a" pp_term result;
      return result
  | TmTyAbs(i, bi, tm) ->
      goDeepUnderLambda tm >>= fun tm ->
      return @@ TmTyAbs(i, bi, tm)
  | _ -> interp t


(* Runs a program.  It takes the program to run as well as a list of 
   (name * primitive function) pairs providing the behaviors of any 
   primitive functions. The progam must output a string in the end, 
   and this will provide that string. *)
let run_interp (program : term) (prims : (string * primfun) list) : string =
  match interp program (None, None, prims) with
  | (_, Ok (TmPrim(_,PrimTString(s))))  -> s
  | (_, Ok _)       -> interp_error "%s" "Interpreter returned a non-string value"
  | (_, Error s)    -> interp_error "%s" s

