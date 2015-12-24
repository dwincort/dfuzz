open Types

let rec si_simpl (si : si) : si = match si with
  | SiTerm (t) -> (match t with
      | TmPrim(_, PrimTNum(f)) -> SiConst f
      | TmPrim(_, PrimTInt(i)) -> SiConst (float_of_int i)
      | TmPrim(_, PrimTBool(b)) -> if b then SiInfty else SiZero
      | _ -> si)
  | SiAdd (si1, si2)  ->
    let si1' = si_simpl si1 in
    let si2' = si_simpl si2 in
    begin
      match si1', si2' with
      | SiInfty, _            -> SiInfty
      | _, SiInfty            -> SiInfty
      | SiConst x, SiConst y  -> SiConst (x +. y)
      | _, _                  -> SiAdd (si1', si2')
    end
  | SiMult(si1, si2) ->
    let si1' = si_simpl si1 in
    let si2' = si_simpl si2 in
    begin
      match si1', si2' with
      | SiConst 1.0, y        -> y
      | x, SiConst 1.0        -> x
      | SiConst x, SiConst y  -> SiConst (x *. y)
      | _, _                  -> SiMult (si1', si2')
    end
  | SiLub(si1, si2) ->
    let si1' = si_simpl si1 in
    let si2' = si_simpl si2 in
    begin
      match si1', si2' with
      | SiInfty, _            -> SiInfty
      | _, SiInfty            -> SiInfty
      | SiConst x, SiConst y  -> SiConst (if x > y then x else y)
      | _, _                  -> SiLub(si1', si2')
    end
  | SiSucc(sis) ->
    let sis' = si_simpl sis in
    begin
      match sis' with
      | SiZero -> SiConst 1.0
      | SiConst x -> SiConst (x +. 1.0)
      | SiInfty -> SiInfty
      | _ -> SiSucc sis'
    end
  | _ -> si


let check_si_leq (sil : si) (sir : si) : bool =
  match (si_simpl sil), (si_simpl sir) with
    | SiZero, _ -> true
    | SiConst 0.0, _ -> true
    | _, SiInfty -> true
    | SiConst l, SiConst r -> (l <= r)
    | _, _ -> sil = sir

