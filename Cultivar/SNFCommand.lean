import Cultivar.SageServer

open Lean Elab Tactic Meta Term IO Process

elab "#snf" t:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let expr ← Lean.Elab.Term.elabTerm t none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let type ← Lean.Meta.inferType expr
    let (``Matrix, #[finM, finN, _R]) := type.getAppFnArgs
      | throwError "expected Matrix type, got {type}"
    let (``Fin, #[mExpr]) := finM.getAppFnArgs
      | throwError "expected Fin m, got {finM}"
    let (``Fin, #[nExpr]) := finN.getAppFnArgs
      | throwError "expected Fin n, got {finN}"
    let mExpr ← Lean.Meta.whnf mExpr
    let nExpr ← Lean.Meta.whnf nExpr
    let some m := mExpr.rawNatLit?
      | throwError "expected nat literal for m"
    let some n := nExpr.rawNatLit?
      | throwError "expected nat literal for n"
    let finMType ← mkAppM ``Fin #[mkRawNatLit m]
    let finNType ← mkAppM ``Fin #[mkRawNatLit n]
    let mut rows : List (List String) := []
    for i in List.range m do
      let mut row : List String := []
      for j in List.range n do
        let iExpr ← Lean.Meta.mkNumeral finMType i
        let jExpr ← Lean.Meta.mkNumeral finNType j
        let entry := mkApp2 expr iExpr jExpr
        let s ← evalSageStringSafe entry
        row := row ++ [s]
      rows := rows ++ [row]
    let str := stringListToMatString rows
    let reqJson := Lean.Json.mkObj [
      ("op", Lean.Json.str "snf"),
      ("matrix", Lean.Json.str str)
    ]
    let json ← sendSageRequest reqJson
    let uJson ← IO.ofExcept (json.getObjVal? "U")
    let uinvJson ← IO.ofExcept (json.getObjVal? "Uinv")
    let dJson ← IO.ofExcept (json.getObjVal? "D")
    let vJson ← IO.ofExcept (json.getObjVal? "V")
    let vinvJson ← IO.ofExcept (json.getObjVal? "Vinv")
    logInfo m!"U = {uJson}\n\
                 Uinv = {uinvJson}\n\
                 D = {dJson}\n\
                 V = {vJson}\n\
                 Vinv = {vinvJson}"
