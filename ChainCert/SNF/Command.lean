import ChainCert.SageServer
import ChainCert.SageEncode

open Lean Elab Tactic Meta Term IO Process

unsafe def evalNatUnsafe (e : Expr) : MetaM Nat :=
    Lean.Meta.evalExpr Nat (.const ``Nat []) e

@[implemented_by evalNatUnsafe]
opaque evalNat (e : Expr) : MetaM Nat

elab "#snf" t:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let expr ← Lean.Elab.Term.elabTerm t none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let rows ← evalMatStringListSafe expr
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
