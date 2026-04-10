import Cultivar.SageServer

open Lean Elab Tactic Meta Term IO Process

elab "#diff" s:term " ," n:term : command =>
  Lean.Elab.Command.liftTermElabM do
  let sexpr ← Lean.Elab.Term.elabTerm s none
  let nexpr ← Lean.Elab.Term.elabTerm n none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let stype ← Lean.Meta.inferType sexpr
  let ntype ← Lean.Meta.inferType nexpr
  logInfo stype

  -- s should be a simplicial complex represented as an `AbstractSimplicialComplex`
  -- n should be a Nat, for the specific differential you want
