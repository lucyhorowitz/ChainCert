import Cultivar.SageServer
import Cultivar.SimplicialComplex

open Lean Elab Tactic Meta Term IO Process

unsafe def evalRawFacets (ffcExpr : Expr) : MetaM (List (List Nat)) := do
  let callExpr ← mkAppM ``FiniteFacetComplex.toRawFacets #[ffcExpr]
  let tyExpr ← mkAppM ``List #[← mkAppM ``List #[mkConst ``Nat]]
  Lean.Meta.evalExpr (List (List Nat)) tyExpr callExpr

@[implemented_by evalRawFacets]
opaque evalRawFacetsSafe (ffcExpr : Expr) : MetaM (List (List Nat))

unsafe def evalNatExpr (e : Expr) : MetaM Nat :=
  Lean.Meta.evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatExpr]
opaque evalNatSafe (e : Expr) : MetaM Nat

elab "#diff" s:term "," n:term : command =>
  Lean.Elab.Command.liftTermElabM do
  let sexpr ← Lean.Elab.Term.elabTerm s none
  let nexpr ← Lean.Elab.Term.elabTerm n (some (mkConst ``Nat))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let stype ← Lean.Meta.inferType sexpr
  let (``FiniteFacetComplex, #[_ιExpr]) := stype.getAppFnArgs
  | throwError "expected FiniteFacetComplex type, got {stype}"
  let n ← evalNatSafe nexpr
  let facets ← evalRawFacetsSafe sexpr
  logInfo m!"n = {n}, facets = {facets}"
  let req : Json := Json.mkObj [
    ("op", toJson "boundary"),
    ("facets", toJson facets),
    ("n", toJson n)
  ]
  let json ← sendSageRequest req
  let status ← IO.ofExcept (json.getObjVal? "status")
  let dom ← IO.ofExcept (json.getObjVal? "domain_basis")
  let d ← IO.ofExcept (json.getObjVal? "d")
  let cod ← IO.ofExcept (json.getObjVal? "codomain_basis")

  -- s should be a FiniteFacetComplex ι; n : Nat is the dimension of the
  -- differential you want
