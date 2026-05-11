import Cultivar.SageServer
import Cultivar.SageEncode
import Cultivar.SimplicialComplex

open Lean Elab Tactic Meta Term IO Process

syntax "#homology" term (", " term)? : command

elab_rules : command
| `(#homology $k:term, $n:term) =>
  Lean.Elab.Command.liftTermElabM do
    let ι ← mkFreshTypeMVar
    let ffcTy ← Lean.Elab.Term.elabType (← `(FiniteFacetComplex _))
    let kExpr ← Lean.Elab.Term.elabTermEnsuringType k ffcTy
    let nExpr ← Lean.Elab.Term.elabTermEnsuringType n (mkConst ``Nat)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let dim ← evalNatSafe nExpr
    let rawExpr ← mkAppM ``FiniteFacetComplex.toRawFacets  #[kExpr]
    let rows    ← evalRawFacetsSafe rawExpr
    let facetsStr := stringListToMatString rows
    let reqJson := Lean.Json.mkObj [
    ("op", Lean.Json.str "homology"),
    ("facets", Lean.Json.str facetsStr),
    ("dim", Lean.Json.num dim),
    ("reduced", Lean.Json.bool false),
    ("base_ring", Lean.Json.str "ZZ")
    ]
    let json ← sendSageRequest reqJson
    let invjson ← IO.ofExcept (json.getObjVal? "invariants")
    logInfo m!"{invjson}"
| `(#homology $k:term) =>
    Lean.Elab.Command.liftTermElabM do
    let ι ← mkFreshTypeMVar
    let ffcTy ← Lean.Elab.Term.elabType (← `(FiniteFacetComplex _))
    let kExpr ← Lean.Elab.Term.elabTermEnsuringType k ffcTy
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let rawExpr ← mkAppM ``FiniteFacetComplex.toRawFacets  #[kExpr]
    let rows    ← evalRawFacetsSafe rawExpr
    let facetsStr := stringListToMatString rows
    let reqJson := Lean.Json.mkObj [
    ("op", Lean.Json.str "homology"),
    ("facets", Lean.Json.str facetsStr),
    ("reduced", Lean.Json.bool false),
    ("base_ring", Lean.Json.str "ZZ")
    ]
    let json ← sendSageRequest reqJson
    logInfo m!"{json}"
