import Cultivar.SageServer
import Cultivar.SageEncode
import Cultivar.SageDecode
import Cultivar.SimplicialComplex
import Cultivar.Boundary.Verify

open Lean Elab Tactic Meta Term IO Process
open Cultivar.SageDecode

unsafe def evalRawFacets (ffcExpr : Expr) : MetaM (List (List Nat)) := do
  let callExpr ← mkAppM ``FiniteFacetComplex.toRawFacets #[ffcExpr]
  let tyExpr ← mkAppM ``List #[← mkAppM ``List #[mkConst ``Nat]]
  Lean.Meta.evalExpr (List (List Nat)) tyExpr callExpr

@[implemented_by evalRawFacets]
opaque evalRawFacetsSafe (ffcExpr : Expr) : MetaM (List (List Nat))

private def formatNatRow (row : List Nat) : String :=
  "[" ++ ", ".intercalate (row.map toString) ++ "]"

private def formatIntRow (row : List Int) : String :=
  "[" ++ ", ".intercalate (row.map toString) ++ "]"

private def formatNatMatrix (rows : List (List Nat)) : String :=
  String.intercalate "\n" (rows.map formatNatRow)

private def formatIntMatrix (rows : List (List Int)) : String :=
  String.intercalate "\n" (rows.map formatIntRow)

private def logBoundaryData (n : Nat) (dom cod : List (List Nat)) (d : List (List Int)) :
    MetaM Unit := do
  logInfo m!"∂_{n} : C_{n} → C_{n - 1}"
  logInfo m!"domain basis (columns):\n{formatNatMatrix dom}"
  logInfo m!"codomain basis (rows):\n{formatNatMatrix cod}"
  logInfo m!"matrix:\n{formatIntMatrix d}"

def fetchBoundaryData (ffcExpr nExpr : Expr) :
    MetaM (Nat × List (List Nat) × List (List Nat) × List (List Int)) := do
    let stype ← inferType ffcExpr
    let (``FiniteFacetComplex, #[_ιExpr]) := stype.getAppFnArgs
    | throwError "expected FiniteFacetComplex type, got {stype}"
    let n ← evalNatSafe nExpr
    let facets ← evalRawFacetsSafe ffcExpr
    logInfo m!"n = {n}, facets = {facets}"
    let req : Json := Json.mkObj [
      ("op", toJson "boundary"),
      ("facets", toJson facets),
      ("n", toJson n)
    ]
    let json ← sendSageRequest req
    let domJson ← IO.ofExcept (json.getObjVal? "domain_basis")
    let dJson ← IO.ofExcept (json.getObjVal? "d")
    let codJson ← IO.ofExcept (json.getObjVal? "codomain_basis")
    let dom ← decodeNatMatrix domJson
    let cod ← decodeNatMatrix codJson
    let d ← decodeIntMatrix dJson
    pure (n, dom, cod, d)

unsafe def evalBoundaryCheck
    (ffcExpr nExpr : Expr)
    (dom cod : List (List Nat))
    (d : List (List Int)) : MetaM Bool := do
  let okExpr ← mkAppM ``verifyBoundaryDataB #[ffcExpr, nExpr, toExpr dom, toExpr cod, toExpr d]
  Lean.Meta.evalExpr Bool (mkConst ``Bool) okExpr

@[implemented_by evalBoundaryCheck]
opaque evalBoundaryCheckSafe
    (ffcExpr nExpr : Expr)
    (dom cod : List (List Nat))
    (d : List (List Int)) : MetaM Bool

unsafe def evalBoundaryDiagnostics
    (ffcExpr nExpr : Expr)
    (dom cod : List (List Nat))
    (d : List (List Int)) : MetaM (Bool × Bool × Bool) := do
  let domExpr ← mkAppM ``validDomainBasisB #[ffcExpr, nExpr, toExpr dom]
  let codExpr ← mkAppM ``validCodomainBasisB #[ffcExpr, nExpr, toExpr cod]
  let coreExpr ← mkAppM ``verifyBoundaryDataCoreB #[toExpr dom, toExpr cod, toExpr d]
  let domOK ← Lean.Meta.evalExpr Bool (mkConst ``Bool) domExpr
  let codOK ← Lean.Meta.evalExpr Bool (mkConst ``Bool) codExpr
  let coreOK ← Lean.Meta.evalExpr Bool (mkConst ``Bool) coreExpr
  pure (domOK, codOK, coreOK)

@[implemented_by evalBoundaryDiagnostics]
opaque evalBoundaryDiagnosticsSafe
    (ffcExpr nExpr : Expr)
    (dom cod : List (List Nat))
    (d : List (List Int)) : MetaM (Bool × Bool × Bool)

unsafe def evalFirstMismatch
    (dom cod : List (List Nat))
    (d : List (List Int)) : MetaM (Option BoundaryMismatch) := do
  let mismatchExpr ← mkAppM ``firstMismatch #[toExpr dom, toExpr cod, toExpr d]
  let mismatchTy ← mkAppM ``Option #[mkConst ``BoundaryMismatch]
  Lean.Meta.evalExpr (Option BoundaryMismatch) mismatchTy mismatchExpr

@[implemented_by evalFirstMismatch]
opaque evalFirstMismatchSafe
    (dom cod : List (List Nat))
    (d : List (List Int)) : MetaM (Option BoundaryMismatch)

elab "#diff" s:term "," n:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let sExpr ← Lean.Elab.Term.elabTerm s none
    let nExpr ← Lean.Elab.Term.elabTerm n (some (mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let (k, dom, cod, d) ← fetchBoundaryData sExpr nExpr
    logBoundaryData k dom cod d

elab "#boundary_check" m:term "," n:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let mExpr ← Lean.Elab.Term.elabTerm m none
    let nExpr ← Lean.Elab.Term.elabTerm n (some (mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let (_k, dom, cod, d) ← fetchBoundaryData mExpr nExpr
    let ok ← evalBoundaryCheckSafe mExpr nExpr dom cod d
    if ok then
      logInfo "boundary check: PASS"
    else
      let (domOK, codOK, coreOK) ← evalBoundaryDiagnosticsSafe mExpr nExpr dom cod d
      logInfo m!"boundary check: FAIL (domOK={domOK}, codOK={codOK}, coreOK={coreOK})"
      let mismatch ← evalFirstMismatchSafe dom cod d
      match mismatch with
      | some mm =>
          logInfo m!"entry mismatch at (row={mm.i}, col={mm.j})"
          logInfo m!"actual={mm.actual}, expected={mm.expected}"
          logInfo m!"tau(row simplex)={mm.τ}, sigma(col simplex)={mm.σ}"
      | none =>
          logInfo "no entry mismatch found (likely basis and/or shape issue)"

elab "#boundary_goal" s:term "," n:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let sExpr ← Lean.Elab.Term.elabTerm s none
    let nExpr ← Lean.Elab.Term.elabTerm n (some (mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let (_k, dom, cod, d) ← fetchBoundaryData sExpr nExpr
    let goalExpr ← mkAppM ``verifyBoundaryData #[sExpr, nExpr, toExpr dom, toExpr cod, toExpr d]
    logInfo m!"goal: {goalExpr}"
