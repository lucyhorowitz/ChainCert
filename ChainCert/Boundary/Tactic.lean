import ChainCert.Boundary.Verify
import Lean.Elab.Tactic
import ChainCert.Boundary.Boundary

open Lean Elab Tactic Meta Term IO Process

unsafe def evalMatNat (ty e : Expr) : MetaM (List (List Nat)) :=
    Lean.Meta.evalExpr (List (List Nat)) ty e

@[implemented_by evalMatNat]
  opaque evalMatNatSafe (ty e : Expr) : MetaM (List (List Nat))

unsafe def evalMatInt (ty e : Expr) : MetaM (List (List Int)) :=
    Lean.Meta.evalExpr (List (List Int)) ty e

@[implemented_by evalMatInt]
  opaque evalMatIntSafe (ty e : Expr) : MetaM (List (List Int))

elab "boundary_verify" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  match target.getAppFnArgs with
  | (``verifyBoundaryData, #[_ι, _inst1, _inst2, _inst3, _F, _k, _dom, _cod, _d]) =>
    let natMatTy ← mkAppM ``List #[← mkAppM ``List #[mkConst ``Nat]]
    let intMatTy ← mkAppM ``List #[← mkAppM ``List #[mkConst ``Int]]
    let dom ← evalMatNatSafe natMatTy _dom
    let cod ← evalMatNatSafe natMatTy _cod
    let d   ← evalMatIntSafe intMatTy _d
    let ok  ← evalBoundaryCheckSafe _F _k dom cod d
    if ok then
      evalTactic (← `(tactic| native_decide))
    else
      let (domOK, codOK, coreOK) ← evalBoundaryDiagnosticsSafe _F _k dom cod d
      logInfo m!"boundary check: FAIL (domOK={domOK}, codOK={codOK}, coreOK={coreOK})"
      let mismatch ← evalFirstMismatchSafe dom cod d
      match mismatch with
      | some mm =>
          throwError m!"entry mismatch at (row={mm.i}, col={mm.j})"
          throwError m!"actual={mm.actual}, expected={mm.expected}"
          throwError m!"tau(row simplex)={mm.τ}, sigma(col simplex)={mm.σ}"
      | none =>
          throwError "no entry mismatch found (likely basis and/or shape issue)"
  | _ => throwError "boundary_verify: goal is not `verifyBoundaryData ...`"
