import Cultivar.SNF.Core
import Cultivar.SNF.Verify
import Cultivar.SNF.Rank
import Cultivar.SageServer
import Cultivar.SageEncode
import Cultivar.SageDecode
import Lean.Elab.Tactic
import Lean


/-! Plan for `snf` tactic UX and behavior.

Two tactics, sharing all internals (Sage call + Lean-side verification + term
construction) and differing only in the final step:

- `snf A` — workhorse, goal-agnostic. Asserts `cert : CertificateSNF A` into
  the local context. Primary driver inside real proofs.
- `verify_snf` — closes a goal of shape `CertificateSNF A`. Niche. Uses
  `MVarId.assign` instead of `MVarId.assert` at the end.

The rest of this comment describes `snf A`.

`snf A` is goal-agnostic: it can be run regardless of the current goal,
and should enrich the local context with certified SNF data for a concrete matrix `A`.

## Preconditions
- `A` should be actual evaluable matrix data (not a fully symbolic matrix variable).
- Matrix dimensions may be non-literal (e.g. `Fin (cellCount F k)`); the tactic
  routes through compiled-code evaluation (`evalMatStringListSafe`) so nothing
  requires the `Fin` arg to reduce in the kernel.
- Matrix entries must be recoverable at elaboration time via `SageSerializable`.

## Core workflow
1. Extract `(finM, finN, R)` Exprs from A's type (no `rawNatLit?`).
2. Run `matStringList A` via `evalMatStringListSafe` to get a `List (List String)`.
3. Send to Sage; decode `U`, `Uinv`, `D`, `V`, `Vinv` JSON.
4. Build U/V/etc. matrix Exprs reusing A's original dim Exprs (so the built
   `D : Matrix finM finN R` type matches A's type syntactically).
5. Construct `CertificateSNF A` term; proof fields default to `native_decide`.
6. Assert `cert : CertificateSNF A` into the goal context. -/

open Lean Elab Tactic Meta Expr

private structure SnfSageJsonPayload where
  U : Lean.Json
  Uinv : Lean.Json
  D : Lean.Json
  V : Lean.Json
  Vinv : Lean.Json

/-- Extract `(finM, finN, mExpr, nExpr, R)` from the type of `AExpr : Matrix (Fin m) (Fin n) R`.
`mExpr`/`nExpr` are the natural-valued Exprs inside the `Fin _` applications; they
need *not* reduce to concrete Nat literals. -/
private def ensureSnfInput (AExpr : Expr) :
    TacticM (Expr × Expr × Expr × Expr × Expr) := do
  let AType ← inferType AExpr
  let (``Matrix, #[finM, finN, R]) := AType.getAppFnArgs
    | throwError "snf: expected `Matrix (Fin m) (Fin n) R`, got {AType}"

  let (``Fin, #[mExpr]) := finM.getAppFnArgs
    | throwError "snf: expected row index type `Fin m`, got {finM}"
  let (``Fin, #[nExpr]) := finN.getAppFnArgs
    | throwError "snf: expected col index type `Fin n`, got {finN}"

  if AExpr.hasMVar then
    throwError "snf: matrix must be concrete/closed (contains metavariables)"

  let sageSerializableTy ← mkAppM ``SageSerializable #[R]
  let _inst ← synthInstance sageSerializableTy

  pure (finM, finN, mExpr, nExpr, R)

private def certTypeFor (AExpr : Expr) : MetaM Expr :=
  mkAppM ``CertificateSNF #[AExpr]

/-- Assert `certName : CertificateSNF AExpr := certExpr` into the main goal context,
returning the new goal mvar. -/
private def addCertToContext
    (goal : MVarId) (certName : Name) (AExpr certExpr : Expr) :
    TacticM MVarId := do
  let certTy ← certTypeFor AExpr
  let certExprTy ← inferType certExpr
  unless (← isDefEq certExprTy certTy) do
    throwError "snf: internal error, certificate term has type {certExprTy}, expected {certTy}"
  let (_, goal') ← goal.note certName certExpr (some certTy)
  pure goal'

/-- Call Sage for SNF. Serializes `A` via `matStringList` → `evalMatStringListSafe`
(compiled-code path; does not require `Fin` dims to reduce in the kernel). -/
private def callSnfSageJson (AExpr : Expr) : TacticM SnfSageJsonPayload := do
  let rows ← evalMatStringListSafe AExpr
  let matStr := stringListToMatString rows
  let reqJson := Lean.Json.mkObj [
    ("op", Lean.Json.str "snf"),
    ("matrix", Lean.Json.str matStr)
  ]
  let json ← sendSageRequest reqJson
  let U ← IO.ofExcept (json.getObjVal? "U")
  let Uinv ← IO.ofExcept (json.getObjVal? "Uinv")
  let D ← IO.ofExcept (json.getObjVal? "D")
  let V ← IO.ofExcept (json.getObjVal? "V")
  let Vinv ← IO.ofExcept (json.getObjVal? "Vinv")
  pure { U := U, Uinv := Uinv, D := D, V := V, Vinv := Vinv }

unsafe def evalBoolExpr (e : Expr) : MetaM Bool :=
  Lean.Meta.evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolExpr]
opaque evalBoolExprSafe (e : Expr) : MetaM Bool

unsafe def evalStringExpr (e : Expr) : MetaM String :=
  Lean.Meta.evalExpr String (mkConst ``String []) e

@[implemented_by evalStringExpr]
opaque evalStringExprSafe (e : Expr) : MetaM String

private def parseSerializableElemExpr (R : Expr) (s : String) : TacticM Expr := do
  let serializableTy ← mkAppM ``SageSerializable #[R]
  let serializableInst ← synthInstance serializableTy
  let parseExpr ← mkAppOptM ``SageSerializable.fromSageString
    #[some R, some serializableInst, some (mkStrLit s)]
  let isSomeExpr ← mkAppM ``Option.isSome #[parseExpr]
  let ok ← evalBoolExprSafe isSomeExpr
  unless ok do
    let sageNameExpr ← mkAppOptM ``SageSerializable.sageName #[some R, some serializableInst]
    let ringName ← evalStringExprSafe sageNameExpr
    throwError "snf: failed to decode Sage entry `{s}` as ring `{ringName}`"
  let zeroTy ← mkAppM ``Zero #[R]
  let zeroInst ← synthInstance zeroTy
  let zeroExpr ← mkAppOptM ``Zero.zero #[some R, some zeroInst]
  mkAppOptM ``Option.getD #[some R, some parseExpr, some zeroExpr]

private def decodeSerializableRowsExpr
    (R : Expr) (j : Lean.Json) : TacticM (List (List Expr)) := do
  let rows ← Cultivar.SageDecode.decodeStringMatrix j
  rows.mapM fun row => row.mapM (parseSerializableElemExpr R)

private def mkListExpr (α : Expr) (xs : List Expr) : TacticM Expr := do
  let nilExpr ← mkAppOptM ``List.nil #[some α]
  xs.foldrM
    (fun x acc => mkAppOptM ``List.cons #[some α, some x, some acc])
    nilExpr

/-- Build `rowsToMatrix rows mExpr nExpr : Matrix (Fin mExpr) (Fin nExpr) R`.
`mExpr`/`nExpr` are arbitrary Nat-valued Exprs (not necessarily literals). -/
private def rowsExprToMatrixExpr
    (R : Expr) (rows : List (List Expr)) (mExpr nExpr : Expr) : TacticM Expr := do
  let rowExprs ← rows.mapM (mkListExpr R)
  let listR ← mkAppM ``List #[R]
  let rowsExpr ← mkListExpr listR rowExprs
  let zeroTy ← mkAppM ``Zero #[R]
  let _zeroInst ← synthInstance zeroTy
  mkAppM ``Cultivar.SageDecode.rowsToMatrix #[rowsExpr, mExpr, nExpr]

/-- Build `Matrix finM finN R` as an Expr, reusing existing `Fin _` Exprs directly. -/
private def matrixTyExprFromFin (R finM finN : Expr) : MetaM Expr :=
  mkAppM ``Matrix #[finM, finN, R]

private def ensureMatrixExprHasType (matrixExpr expectedTy : Expr) : TacticM Unit := do
  let gotTy ← inferType matrixExpr
  unless (← isDefEq gotTy expectedTy) do
    throwError "snf: internal error, matrix expression has type {gotTy}, expected {expectedTy}"



syntax (name := snfTac) "snf " term : tactic

@[tactic snfTac] def evalSnfTac : Tactic := fun stx => do
  let goal ← getMainGoal
  let some (_, AStx) := (match stx with
    | `(tactic| snf $A) => some ((), A)
    | _ => none) |
    throwError "expected `snf A`"
  let AExpr ← elabTerm AStx none
  let (finM, finN, mExpr, nExpr, R) ← ensureSnfInput AExpr
  logInfo m!"snf input validated: m={mExpr}, n={nExpr}, ring={R}"
  let payload ← callSnfSageJson AExpr
  let ⟨uJson, uinvJson, dJson, vJson, vinvJson⟩ := payload
  let uRowsExpr ← decodeSerializableRowsExpr R uJson
  let uinvRowsExpr ← decodeSerializableRowsExpr R uinvJson
  let dRowsExpr ← decodeSerializableRowsExpr R dJson
  let vRowsExpr ← decodeSerializableRowsExpr R vJson
  let vinvRowsExpr ← decodeSerializableRowsExpr R vinvJson

  let UExpr ← rowsExprToMatrixExpr R uRowsExpr mExpr mExpr
  let UinvExpr ← rowsExprToMatrixExpr R uinvRowsExpr mExpr mExpr
  let DExpr ← rowsExprToMatrixExpr R dRowsExpr mExpr nExpr
  let VExpr ← rowsExprToMatrixExpr R vRowsExpr nExpr nExpr
  let VinvExpr ← rowsExprToMatrixExpr R vinvRowsExpr nExpr nExpr

  let matMMTy ← matrixTyExprFromFin R finM finM
  let matMNTy ← matrixTyExprFromFin R finM finN
  let matNNTy ← matrixTyExprFromFin R finN finN
  ensureMatrixExprHasType UExpr matMMTy
  ensureMatrixExprHasType UinvExpr matMMTy
  ensureMatrixExprHasType DExpr matMNTy
  ensureMatrixExprHasType VExpr matNNTy
  ensureMatrixExprHasType VinvExpr matNNTy

  let certTy ← certTypeFor AExpr
  let AStx : TSyntax `term ← Lean.PrettyPrinter.delab AExpr
  let RStx : TSyntax `term ← Lean.PrettyPrinter.delab R
  let UStx : TSyntax `term ← Lean.PrettyPrinter.delab UExpr
  let UinvStx : TSyntax `term ← Lean.PrettyPrinter.delab UinvExpr
  let VStx : TSyntax `term ← Lean.PrettyPrinter.delab VExpr
  let VinvStx : TSyntax `term ← Lean.PrettyPrinter.delab VinvExpr
  let DStx : TSyntax `term ← Lean.PrettyPrinter.delab DExpr
  let certStx ← `(
    ({
      U := $UStx
      Uinv := $UinvStx
      V := $VStx
      Vinv := $VinvStx
      D := $DStx
      r := firstZeroDiag $DStx
      hdiag := by native_decide
      hrank := by
        intro i
        have hdiagOk : verifyDiag (R := $RStx) $DStx := by native_decide
        simpa using
          (Cultivar.SNF.diagEntry_eq_zero_iff_ge_firstZeroDiag_of_verifyDiag
            (R := $RStx) (D := $DStx) (i := i) hdiagOk)
      hUUinv := by native_decide
      hVVinv := by native_decide
      heq := by native_decide
      hdiv := by native_decide
    } : CertificateSNF (A := $AStx))
  )
  let certExpr ← elabTerm certStx (some certTy)
  let certExprTy ← inferType certExpr
  unless (← isDefEq certExprTy certTy) do
    throwError "snf: internal error, certificate term has wrong type\nactual: {certExprTy}\nexpected: {certTy}"

  let goal' ← addCertToContext goal `cert AExpr certExpr
  logInfo "snf: added `cert : CertificateSNF A` to local context."
  setGoals [goal']
