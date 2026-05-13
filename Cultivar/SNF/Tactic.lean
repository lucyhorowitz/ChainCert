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
  the local context. `snf A as hA` uses the provided local name instead.
  Primary driver inside real proofs.
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


/-- Build a `CertificateSNF AExpr` expression from Sage data, then elaborate and
type-check it. This is the reusable construction backend for the `snf` tactic. -/
def mkSNFCertExpr (AExpr : Expr) : TacticM Expr := do
  let (finM, finN, mExpr, nExpr, R) ← ensureSnfInput AExpr
  -- logInfo m!"snf input validated: m={mExpr}, n={nExpr}, ring={R}"
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
  let mStx : TSyntax `term ← Lean.PrettyPrinter.delab mExpr
  let nStx : TSyntax `term ← Lean.PrettyPrinter.delab nExpr

  let ATypedStx : TSyntax `term ←
    `(($AStx : Matrix (Fin $mStx) (Fin $nStx) $RStx))
  let UTypedStx : TSyntax `term ←
    `(($UStx : Matrix (Fin $mStx) (Fin $mStx) $RStx))
  let UinvTypedStx : TSyntax `term ←
    `(($UinvStx : Matrix (Fin $mStx) (Fin $mStx) $RStx))
  let VTypedStx : TSyntax `term ←
    `(($VStx : Matrix (Fin $nStx) (Fin $nStx) $RStx))
  let VinvTypedStx : TSyntax `term ←
    `(($VinvStx : Matrix (Fin $nStx) (Fin $nStx) $RStx))
  let DTypedStx : TSyntax `term ←
    `(($DStx : Matrix (Fin $mStx) (Fin $nStx) $RStx))

  let hdiagTy ← Lean.Elab.Term.elabType (← `(IsDiagonal $DTypedStx))
  let hdiagExpr ← Lean.Elab.Tactic.elabTerm (← `(by native_decide)) (some hdiagTy)

  let hrankTy ← Lean.Elab.Term.elabType (← `(
  ∀ (i : Fin (min $mStx $nStx)),
    diagEntry $DTypedStx i = 0 ↔ firstZeroDiag $DTypedStx ≤ i.val))
  let hrankExpr ← Lean.Elab.Tactic.elabTerm (← `(
  by
    intro i
    have hdiagOk : verifyDiag (R := $RStx) $DTypedStx := by native_decide
    simpa using
      (Cultivar.SNF.diagEntry_eq_zero_iff_ge_firstZeroDiag_of_verifyDiag
        (R := $RStx) (D := $DTypedStx) (i := i) hdiagOk)
  )) (some hrankTy)

  let hUUinvTy ← Lean.Elab.Term.elabType (← `($UTypedStx * $UinvTypedStx = 1))
  let hUUinvExpr ← Lean.Elab.Tactic.elabTerm (← `(by native_decide)) (some hUUinvTy)

  let hVVinvTy ← Lean.Elab.Term.elabType (← `($VTypedStx * $VinvTypedStx = 1))
  let hVVinvExpr ← Lean.Elab.Tactic.elabTerm (← `(by native_decide)) (some hVVinvTy)

  let heqTy ← Lean.Elab.Term.elabType (← `($UTypedStx * $ATypedStx * $VTypedStx = $DTypedStx))
  let heqExpr ← Lean.Elab.Tactic.elabTerm (← `(by native_decide)) (some heqTy)

  let hdivTy ← Lean.Elab.Term.elabType (← `(
    ∀ i j : Fin (min $mStx $nStx), i.val + 1 = j.val →
      diagEntry $DTypedStx i ∣ diagEntry $DTypedStx j))
  let hdivExpr ← Lean.Elab.Tactic.elabTerm (← `(by native_decide)) (some hdivTy)

  let rExpr ← mkAppM ``firstZeroDiag #[DExpr]

  let certExpr ← mkAppOptM ``CertificateSNF.mk #[
    some mExpr, some nExpr,
    some R,
    none, none,
    some AExpr,
    some UExpr,
    some UinvExpr,
    some VExpr,
    some VinvExpr,
    some DExpr,
    some rExpr,
    some hdiagExpr,
    some hrankExpr,
    some hUUinvExpr,
    some hVVinvExpr,
    some heqExpr,
    some hdivExpr
  ]

  let certExprTy ← inferType certExpr
  unless (← isDefEq certExprTy certTy) do
    throwError "snf: internal error, constructed certificate has wrong type\n\
     actual: {certExprTy}\n\
     expected: {certTy}"
  pure certExpr

syntax (name := snfTac) "snf " term (" as " ident)? : tactic

@[tactic snfTac] def evalSnfTac : Tactic := fun stx => do
  let goal ← getMainGoal
  let some (certName, AStx) := (match stx with
    | `(tactic| snf $A as $h:ident) => some (h.getId, A)
    | `(tactic| snf $A) => some (`cert, A)
    | _ => none) |
    throwError "expected `snf A` or `snf A as h`"
  let AExpr ← elabTerm AStx none
  let certExpr ← mkSNFCertExpr AExpr
  let certExprTy ← inferType certExpr
  let certTy ← certTypeFor AExpr
  unless (← isDefEq certExprTy certTy) do
    throwError "snf: internal error, certificate term has wrong type\nactual: {certExprTy}\nexpected: {certTy}"

  let goal' ← addCertToContext goal certName AExpr certExpr
  -- logInfo "snf: added `cert : CertificateSNF A` to local context."
  setGoals [goal']
