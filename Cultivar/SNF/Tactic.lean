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
- Matrix dimensions and entries should be recoverable at elaboration time.

## Core workflow
1. Serialize `A`, call Sage, and obtain `U`, `Uinv`, `D`, `V`, `Vinv`.
2. Decode back into Lean matrices.
3. Verify in Lean before introducing results:
   - diagonal/core checks (shape + zero tail),
   - inverse checks (`U * Uinv = 1`, `V * Vinv = 1`),
   - factorization check (`U * A * V = D`),
   - divisibility chain on diagonal entries.
4. If verification fails, throw a hard error with useful diagnostics.

## What to add to local context
Prefer introducing one main object first:
- `cert : CertificateSNF (A := A)`

Then optionally expose convenient projections/bindings:
- `cert.D`, `cert.r`
- diagonal accessor (e.g. `fun i => diagEntry cert.D i`)
- `cert.heq` (factorization)
- `cert.hdiv` (divisibility chain)

This keeps downstream use (e.g. homology computations) proof-friendly while
still allowing easy extraction of diagonal invariants.

## Suggested options
- default `snf A`: add only `cert`.
- `snf A (diag)`: also add explicit diagonal data binding/list.
- `snf A (verbose)`: print Sage payload + verification diagnostics.
- optional cache control later (`cache` / `no_cache`) if recomputation becomes expensive.

Design preference: center the tactic around `CertificateSNF`; diagonal lists are
derived convenience data, not the primary artifact. -/

open Lean Elab Tactic Meta Expr

private structure SnfSageJsonPayload where
  U : Lean.Json
  Uinv : Lean.Json
  D : Lean.Json
  V : Lean.Json
  Vinv : Lean.Json

private def ensureSnfInput (AExpr : Expr) : TacticM (Nat × Nat × Expr) := do
  let AType ← inferType AExpr
  let (``Matrix, #[finM, finN, R]) := AType.getAppFnArgs
    | throwError "snf: expected `Matrix (Fin m) (Fin n) R`, got {AType}"

  let (``Fin, #[mExpr0]) := finM.getAppFnArgs
    | throwError "snf: expected row index type `Fin m`, got {finM}"
  let (``Fin, #[nExpr0]) := finN.getAppFnArgs
    | throwError "snf: expected col index type `Fin n`, got {finN}"

  let mExpr ← whnf mExpr0
  let nExpr ← whnf nExpr0
  let some m := mExpr.rawNatLit?
    | throwError "snf: `m` must be a concrete Nat"
  let some n := nExpr.rawNatLit?
    | throwError "snf: `n` must be a concrete Nat"

  if AExpr.hasMVar then
    throwError "snf: matrix must be concrete/closed (contains metavariables)"

  let sageSerializableTy ← mkAppM ``SageSerializable #[R]
  let _inst ← synthInstance sageSerializableTy

  pure (m, n, R)

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

private def callSnfSageJson
    (AExpr : Expr) (m n : Nat) : TacticM SnfSageJsonPayload := do
  let finMType ← mkAppM ``Fin #[mkRawNatLit m]
  let finNType ← mkAppM ``Fin #[mkRawNatLit n]
  let mut rows : List (List String) := []
  for i in List.range m do
    let mut row : List String := []
    for j in List.range n do
      let iExpr ← mkNumeral finMType i
      let jExpr ← mkNumeral finNType j
      let entry := mkApp2 AExpr iExpr jExpr
      let s ← evalSageStringSafe entry
      row := row ++ [s]
    rows := rows ++ [row]
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
  Lean.Meta.evalExpr String (mkConst ``String) e

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

private def rowsExprToMatrixExpr
    (R : Expr) (rows : List (List Expr)) (m n : Nat) : TacticM Expr := do
  let rowExprs ← rows.mapM (mkListExpr R)
  let listR ← mkAppM ``List #[R]
  let rowsExpr ← mkListExpr listR rowExprs
  Cultivar.SageDecode.matrixExprOfRows R rowsExpr m n

private def matrixTyExpr (R : Expr) (m n : Nat) : MetaM Expr :=
  mkAppM ``Matrix #[mkApp (mkConst ``Fin) (mkRawNatLit m), mkApp (mkConst ``Fin) (mkRawNatLit n), R]

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
  let (m, n, R) ← ensureSnfInput AExpr
  logInfo m!"snf input validated: m={m}, n={n}, ring={R}"
  let (_payload) ← callSnfSageJson AExpr m n
  let ⟨uJson, uinvJson, dJson, vJson, vinvJson⟩ := _payload
  let uRowsExpr ← decodeSerializableRowsExpr R uJson
  let uinvRowsExpr ← decodeSerializableRowsExpr R uinvJson
  let dRowsExpr ← decodeSerializableRowsExpr R dJson
  let vRowsExpr ← decodeSerializableRowsExpr R vJson
  let vinvRowsExpr ← decodeSerializableRowsExpr R vinvJson

  let UExpr ← rowsExprToMatrixExpr R uRowsExpr m m
  let UinvExpr ← rowsExprToMatrixExpr R uinvRowsExpr m m
  let DExpr ← rowsExprToMatrixExpr R dRowsExpr m n
  let VExpr ← rowsExprToMatrixExpr R vRowsExpr n n
  let VinvExpr ← rowsExprToMatrixExpr R vinvRowsExpr n n

  let matMMTy ← matrixTyExpr R m m
  let matMNTy ← matrixTyExpr R m n
  let matNNTy ← matrixTyExpr R n n
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
