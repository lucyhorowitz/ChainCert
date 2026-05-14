import ChainCert.SNF.Core
import ChainCert.SNF.Verify
import ChainCert.SNF.Rank
import ChainCert.SageServer
import ChainCert.SageEncode
import ChainCert.SageDecode
import Lean.Elab.Tactic
import Lean

/-!
# SNF tactic

The `snf` tactic computes and certifies Smith normal form data for a concrete
matrix.

## User syntax

* `snf A`

  Adds a local hypothesis named `cert`:

  ```lean
  cert : CertificateSNF A
  ```

* `snf A as hA`

  Adds the same certificate under the chosen name:

  ```lean
  hA : CertificateSNF A
  ```

The tactic is goal-agnostic: it enriches the local context and leaves the
current goal unchanged.

## Requirements

The matrix must have type:

```lean
Matrix (Fin m) (Fin n) R
```

where its entries can be serialized through `SageSerializable R`. The matrix
data must be evaluable at elaboration time; fully symbolic matrix variables are
not supported.

Dimensions may be non-literal expressions such as `cellCount X k`. The tactic
serializes entries by compiled evaluation, asks Sage for SNF data, reconstructs
the matrices in Lean, and builds a `CertificateSNF A` term checked by Lean.
-/

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
  let rows ← ChainCert.SageDecode.decodeStringMatrix j
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
  mkAppM ``ChainCert.SageDecode.rowsToMatrix #[rowsExpr, mExpr, nExpr]

/-- Build `Matrix finM finN R` as an Expr, reusing existing `Fin _` Exprs directly. -/
private def matrixTyExprFromFin (R finM finN : Expr) : MetaM Expr :=
  mkAppM ``Matrix #[finM, finN, R]

private def ensureMatrixExprHasType (matrixExpr expectedTy : Expr) : TacticM Unit := do
  let gotTy ← inferType matrixExpr
  unless (← isDefEq gotTy expectedTy) do
    throwError "snf: internal error, matrix expression has type {gotTy}, expected {expectedTy}"

private def mkZeroOfType (α : Expr) : TacticM Expr := do
  let zeroTy ← mkAppM ``Zero #[α]
  let zeroInst ← synthInstance zeroTy
  mkAppOptM ``Zero.zero #[some α, some zeroInst]

private def mkOneOfType (α : Expr) : TacticM Expr := do
  let oneTy ← mkAppM ``One #[α]
  let oneInst ← synthInstance oneTy
  mkAppOptM ``One.one #[some α, some oneInst]

private def mkMulExpr (a b : Expr) : TacticM Expr :=
  mkAppM ``HMul.hMul #[a, b]

private def mkDiagEntryExpr (D i : Expr) : TacticM Expr :=
  mkAppM ``diagEntry #[D, i]

private def mkFirstZeroDiagExpr (D : Expr) : TacticM Expr :=
  mkAppM ``firstZeroDiag #[D]

private def mkFinValExpr (i : Expr) : TacticM Expr :=
  mkAppM ``Fin.val #[i]

private def mkDecideProofExpr (p : Expr) : TacticM Expr :=
  Lean.Elab.Tactic.elabNativeDecideCore `snf p

private def mkIsDiagonalExpr (R mExpr nExpr DExpr : Expr) : TacticM Expr := do
  let zeroTy ← mkAppM ``Zero #[R]
  let zeroInst ← synthInstance zeroTy
  mkAppOptM ``IsDiagonal #[
    some R, some mExpr, some nExpr, some DExpr, some zeroInst]

private def mkRankProofType (mExpr nExpr DExpr rExpr R : Expr) : TacticM Expr := do
  let minExpr ← mkAppM ``Nat.min #[mExpr, nExpr]
  let finMinTy ← mkAppM ``Fin #[minExpr]
  withLocalDeclD `i finMinTy fun i => do
    let diagI ← mkDiagEntryExpr DExpr i
    let zeroR ← mkZeroOfType R
    let lhs ← mkEq diagI zeroR
    let iVal ← mkFinValExpr i
    let rhs ← mkAppM ``Nat.le #[rExpr, iVal]
    let body ← mkAppM ``Iff #[lhs, rhs]
    mkForallFVars #[i] body

private def mkRankProofExpr (mExpr nExpr DExpr rExpr R : Expr) : TacticM Expr := do
  let hTy ← mkAppM ``verifyDiag #[DExpr]
  let hdiagOk ← mkDecideProofExpr hTy
  let minExpr ← mkAppM ``Nat.min #[mExpr, nExpr]
  let finMinTy ← mkAppM ``Fin #[minExpr]
  let proof ←
    withLocalDeclD `i finMinTy fun i => do
      let theoremExpr ←
        mkAppM ``ChainCert.SNF.diagEntry_eq_zero_iff_ge_firstZeroDiag_of_verifyDiag
          #[DExpr, i, hdiagOk]
      mkLambdaFVars #[i] theoremExpr
  let proofTy ← inferType proof
  let expectedTy ← mkRankProofType mExpr nExpr DExpr rExpr R
  unless (← isDefEq proofTy expectedTy) do
    throwError "snf: internal error, rank proof has type {proofTy}, expected {expectedTy}"
  pure proof

private def mkDivisibilityProofType (mExpr nExpr DExpr : Expr) : TacticM Expr := do
  let minExpr ← mkAppM ``Nat.min #[mExpr, nExpr]
  let finMinTy ← mkAppM ``Fin #[minExpr]
  withLocalDeclD `i finMinTy fun i => do
    withLocalDeclD `j finMinTy fun j => do
      let iVal ← mkFinValExpr i
      let jVal ← mkFinValExpr j
      let iSucc ← mkAppM ``Nat.succ #[iVal]
      let hTy ← mkEq iSucc jVal
      withLocalDeclD `h hTy fun h => do
        let diagI ← mkDiagEntryExpr DExpr i
        let diagJ ← mkDiagEntryExpr DExpr j
        let body ← mkAppM ``Dvd.dvd #[diagI, diagJ]
        mkForallFVars #[i, j, h] body


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

  let rExpr ← mkAppM ``firstZeroDiag #[DExpr]

  let hdiagTy ← mkIsDiagonalExpr R mExpr nExpr DExpr
  let hdiagExpr ← mkDecideProofExpr hdiagTy

  let hrankExpr ← mkRankProofExpr mExpr nExpr DExpr rExpr R

  let UUinvExpr ← mkMulExpr UExpr UinvExpr
  let oneMM ← mkOneOfType matMMTy
  let hUUinvTy ← mkEq UUinvExpr oneMM
  let hUUinvExpr ← mkDecideProofExpr hUUinvTy

  let VVinvExpr ← mkMulExpr VExpr VinvExpr
  let oneNN ← mkOneOfType matNNTy
  let hVVinvTy ← mkEq VVinvExpr oneNN
  let hVVinvExpr ← mkDecideProofExpr hVVinvTy

  let UAExpr ← mkMulExpr UExpr AExpr
  let UAVExpr ← mkMulExpr UAExpr VExpr
  let heqTy ← mkEq UAVExpr DExpr
  let heqExpr ← mkDecideProofExpr heqTy

  let hdivTy ← mkDivisibilityProofType mExpr nExpr DExpr
  let hdivExpr ← mkDecideProofExpr hdivTy

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

/--
Compute a Smith normal form certificate for `A`.

Examples:

```lean
example : True := by
  snf A
  -- cert : CertificateSNF A
  trivial

example : True := by
  snf A as hA
  -- hA : CertificateSNF A
  trivial
```
-/
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
