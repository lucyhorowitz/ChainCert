import ChainCert.Homology.Basic
import ChainCert.SNF.Tactic
import Lean.Elab.Tactic

open Lean Elab Tactic Meta Expr

/-!
# Homology tactic

The `homology` tactic computes a certified presentation for simplicial homology
over `ℤ`.

For a finite facet complex `X` and dimension `k`, the tactic builds a
certificate for:

```lean
ker (boundaryK (R := ℤ) X k) / im (boundaryK (R := ℤ) X (k + 1))
```

as a top-level value of type:

```lean
CertificateHomology (R := ℤ) X k
```

Internally, this includes a `ChainQuotientCert` containing SNF certificates for
`∂ₖ` and for the cycle-presentation matrix.

## User syntax

* `homology X, k`

  If the goal is definitionally equal to
  `CertificateHomology (R := ℤ) X k`, the tactic closes it. Otherwise, it adds
  a local hypothesis named `homologyCert` and leaves the goal unchanged.

* `homology X, k as h`

  Always adds a local hypothesis with the chosen name:

  ```lean
  h : CertificateHomology (R := ℤ) X k
  ```

The lower-level quotient certificate is available as `h.quotientCert`.

## Requirements

`X` must elaborate as `FiniteFacetComplex ι`, and `k` must elaborate as `Nat`.
The boundary matrices must be evaluable by the same SNF backend used by the
`snf` tactic.
-/

/--
Compute a certified simplicial homology presentation over `ℤ`.

Examples:

```lean
example : CertificateHomology (R := ℤ) X k := by
  homology X, k

example : True := by
  homology X, k as h
  -- h : CertificateHomology (R := ℤ) X k
  exact trivial
```
-/
syntax (name := homologyTac) "homology " term ", " term (" as " ident)? : tactic

@[tactic homologyTac] def evalHomologyTac : Tactic := fun stx => do
  let (certName, XStx, kStx) ←
    match stx with
    | `(tactic| homology $X:term, $k:term as $h:ident) => pure (h.getId, X, k)
    | `(tactic| homology $X:term, $k:term) => pure (`homologyCert, X, k)
    | _ => throwUnsupportedSyntax

  let XExpr ← elabTerm XStx none
  let kExpr ← elabTerm kStx (some (mkConst ``Nat))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

  -- sanity checks
  let XTy ← inferType XExpr
  let (``FiniteFacetComplex, #[ιExpr]) := XTy.getAppFnArgs
    | throwError "homology: expected `X : FiniteFacetComplex ι`, got {XTy}"

  let kTy ← inferType kExpr
  unless (← isDefEq kTy (mkConst ``Nat)) do
    throwError "homology: expected `k : Nat`, got {kTy}"

  let k1Expr ← mkAppM ``Nat.succ #[kExpr]

  let dkExpr ← mkAppOptM ``boundaryK #[
    some (mkConst ``Int), none, none, none, none, none, some XExpr, some kExpr]
  let dk1Expr ← mkAppOptM ``boundaryK #[
    some (mkConst ``Int), none, none, none, none, none, some XExpr, some k1Expr]

  let certK ← mkSNFCertExpr dkExpr -- obligation 1 done!

  let MExpr ← mkAppM ``cyclePresentationMatrix #[certK, dk1Expr] --obligation 2
  let certM ← mkSNFCertExpr MExpr --obligation 3

  let prodExpr ← mkAppM ``HMul.hMul #[dkExpr, dk1Expr]
  let prodTy ← inferType prodExpr
  let zeroTy ← mkAppM ``Zero #[prodTy]
  let zeroInst ← synthInstance zeroTy
  let zeroExpr ← mkAppOptM ``Zero.zero #[some prodTy, some zeroInst]
  let hCCTy ← mkEq prodExpr zeroExpr
  let hCC ← Lean.Elab.Tactic.elabNativeDecideCore `homology hCCTy

  let hM ← mkEqRefl MExpr

  let qcExpr ← mkAppOptM ``ChainQuotientCert.mk #[
  none, none, none,        -- m n p
  some (mkConst ``Int),    -- R
  none, none,              -- instances
  some dkExpr,
  some dk1Expr,
  some certK,
  some hCC,
  some MExpr,
  some hM,
  some certM]

  let homologyCertExpr ← mkAppOptM ``CertificateHomology.mk #[
    some (mkConst ``Int),
    none, none,
    some ιExpr,
    none, none, none,
    some XExpr,
    some kExpr,
    some qcExpr
  ]

  let hcTy ← mkAppOptM ``CertificateHomology #[
    some (mkConst ``Int),
    none, none,
    some ιExpr,
    none, none, none,
    some XExpr,
    some kExpr
  ]

  let goal ← getMainGoal

  if certName == `homologyCert then
    let target ← goal.getType
    if ← isDefEq target hcTy then
      goal.assign homologyCertExpr
      setGoals []
    else
      let (_, goal') ← goal.note certName homologyCertExpr (some hcTy)
      setGoals [goal']
  else
    let (_, goal') ← goal.note certName homologyCertExpr (some hcTy)
    setGoals [goal']
