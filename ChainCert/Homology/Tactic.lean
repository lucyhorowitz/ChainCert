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
syntax (name := homologyCertCmd) "homology_cert " term ", " term " as " ident : command

private def snfPayloadFromObject (j : Lean.Json) : TacticM SnfSageJsonPayload := do
  let U ← IO.ofExcept (j.getObjVal? "U")
  let Uinv ← IO.ofExcept (j.getObjVal? "Uinv")
  let D ← IO.ofExcept (j.getObjVal? "D")
  let V ← IO.ofExcept (j.getObjVal? "V")
  let Vinv ← IO.ofExcept (j.getObjVal? "Vinv")
  pure { U := U, Uinv := Uinv, D := D, V := V, Vinv := Vinv }

private def callHomologyWitnesses (XExpr kExpr : Expr) :
    TacticM (SnfSageJsonPayload × SnfSageJsonPayload) := do
  let dim ← evalNatSafe kExpr
  let rawExpr ← mkAppM ``FiniteFacetComplex.toRawFacets #[XExpr]
  let rows ← evalRawFacetStringListSafe rawExpr
  let facetsStr := stringListToMatString rows
  let reqJson := Lean.Json.mkObj [
    ("op", Lean.Json.str "homology"),
    ("facets", Lean.Json.str facetsStr),
    ("dim", Lean.Json.num dim),
    ("reduced", Lean.Json.bool false),
    ("base_ring", Lean.Json.str "ZZ"),
    ("witnesses", Lean.Json.bool true)
  ]
  let json ← sendSageRequest reqJson
  let snfKJson ← IO.ofExcept (json.getObjVal? "snf_k")
  let snfMJson ← IO.ofExcept (json.getObjVal? "snf_M")
  let snfK ← snfPayloadFromObject snfKJson
  let snfM ← snfPayloadFromObject snfMJson
  pure (snfK, snfM)

private def addAbbrevDecl (name : Name) (type value : Expr) : Term.TermElabM Unit := do
  addAndCompile <| Declaration.defnDecl
    { name := name
      levelParams := []
      safety := DefinitionSafety.safe
      hints := ReducibilityHints.regular 0
      type := ← instantiateMVars type
      value := ← instantiateMVars value }

private def runTacticAsTerm (x : TacticM α) : Term.TermElabM α := do
  let (a, _) ← x { elaborator := `homology_cert, recover := false } |>.run { goals := [] }
  pure a

private def scopedName (n : Name) : Term.TermElabM Name := do
  if n.isInternal then
    pure n
  else
    return (← getCurrNamespace) ++ n

elab_rules : command
| `(homology_cert $XStx:term, $kStx:term as $h:ident) =>
  Lean.Elab.Command.liftTermElabM do
    let baseName ← scopedName h.getId
    let XExpr ← Term.elabTerm XStx none
    let kExpr ← Term.elabTerm kStx (some (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing

    let XTy ← inferType XExpr
    let (``FiniteFacetComplex, #[ιExpr]) := XTy.getAppFnArgs
      | throwError "homology_cert: expected `X : FiniteFacetComplex ι`, got {XTy}"

    let kTy ← inferType kExpr
    unless (← isDefEq kTy (mkConst ``Nat)) do
      throwError "homology_cert: expected `k : Nat`, got {kTy}"

    let k1Expr ← mkAppM ``Nat.succ #[kExpr]
    let dkExpr ← mkAppOptM ``boundaryK #[
      some (mkConst ``Int), none, none, none, none, none, some XExpr, some kExpr]
    let dk1Expr ← mkAppOptM ``boundaryK #[
      some (mkConst ``Int), none, none, none, none, none, some XExpr, some k1Expr]

    let (snfKPayload, snfMPayload) ←
      runTacticAsTerm (callHomologyWitnesses XExpr kExpr)

    let dkName := baseName.str "dk"
    let dkTy ← inferType dkExpr
    logInfo m!"homology_cert: adding {dkName}"
    addAbbrevDecl dkName dkTy dkExpr
    let dkConst := mkConst dkName

    let dk1Name := baseName.str "dk1"
    let dk1Ty ← inferType dk1Expr
    logInfo m!"homology_cert: adding {dk1Name}"
    addAbbrevDecl dk1Name dk1Ty dk1Expr
    let dk1Const := mkConst dk1Name

    let certKName := baseName.str "certK"
    logInfo m!"homology_cert: adding {certKName}"
    let certKConst ← declareSNFCertFromPayload certKName dkConst snfKPayload

    let MExpr ← mkAppM ``cyclePresentationMatrix #[certKConst, dk1Const]
    let MName := baseName.str "M"
    let MTy ← inferType MExpr
    logInfo m!"homology_cert: adding {MName}"
    addAbbrevDecl MName MTy MExpr
    let MConst := mkConst MName

    let certMName := baseName.str "certM"
    logInfo m!"homology_cert: adding {certMName}"
    let certMConst ← declareSNFCertFromPayload certMName MConst snfMPayload

    let prodExpr ← mkAppM ``HMul.hMul #[dkConst, dk1Const]
    let prodTy ← inferType prodExpr
    let zeroTy ← mkAppM ``Zero #[prodTy]
    let zeroInst ← synthInstance zeroTy
    let zeroExpr ← mkAppOptM ``Zero.zero #[some prodTy, some zeroInst]
    let hCCTy ← mkEq prodExpr zeroExpr
    logInfo m!"homology_cert: proving chain condition"
    let hCC ← runTacticAsTerm (Lean.Elab.Tactic.elabNativeDecideCore `homology_cert hCCTy)

    let hMTy ← mkEq MConst MExpr
    let hM ← mkEqRefl MConst
    unless (← isDefEq (← inferType hM) hMTy) do
      throwError "homology_cert: internal error constructing presentation matrix equality"

    let qcExpr ← mkAppOptM ``ChainQuotientCert.mk #[
      none, none, none,
      some (mkConst ``Int),
      none, none,
      some dkConst,
      some dk1Const,
      some certKConst,
      some hCC,
      some MConst,
      some hM,
      some certMConst]

    let finalExpr ← mkAppOptM ``CertificateHomology.mk #[
      some (mkConst ``Int),
      none, none,
      some ιExpr,
      none, none, none,
      some XExpr,
      some kExpr,
      some qcExpr]

    let finalTy ← mkAppOptM ``CertificateHomology #[
      some (mkConst ``Int),
      none, none,
      some ιExpr,
      none, none, none,
      some XExpr,
      some kExpr]
    logInfo m!"homology_cert: adding {baseName}"
    addAbbrevDecl baseName finalTy finalExpr

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

  let (snfKPayload, snfMPayload) ← callHomologyWitnesses XExpr kExpr

  let certK ← mkSNFCertExprFromPayload dkExpr snfKPayload -- obligation 1 done!

  let MExpr ← mkAppM ``cyclePresentationMatrix #[certK, dk1Expr] --obligation 2
  let certM ← mkSNFCertExprFromPayload MExpr snfMPayload --obligation 3

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
