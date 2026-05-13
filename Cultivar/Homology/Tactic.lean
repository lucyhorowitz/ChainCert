import Cultivar.Homology.Basic
import Cultivar.SNF.Tactic
import Lean.Elab.Tactic

open Lean Elab Tactic Meta Expr

syntax (name := homologyTac) "homology " term ", " term : tactic

@[tactic homologyTac] def evalHomologyTac : Tactic := fun stx => do
  let (XStx, kStx) ←
    match stx with
    | `(tactic| homology $X:term, $k:term) => pure (X, k)
    | _ => throwUnsupportedSyntax

  let XExpr ← elabTerm XStx none
  let kExpr ← elabTerm kStx (some (mkConst ``Nat))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

  -- sanity checks
  let XTy ← inferType XExpr
  let (``FiniteFacetComplex, #[_ι]) := XTy.getAppFnArgs
    | throwError "homology: expected `X : FiniteFacetComplex ι`, got {XTy}"

  let kTy ← inferType kExpr
  unless (← isDefEq kTy (mkConst ``Nat)) do
    throwError "homology: expected `k : Nat`, got {kTy}"

  -- next: build boundaryK expression
  let XTerm : TSyntax `term ← Lean.PrettyPrinter.delab XExpr
  let kTerm : TSyntax `term ← Lean.PrettyPrinter.delab kExpr

  let dkStx ← `(boundaryK (R := ℤ) $XTerm $kTerm)
  let dkExpr ← elabTerm dkStx none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

  let certK ← mkSNFCertExpr dkExpr

  -- for now, just add this local cert
  let certTy ← mkAppM ``CertificateSNF #[dkExpr]
  let goal ← getMainGoal
  let (_, goal') ← goal.note `certK certK (some certTy)
  setGoals [goal']
