import ChainCert.Examples.Complexes
import ChainCert.Boundary.Verify
import ChainCert.SNF.Tactic
import ChainCert.Homology.Tactic
import ChainCert.Homology.Command
import ChainCert.Homology.Bridge

/-!
Outline toward computing simplicial homology of the Klein bottle over `ℤ`.

This file is intentionally staged and contains `sorry` placeholders.
The intended pipeline is:

1. Fix concrete `∂₂ : C₂ → C₁` and `∂₁ : C₁ → C₀` matrices in canonical bases.
2. Certify SNF data for `∂₂` and `∂₁` with `snf`.
3. Read off rank data (Betti/free-rank part).
4. Use SNF/quotient decomposition to identify torsion in `H₁`.

Target result:
* `H₀(Klein; ℤ) ≅ ℤ`
* `H₁(Klein; ℤ) ≅ ℤ ⊕ ℤ/2ℤ`
* `H₂(Klein; ℤ) = 0`
-/

-- #homology kleinBottleFFC, 1

-- /-- Build the H₁ certificate via the `homology` tactic (term-mode), avoiding
-- `homology_cert`'s slow per-field `addAbbrevDecl`. -/
-- set_option maxHeartbeats 4000000 in
-- noncomputable def kleinBottleH1Cert : CertificateHomology (R := ℤ) kleinBottleFFC 1 := by
--   homology kleinBottleFFC, 1

example : True := by
  homology triangleFFC, 1
  trivial

/-! ## Worked example: `H₁(triangle; ℤ) = 0`

The filled 2-simplex has `H₁ = 0`. The pipeline used here:

* `homology triangleFFC, 1` builds `hTri : CertificateHomology ℤ triangleFFC 1`
  from a Sage-checked SNF;
* `CertificateHomology.homologyEquivPi` identifies the abstract homology
  quotient with the product `∀ i, ℤ ⧸ ⟨D_{ii}⟩` of row-quotients of the
  certified diagonal Smith form `D` returned by Sage;
* on the triangle the presentation matrix has SNF `diag(1)`, so every factor
  is `ℤ ⧸ ⟨1⟩ = 0` and the product is the trivial module. -/

/-- The H₁ certificate for the triangle, produced by the `homology` pipeline
from a Sage-checked SNF. -/
noncomputable def triangleH1Cert : CertificateHomology (R := ℤ) triangleFFC 1 := by
  homology triangleFFC, 1

/-- The certified H₁ of the triangle is linearly equivalent to the product of
row-ideal quotients of the Sage-certified diagonal Smith form `D`.

This is the pipeline's main correctness statement specialised to the
triangle: the abstract homology module of the simplicial complex is
identified with the cokernel of the diagonal matrix returned by Sage. -/
theorem triangleH1_equiv_sage_diagonal_pi :
    Nonempty (triangleH1Cert.homologyModule ≃ₗ[ℤ]
      ∀ i : Fin (cellCount triangleFFC 1 - triangleH1Cert.quotientCert.certK.r),
        ℤ ⧸ rowDiagIdeal (R := ℤ) triangleH1Cert.presentationCert.D i) :=
  ⟨triangleH1Cert.homologyEquivPi⟩

/-- Each row-ideal in a diagonal SNF is the whole ring exactly when its
diagonal entry is a unit. -/
private lemma rowDiagIdeal_eq_top_of_isUnit
    {R : Type*} [CommRing R] {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) R) (i : Fin m)
    (h : IsUnit (rowDiagVal D i)) : rowDiagIdeal D i = ⊤ := by
  change (Ideal.span {rowDiagVal D i} : Ideal R) = ⊤
  rw [Ideal.span_singleton_eq_top]
  exact h

/-- `H₁(triangle; ℤ) = 0`: the certified homology module is trivial. -/
theorem triangleH1_subsingleton : Subsingleton triangleH1Cert.homologyModule := by
  haveI : ∀ i : Fin (cellCount triangleFFC 1 - triangleH1Cert.quotientCert.certK.r),
      Subsingleton (ℤ ⧸ rowDiagIdeal (R := ℤ) triangleH1Cert.presentationCert.D i) := by
    intro i
    refine Submodule.Quotient.subsingleton_iff.mpr ?_
    refine rowDiagIdeal_eq_top_of_isUnit _ i ?_
    rw [Int.isUnit_iff]
    revert i
    unfold triangleH1Cert
    native_decide
  exact triangleH1Cert.homologyEquivPi.toEquiv.subsingleton

namespace ChainCert
namespace Examples

end Examples
end ChainCert
