import ChainCert.Examples.RP2Cert
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# Worked example: `H₁(ℝP²; ℤ)` has order-2 torsion

The real projective plane is the smallest closed surface whose integral
homology has torsion. Its minimal triangulation `rp2FFC` has 6 vertices,
15 edges, and 10 triangles. The `H₁` certificate is built in
`ChainCert.Examples.RP2Cert`; here we read off the torsion factor from the
diagonal Smith form via `CertificateHomology.homologyEquivPi`.
-/

/-- The certified `H₁` of `ℝP²` is linearly equivalent to the product of
row-ideal quotients of the Sage-certified diagonal Smith form `D`.

This is the bridge pipeline's main correctness statement specialised to
`ℝP²`: the abstract homology module of the simplicial complex is identified
with the cokernel of the diagonal matrix returned by Sage. -/
theorem rp2H1_equiv_sage_diagonal_pi :
    Nonempty (rp2H1Cert.homologyModule ≃ₗ[ℤ]
      ∀ i : Fin (cellCount rp2FFC 1 - rp2H1Cert.quotientCert.certK.r),
        ℤ ⧸ rowDiagIdeal (R := ℤ) rp2H1Cert.presentationCert.D i) :=
  ⟨rp2H1Cert.homologyEquivPi⟩

/-! ### Torsion structure of `H₁(ℝP²)`

We probe the Sage-certified diagonal: it has 10 entries, exactly one of which
is non-unit, and that entry is `±2`. So among the ten factors of
`homologyEquivPi`, nine are trivial and one is `ℤ/2ℤ`. -/

/-- The diagonal index set has 10 elements. -/
theorem rp2_presentation_size :
    cellCount rp2FFC 1 - rp2H1Cert.quotientCert.certK.r = 10 := by
  unfold rp2H1Cert
  native_decide

/-- Exactly one diagonal entry of the certified Smith form is non-unit. -/
theorem rp2_unique_non_unit_diagonal :
    (Finset.univ.filter (fun i : Fin (cellCount rp2FFC 1 -
        rp2H1Cert.quotientCert.certK.r) =>
      ¬ IsUnit (rowDiagVal (R := ℤ) rp2H1Cert.presentationCert.D i))).card
      = 1 := by
  unfold rp2H1Cert
  native_decide

/-- The unique non-unit diagonal entry has absolute value `2`. -/
theorem rp2_torsion_diagonal_is_two
    (i : Fin (cellCount rp2FFC 1 - rp2H1Cert.quotientCert.certK.r))
    (hi : ¬ IsUnit (rowDiagVal (R := ℤ) rp2H1Cert.presentationCert.D i)) :
    (rowDiagVal (R := ℤ) rp2H1Cert.presentationCert.D i).natAbs = 2 := by
  revert i hi
  unfold rp2H1Cert
  native_decide
