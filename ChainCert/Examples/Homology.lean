import ChainCert.Homology.Tactic
import ChainCert.Examples.Complexes

/-!
# Homology tactic examples

This file shows the basic user-facing modes of the `homology` tactic.
-/

/-- `homology X, k` can add a named certificate to the local context. -/
example : True := by
  homology triangleFFC, 1
  trivial

/-- `homology X, k as h` chooses the local certificate name. -/
example : True := by
  homology triangleFFC, 1 as hTri
  have _ :
      CertificateHomology (R := ℤ) triangleFFC 1 := hTri
  have _ :
      ChainQuotientCert
        (boundaryK (R := ℤ) triangleFFC 1)
        (boundaryK (R := ℤ) triangleFFC 2) := hTri.quotientCert
  have _ :
      CertificateSNF (A := hTri.presentationMatrix) := hTri.presentationCert
  have _ :
      boundaryK (R := ℤ) triangleFFC 1 *
          boundaryK (R := ℤ) triangleFFC 2 = 0 :=
    hTri.boundary_comp_next
  have _ :
      hTri.presentationMatrix =
        cyclePresentationMatrix hTri.quotientCert.certK
          (boundaryK (R := ℤ) triangleFFC 2) :=
    hTri.presentationMatrix_eq
  have _ :
      CertificateSNF (A := hTri.presentationMatrix) :=
    hTri.presentation_has_snf
  trivial

/-- `homology X, k` closes a matching `CertificateHomology` goal. -/
example : CertificateHomology (R := ℤ) triangleFFC 1 := by
  homology triangleFFC, 1
