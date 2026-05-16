import ChainCert.Homology.Basic
import ChainCert.SNF.Bridge
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Bridges from homology certificates to Mathlib linear algebra

This file defines the ordinary algebraic quotient represented by a pair of
boundary matrices,

```lean
ker dₖ / im dₖ₊₁,
```

and records the first bridge theorem: the chain condition stored in a
`ChainQuotientCert` is exactly what makes `im dₖ₊₁` a submodule of `ker dₖ`.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
                     [DecidableEq R] [SageSerializable R]
variable {m n p : ℕ}

open scoped Matrix

/-- The cycle submodule of a matrix boundary map. -/
abbrev cycles (dk : Matrix (Fin m) (Fin n) R) : Submodule R (Fin n → R) :=
  LinearMap.ker (matLin dk)

/-- If consecutive matrix boundary maps compose to zero, then the image of the
second lies in the kernel of the first. -/
theorem matRange_le_cycles_of_comp_eq_zero
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (hCC : dk * dk1 = 0) :
    matRange dk1 ≤ cycles dk := by
  rintro y ⟨z, hz⟩
  rw [cycles, LinearMap.mem_ker, matLin, Matrix.mulVecLin_apply]
  rw [← hz]
  calc
    dk *ᵥ (dk1 *ᵥ z) = (dk * dk1) *ᵥ z := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hCC, Matrix.zero_mulVec]

/-- The boundary image, regarded as a submodule of cycles. -/
def boundaryImageInCycles
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R)
    (hCC : dk * dk1 = 0) :
    Submodule R (cycles dk) :=
  (matRange dk1).comap (cycles dk).subtype

/-- The ordinary algebraic homology module represented by two consecutive
boundary matrices. -/
def matrixHomology
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R)
    (hCC : dk * dk1 = 0) : Type _ :=
  cycles dk ⧸ boundaryImageInCycles dk dk1 hCC

instance matrixHomology.instAddCommGroup
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R)
    (hCC : dk * dk1 = 0) :
    AddCommGroup (matrixHomology dk dk1 hCC) := by
  dsimp [matrixHomology]
  exact Submodule.Quotient.addCommGroup (boundaryImageInCycles dk dk1 hCC)

instance matrixHomology.instModule
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R)
    (hCC : dk * dk1 = 0) :
    Module R (matrixHomology dk dk1 hCC) := by
  dsimp [matrixHomology]
  exact Submodule.Quotient.module (boundaryImageInCycles dk dk1 hCC)

namespace CertificateSNF

/-- The coordinate equivalence on cycles induced by an SNF certificate for
`dk`.

Mathematically, this applies the certified inverse column change `Vinv` and then
keeps the bottom coordinates, i.e. the coordinates after the rank cutoff
`certK.r`.  The statement is packaged as a linear equivalence because the SNF
certificate for `dk` should identify `ker dk` with a free module on those bottom
coordinates. -/
noncomputable def cycleCoordinateEquiv
    {dk : Matrix (Fin m) (Fin n) R}
    (certK : CertificateSNF (A := dk)) :
    cycles dk ≃ₗ[R] (Fin (n - certK.r) → R) := by
  sorry

end CertificateSNF

namespace ChainQuotientCert

/-- A chain quotient certificate proves that the certified boundary image is
inside the certified cycles. -/
theorem boundaryImage_le_cycles
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    matRange dk1 ≤ cycles dk :=
  matRange_le_cycles_of_comp_eq_zero cert.hCC

/-- The actual algebraic homology quotient associated to a chain quotient
certificate. -/
abbrev homologyModule
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) : Type _ :=
  matrixHomology dk dk1 cert.hCC

/-- The SNF certificate for the presentation matrix gives a Mathlib quotient
equivalence from that presentation to its diagonal Smith form. -/
noncomputable def presentationCokernelEquivDiagonal
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    ((Fin (n - cert.certK.r) → R) ⧸ matRange cert.M) ≃ₗ[R]
      ((Fin (n - cert.certK.r) → R) ⧸ matRange cert.certM.D) :=
  CertificateSNF.cokernelEquivDiagonal (A := cert.M) cert.certM

/-- Under the cycle-coordinate equivalence coming from the SNF certificate for
`dk`, the boundary image `im dk1` inside `ker dk` is exactly the range of the
stored presentation matrix `M`.

This is the central bookkeeping lemma behind the homology bridge.  It says that
the matrix `M` stored in the certificate is not merely some auxiliary matrix: it
is precisely the boundary image expressed in the certified coordinates on
cycles. -/
theorem map_boundaryImage_eq_presentationRange
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    (boundaryImageInCycles dk dk1 cert.hCC).map
        (CertificateSNF.cycleCoordinateEquiv (R := R) (m := m) (n := n)
          (dk := dk) cert.certK :
          cycles dk →ₗ[R] (Fin (n - cert.certK.r) → R)) =
      matRange cert.M := by
  sorry

/-- A chain quotient certificate identifies the actual algebraic homology
quotient

`ker dk / im dk1`

with the cokernel of the stored presentation matrix `M`.

This is the main theorem needed to justify the `homology` certificate format:
after this theorem, the rest of the computation is ordinary Smith normal form
on `M`. -/
noncomputable def homologyEquivPresentation
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    cert.homologyModule ≃ₗ[R]
      ((Fin (n - cert.certK.r) → R) ⧸ matRange cert.M) :=
  Submodule.Quotient.equiv
    (boundaryImageInCycles dk dk1 cert.hCC)
    (matRange cert.M)
    (CertificateSNF.cycleCoordinateEquiv (R := R) (m := m) (n := n)
      (dk := dk) cert.certK)
    (map_boundaryImage_eq_presentationRange (R := R) cert)

/-- Combining `homologyEquivPresentation` with the existing SNF bridge for `M`
identifies the homology quotient with the cokernel of the certified diagonal
Smith form of `M`.

This is the matrix-level version of the final correctness theorem for a
homology certificate. -/
noncomputable def homologyEquivDiagonal
    {dk : Matrix (Fin m) (Fin n) R}
    {dk1 : Matrix (Fin n) (Fin p) R}
    (cert : ChainQuotientCert (R := R) dk dk1) :
    cert.homologyModule ≃ₗ[R]
      ((Fin (n - cert.certK.r) → R) ⧸ matRange cert.certM.D) :=
  (homologyEquivPresentation (R := R) cert).trans
    (presentationCokernelEquivDiagonal (R := R) cert)

end ChainQuotientCert

namespace CertificateHomology

variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

/-- A homology certificate proves that the next boundary image lies in the
current boundary kernel. -/
theorem boundaryImage_le_cycles {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    matRange (boundaryK (R := R) X (k + 1)) ≤
      cycles (boundaryK (R := R) X k) :=
  cert.quotientCert.boundaryImage_le_cycles

/-- The actual algebraic homology quotient associated to a homology
certificate. -/
abbrev homologyModule {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) : Type _ :=
  cert.quotientCert.homologyModule

/-- The certified presentation of homology has a Mathlib quotient equivalence
to its diagonal Smith form. -/
noncomputable def presentationCokernelEquivDiagonal {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    ((Fin (cellCount X k - cert.quotientCert.certK.r) → R) ⧸
        matRange cert.presentationMatrix) ≃ₗ[R]
      ((Fin (cellCount X k - cert.quotientCert.certK.r) → R) ⧸
        matRange cert.presentationCert.D) :=
  CertificateSNF.cokernelEquivDiagonal (A := cert.presentationMatrix)
    cert.presentationCert

/-- A homology certificate identifies the actual homology quotient of the
boundary maps of `X` in degree `k` with the cokernel of its stored presentation
matrix.

This is the simplicial-complex wrapper around
`ChainQuotientCert.homologyEquivPresentation`. -/
noncomputable def homologyEquivPresentation {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    cert.homologyModule ≃ₗ[R]
      ((Fin (cellCount X k - cert.quotientCert.certK.r) → R) ⧸
        matRange cert.presentationMatrix) :=
  ChainQuotientCert.homologyEquivPresentation (R := R) cert.quotientCert

/-- Final intended correctness statement for `CertificateHomology`: the actual
homology quotient of `X` in degree `k` is linearly equivalent to the cokernel of
the certified diagonal Smith form of the presentation matrix.

For coefficients in `ℤ`, this is the point from which one reads off Betti
numbers and torsion coefficients from the diagonal entries. -/
noncomputable def homologyEquivDiagonal {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    cert.homologyModule ≃ₗ[R]
      ((Fin (cellCount X k - cert.quotientCert.certK.r) → R) ⧸
        matRange cert.presentationCert.D) :=
  (homologyEquivPresentation (R := R) cert).trans
    (presentationCokernelEquivDiagonal (R := R) cert)

end CertificateHomology
