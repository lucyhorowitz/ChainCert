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

end CertificateHomology
