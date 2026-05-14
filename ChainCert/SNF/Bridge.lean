import ChainCert.SNF.Core
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Bridges from executable SNF certificates to Mathlib objects

The executable certificate `CertificateSNF A` stores concrete matrices `U`, `V`
and `D` with `U * A * V = D`.  This file records consequences of that data in
ordinary Mathlib linear algebra terms.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [DecidableEq R]
variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)

open scoped Matrix

namespace CertificateSNF

/-- The row-operation matrix from an SNF certificate as a linear equivalence. -/
noncomputable def rowLinearEquiv (cert : CertificateSNF A) :
    (Fin m → R) ≃ₗ[R] (Fin m → R) :=
  Matrix.toLin'OfInv (M := cert.Uinv) (M' := cert.U) cert.hUinvU cert.hUUinv

omit [IsDomain R] [IsPrincipalIdealRing R] in
@[simp]
theorem rowLinearEquiv_apply (cert : CertificateSNF A) (x : Fin m → R) :
    rowLinearEquiv (A := A) cert x = cert.U *ᵥ x :=
  rfl

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- The certified row operations identify the range of `A` with the range of
the certified diagonal matrix `D`. -/
theorem map_matRange_eq_diagonal (cert : CertificateSNF A) :
    (matRange A).map (rowLinearEquiv (A := A) cert : (Fin m → R) →ₗ[R] (Fin m → R)) =
      matRange cert.D := by
  ext y
  constructor
  · rintro ⟨x, hx, hy⟩
    rcases hx with ⟨z, hz⟩
    refine ⟨cert.Vinv *ᵥ z, ?_⟩
    rw [← hy, ← hz]
    rw [matLin, Matrix.mulVecLin_apply]
    calc
      cert.D *ᵥ (cert.Vinv *ᵥ z)
          = (cert.U * A * cert.V) *ᵥ (cert.Vinv *ᵥ z) := by rw [cert.heq]
      _ = cert.U *ᵥ (A *ᵥ z) := by
          rw [Matrix.mulVec_mulVec]
          calc
            (cert.U * A * cert.V * cert.Vinv) *ᵥ z
                = ((cert.U * A) * (cert.V * cert.Vinv)) *ᵥ z := by
                    rw [Matrix.mul_assoc]
            _ = ((cert.U * A) * (1 : Matrix (Fin n) (Fin n) R)) *ᵥ z := by
                rw [cert.hVVinv]
            _ = (cert.U * A) *ᵥ z := by rw [Matrix.mul_one]
            _ = cert.U *ᵥ (A *ᵥ z) := by rw [Matrix.mulVec_mulVec]
  · rintro ⟨z, hz⟩
    refine ⟨A *ᵥ (cert.V *ᵥ z), ?_, ?_⟩
    · exact ⟨cert.V *ᵥ z, rfl⟩
    · rw [← hz]
      rw [matLin, Matrix.mulVecLin_apply]
      calc
        cert.U *ᵥ (A *ᵥ (cert.V *ᵥ z))
            = (cert.U * A * cert.V) *ᵥ z := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        _ = cert.D *ᵥ z := by rw [cert.heq]

/-- An SNF certificate identifies the cokernel of the original matrix map with
the cokernel of its certified diagonal form. -/
noncomputable def cokernelEquivDiagonal (cert : CertificateSNF A) :
    ((Fin m → R) ⧸ matRange A) ≃ₗ[R] ((Fin m → R) ⧸ matRange cert.D) :=
  Submodule.Quotient.equiv (matRange A) (matRange cert.D)
    (rowLinearEquiv (A := A) cert) (map_matRange_eq_diagonal (A := A) cert)

omit [IsDomain R] [IsPrincipalIdealRing R] in
@[simp]
theorem cokernelEquivDiagonal_mk (cert : CertificateSNF A) (x : Fin m → R) :
    cokernelEquivDiagonal (A := A) cert (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cert.U *ᵥ x) :=
  rfl

end CertificateSNF
