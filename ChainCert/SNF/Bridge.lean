import ChainCert.SNF.Core
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Pi

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

/-- The diagonal value at row `i` of an `m × n` matrix: `D i ⟨i, _⟩` if
`i.val < n`, else `0`. For a diagonal matrix, this is the only entry of row `i`
that can be nonzero. -/
def rowDiagVal (D : Matrix (Fin m) (Fin n) R) (i : Fin m) : R :=
  if h : i.val < n then D i ⟨i.val, h⟩ else 0

/-- The submodule of `R` (an ideal) that constrains the `i`-th coordinate of
vectors in `matRange D` when `D` is diagonal: `⟨rowDiagVal D i⟩`. -/
def rowDiagIdeal (D : Matrix (Fin m) (Fin n) R) (i : Fin m) : Submodule R R :=
  Submodule.span R {rowDiagVal D i}

omit [IsDomain R] [IsPrincipalIdealRing R] [DecidableEq R] in
private theorem diagonal_mulVec_eq_rowDiagVal_mul
    {D : Matrix (Fin m) (Fin n) R} (hD : IsDiagonal D)
    (z : Fin n → R) (i : Fin m) :
    (D *ᵥ z) i =
      (if h : i.val < n then z ⟨i.val, h⟩ else 0) * rowDiagVal D i := by
  classical
  rw [Matrix.mulVec, dotProduct]
  by_cases hi : i.val < n
  · rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin n)]
    · simp [rowDiagVal, hi, mul_comm]
    · intro b _ hb
      have hne : i.val ≠ b.val := fun h => hb (Fin.ext h.symm)
      simp [hD i b hne]
    · intro hmem; exact (hmem (Finset.mem_univ _)).elim
  · rw [Finset.sum_eq_zero]
    · simp [rowDiagVal, hi]
    · intro j _
      have hne : i.val ≠ j.val := by
        have hj : j.val < n := j.isLt
        omega
      simp [hD i j hne]

omit [IsDomain R] [IsPrincipalIdealRing R] [DecidableEq R] in
/-- For a diagonal matrix `D`, the range of `D *ᵥ ·` is exactly the set of
vectors whose `i`-th coordinate lies in `⟨D_{ii}⟩` for each `i`. -/
theorem matRange_eq_pi_of_diagonal {D : Matrix (Fin m) (Fin n) R}
    (hD : IsDiagonal D) :
    matRange D = Submodule.pi Set.univ (rowDiagIdeal (R := R) D) := by
  classical
  ext v
  rw [matRange, LinearMap.mem_range]
  rw [Submodule.mem_pi]
  constructor
  · rintro ⟨z, hz⟩ i _
    rw [matLin, Matrix.mulVecLin_apply] at hz
    rw [rowDiagIdeal, Submodule.mem_span_singleton]
    refine ⟨if h : i.val < n then z ⟨i.val, h⟩ else 0, ?_⟩
    show _ • rowDiagVal D i = v i
    rw [smul_eq_mul, ← hz]
    exact (diagonal_mulVec_eq_rowDiagVal_mul hD z i).symm
  · intro hv
    -- For each i, choose c i so that v i = c i * rowDiagVal D i.
    have hchoose : ∀ i : Fin m, ∃ c : R, c • rowDiagVal D i = v i := by
      intro i
      have := hv i (Set.mem_univ _)
      rwa [rowDiagIdeal, Submodule.mem_span_singleton] at this
    choose c hc using hchoose
    refine ⟨fun j => if h : j.val < m then c ⟨j.val, h⟩ else 0, ?_⟩
    rw [matLin, Matrix.mulVecLin_apply]
    ext i
    rw [diagonal_mulVec_eq_rowDiagVal_mul hD]
    by_cases hi : i.val < n
    · have hin : i.val < m := i.isLt
      have hci := hc i
      rw [smul_eq_mul] at hci
      rw [dif_pos hi]
      change (if h : (⟨i.val, hi⟩ : Fin n).val < m then
              c ⟨(⟨i.val, hi⟩ : Fin n).val, h⟩ else 0) *
            rowDiagVal D i = v i
      rw [dif_pos hin]
      have hi_eq : (⟨i.val, hin⟩ : Fin m) = i := Fin.ext rfl
      rw [hi_eq]
      exact hci
    · have hzero : rowDiagVal D i = 0 := by simp [rowDiagVal, hi]
      have hvi : v i = 0 := by
        have hci := hc i
        rw [smul_eq_mul, hzero, mul_zero] at hci
        exact hci.symm
      rw [dif_neg hi, hzero, zero_mul, hvi]

omit [IsDomain R] [IsPrincipalIdealRing R] [DecidableEq R] in
/-- The cokernel of a diagonal `m × n` matrix decomposes as a product over rows
of `R / ⟨D_{ii}⟩` (with `D_{ii} = 0` for rows beyond `min m n`).

For SNF outputs this is the structural decomposition that reads off the
abelian-group factors: a diagonal entry `0` contributes a copy of `R`, a unit
contributes `0`, and a general `d` contributes `R / ⟨d⟩`. -/
noncomputable def diagonalCokernelPiEquiv
    {D : Matrix (Fin m) (Fin n) R} (hD : IsDiagonal D) :
    ((Fin m → R) ⧸ matRange D) ≃ₗ[R]
      ∀ i : Fin m, R ⧸ rowDiagIdeal (R := R) D i :=
  (Submodule.quotEquivOfEq _ _ (matRange_eq_pi_of_diagonal hD)).trans
    (Submodule.quotientPi _)
