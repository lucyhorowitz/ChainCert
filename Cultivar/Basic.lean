import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

variable {α : Type*} {m n : ℕ}

def IsDiagonal {m n : ℕ} (M : Matrix (Fin m) (Fin n) α) [Zero α] : Prop :=
  ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → M i j = 0

def diagEntry (D : Matrix (Fin m) (Fin n) α) (i : Fin (min m n)) : α :=
  D (Fin.castLE (by omega) i) (Fin.castLE (by omega) i)

instance {α : Type*} {m n : ℕ} [Zero α] [DecidableEq α] (M : Matrix (Fin m) (Fin n) α) :
      Decidable (IsDiagonal M) := by
    unfold IsDiagonal
    infer_instance

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (A : Matrix (Fin m) (Fin n) R)

/-- The linear map `R^n → R^m` represented by a matrix `A` via `mulVec`. -/
def matLin (A : Matrix (Fin m) (Fin n) R) :
    (Fin n → R) →ₗ[R] (Fin m → R) :=
  Matrix.mulVecLin A

/-- The image submodule of the matrix map `matLin A`. -/
def matRange (A : Matrix (Fin m) (Fin n) R) : Submodule R (Fin m → R) :=
  LinearMap.range (matLin A)

structure CertificateSNF (A : Matrix (Fin m) (Fin n) R) where
  U : Matrix (Fin m) (Fin m) R
  Uinv : Matrix (Fin m) (Fin m) R
  V : Matrix (Fin n) (Fin n) R
  Vinv : Matrix (Fin n) (Fin n) R
  D : Matrix (Fin m) (Fin n) R
  r : ℕ
  hr : r ≤ min m n
  hdiag : IsDiagonal D
  hrank : ∀ (i : Fin (min m n)), diagEntry D i = 0 ↔ r ≤ i.val
  hUUinv : U * Uinv = 1
  hUinvU : Uinv * U = 1
  hVVinv : V * Vinv = 1
  hVinvV : Vinv * V = 1
  heq : U * A * V = D
  hdiv :
    ∀ (i : Fin (min m n)) (hi : i.val + 1 < min m n),
      diagEntry D i ∣ diagEntry D ⟨i.val + 1, by omega⟩

namespace CertificateSNF

omit [IsDomain R] [IsPrincipalIdealRing R] in
lemma hU (cert : CertificateSNF A) : IsUnit cert.U.det :=
  Matrix.isUnit_det_of_left_inverse cert.hUinvU

omit [IsDomain R] [IsPrincipalIdealRing R] in
lemma hV (cert : CertificateSNF A) : IsUnit cert.V.det :=
  Matrix.isUnit_det_of_left_inverse cert.hVinvV

end CertificateSNF

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- A certificate `U * A * V = D` identifies the image submodule of `D` as the image
of the image submodule of `A` under the codomain change-of-basis map induced by `U`.

Concretely, this proves:
`range(D) = U(range(A))` as submodules of `Fin m → R`. -/
theorem matRange_D_eq_map_matRange (cert : CertificateSNF A) :
    matRange (A := cert.D) =
      Submodule.map (matLin (A := cert.U)) (matRange (A := A)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨(matLin (A := A)) ((matLin (A := cert.V)) x), ?_, ?_⟩
    · exact ⟨(matLin (A := cert.V)) x, rfl⟩
    · change
        Matrix.mulVec cert.U (Matrix.mulVec A (Matrix.mulVec cert.V x)) =
          Matrix.mulVec cert.D x
      rw [← cert.heq]
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, rfl⟩
    refine ⟨(matLin (A := cert.Vinv)) x, ?_⟩
    change
      Matrix.mulVec cert.D (Matrix.mulVec cert.Vinv x) =
        Matrix.mulVec cert.U (Matrix.mulVec A x)
    rw [← cert.heq]
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, cert.hVVinv]

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- The converse transport of `matRange_D_eq_map_matRange`: the image submodule of `A`
is the image of the image submodule of `D` under the codomain change-of-basis map
induced by `Uinv`. Concretely:
`range(A) = Uinv(range(D))` as submodules of `Fin m → R`. -/
theorem matRange_A_eq_map_matRange (cert : CertificateSNF A) :
  matRange (A := A) = Submodule.map (matLin cert.Uinv) (matRange (A := cert.D)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨(matLin (A := cert.U)) (matLin ( A := A) x), ?_, ?_⟩
    · refine ⟨(matLin (A := cert.Vinv)) x, ?_⟩
      simp [matLin, ← cert.heq, Matrix.mul_assoc, cert.hVVinv]
    · simp [matLin, ← Matrix.mul_assoc, cert.hUinvU, Matrix.mulVec_mulVec]
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, rfl⟩
    refine ⟨(matLin (A := cert.V)) x, ?_⟩
    simp [matLin, Matrix.mulVec_mulVec, ← cert.heq, ← Matrix.mul_assoc, cert.hUinvU]
