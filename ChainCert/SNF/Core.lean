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

/-- The first diagonal index where `D` is zero; returns `min m n` if no diagonal entry is zero. -/
def firstZeroDiag {R : Type*} [Zero R] [DecidableEq R] (D : Matrix (Fin m) (Fin n) R) : ℕ :=
  let rec go : List (Fin (min m n)) → Option (Fin (min m n))
    | [] => none
    | i :: is => if diagEntry D i = 0 then some i else go is
  match go (List.finRange (min m n)) with
  | some i => i.val
  | none => min m n

/-- The linear map `R^n → R^m` represented by a matrix `A` via `mulVec`. -/
def matLin {R : Type*} [CommSemiring R] (A : Matrix (Fin m) (Fin n) R) :
    (Fin n → R) →ₗ[R] (Fin m → R) :=
  Matrix.mulVecLin A

/-- The image submodule of the matrix map `matLin A`. -/
def matRange {R : Type*} [CommSemiring R] (A : Matrix (Fin m) (Fin n) R) : Submodule R (Fin m → R) :=
  LinearMap.range (matLin A)

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [DecidableEq R]
variable (A : Matrix (Fin m) (Fin n) R)

structure CertificateSNF [DecidableEq R] (A : Matrix (Fin m) (Fin n) R) where
  U : Matrix (Fin m) (Fin m) R
  Uinv : Matrix (Fin m) (Fin m) R
  V : Matrix (Fin n) (Fin n) R
  Vinv : Matrix (Fin n) (Fin n) R
  D : Matrix (Fin m) (Fin n) R
  r : ℕ := firstZeroDiag D
  hrankCutoff : r = firstZeroDiag D := by native_decide
  hdiag : IsDiagonal D := by native_decide
  hrank : ∀ (i : Fin (min m n)), diagEntry D i = 0 ↔ r ≤ i.val := by native_decide
  hUUinv : U * Uinv = 1 := by native_decide
  hVVinv : V * Vinv = 1 := by native_decide
  heq : U * A * V = D  := by native_decide
  hdiv : ∀ i j : Fin (min m n), i.val + 1 = j.val →
           diagEntry D i ∣ diagEntry D j := by native_decide

namespace CertificateSNF

omit [IsDomain R] [IsPrincipalIdealRing R] in
lemma rankCutoff_le_min (cert : CertificateSNF A) : cert.r ≤ min m n := by
  rw [cert.hrankCutoff]
  unfold firstZeroDiag
  split
  · rename_i i _
    exact Nat.le_of_lt i.isLt
  · rfl

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Right-inverse flip: `Uinv * U = 1` follows from `U * Uinv = 1` over a CommRing. -/
lemma hUinvU (cert : CertificateSNF A) : cert.Uinv * cert.U = 1 :=
  mul_eq_one_comm.mp cert.hUUinv

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Right-inverse flip: `Vinv * V = 1` follows from `V * Vinv = 1` over a CommRing. -/
lemma hVinvV (cert : CertificateSNF A) : cert.Vinv * cert.V = 1 :=
  mul_eq_one_comm.mp cert.hVVinv

omit [IsDomain R] [IsPrincipalIdealRing R] in
lemma hU (cert : CertificateSNF A) : IsUnit cert.U.det :=
  Matrix.isUnit_det_of_left_inverse cert.hUinvU

omit [IsDomain R] [IsPrincipalIdealRing R] in
lemma hV (cert : CertificateSNF A) : IsUnit cert.V.det :=
  Matrix.isUnit_det_of_left_inverse cert.hVinvV

end CertificateSNF
