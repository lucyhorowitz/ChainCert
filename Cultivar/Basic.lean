import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

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

structure CertificateSNF (A : Matrix (Fin m) (Fin n) R) where
  U : Matrix (Fin m) (Fin m) R
  V : Matrix (Fin n) (Fin n) R
  D : Matrix (Fin m) (Fin n) R
  hD : IsDiagonal D
  hU : IsUnit U.det
  hV : IsUnit V.det
  heq : U * A * V = D
  hdiv : ∀ (i : Fin (min m n)) (hi : i.val + 1 < min m n), diagEntry D i ∣ diagEntry D ⟨i.val + 1, by omega⟩
