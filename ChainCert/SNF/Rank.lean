import ChainCert.SNF.Core
import ChainCert.SNF.Verify

/-!
# SNF Rank Readoff

This file is for lemmas that let us read rank information from SNF/diagonal
verification data.

-/

variable {α : Type*} {m n : ℕ}
variable {R : Type*} [CommRing R] [DecidableEq R]

namespace ChainCert
namespace SNF

theorem zeroTailAt_firstZeroDiag_of_verifyDiag (D : Matrix (Fin m) (Fin n) R) :
    verifyDiag D → zeroTailAt D (firstZeroDiag D) := by
  intro h
  exact h.left.right

theorem diagEntry_eq_zero_iff_ge_firstZeroDiag_of_verifyDiag
    (D : Matrix (Fin m) (Fin n) R) (i : Fin (min m n)) :
    verifyDiag D → (diagEntry D i = 0 ↔ firstZeroDiag D ≤ i.val) := by
  intro h
  exact (zeroTailAt_firstZeroDiag_of_verifyDiag D h) i

theorem diagEntry_ne_zero_of_lt_firstZeroDiag_of_verifyDiag
    (D : Matrix (Fin m) (Fin n) R) (i : Fin (min m n)) :
    verifyDiag D → i.val < firstZeroDiag D → diagEntry D i ≠ 0 := by
  intro h hlt hz
  have hiff := (diagEntry_eq_zero_iff_ge_firstZeroDiag_of_verifyDiag D i h)
  have hge : firstZeroDiag D ≤ i.val := hiff.mp hz
  exact (Nat.not_le_of_lt hlt) hge

end SNF
end ChainCert
