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

theorem isDiagonal_of_verifyDiag (D : Matrix (Fin m) (Fin n) R) :
    verifyDiag D → IsDiagonal D := by
  intro h
  exact h.left.left

theorem divChain_of_verifyDiag
    (D : Matrix (Fin m) (Fin n) R) :
    verifyDiag D →
      ∀ i j : Fin (min m n), i.val + 1 = j.val →
        diagEntry D i ∣ diagEntry D j := by
  intro h i j hij
  by_cases hj : j.val < firstZeroDiag D
  · exact h.right i j hij hj
  · have hz : diagEntry D j = 0 :=
      (diagEntry_eq_zero_iff_ge_firstZeroDiag_of_verifyDiag D j h).2
        (Nat.le_of_not_gt hj)
    rw [hz]
    exact dvd_zero (diagEntry D i)

namespace CertificateSNF

def ofVerifySNF
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [DecidableEq R]
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R)
    (U Uinv : Matrix (Fin m) (Fin m) R)
    (V Vinv : Matrix (Fin n) (Fin n) R)
    (D : Matrix (Fin m) (Fin n) R) :
    verifySNF A U Uinv V Vinv D → CertificateSNF A := by
  intro h
  refine
    { U := U
      Uinv := Uinv
      V := V
      Vinv := Vinv
      D := D
      r := firstZeroDiag D
      hrankCutoff := rfl
      hdiag := isDiagonal_of_verifyDiag D h.left
      hrank := ?_
      hUUinv := h.right.left
      hVVinv := h.right.right.left
      heq := h.right.right.right
      hdiv := h.left.right }
  intro i
  exact diagEntry_eq_zero_iff_ge_firstZeroDiag_of_verifyDiag D i h.left

end CertificateSNF

end SNF
end ChainCert
