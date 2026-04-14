import Cultivar.SNF.Core

/-! # Bridge to Mathlib's SmithNormalForm

This file contains partially-complete work connecting `CertificateSNF` to
`Module.Basis.SmithNormalForm`. Parked for now — may return to this later.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)

section ComputableBasis

variable [DecidableEq R]

def funToFinsupp (x : Fin m → R) : Fin m →₀ R where
  support := Finset.univ.filter fun i => x i ≠ 0
  toFun := x
  mem_support_toFun := by
    intro i
    simp

def funLinearEquivFinsupp : (Fin m → R) ≃ₗ[R] (Fin m →₀ R) where
  toFun := funToFinsupp (R := R) (m := m)
  invFun := fun f i => f i
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro f
    ext i
    rfl
  map_add' := by
    intro x y
    ext i
    rfl
  map_smul' := by
    intro c x
    ext i
    rfl

def finBasisFunComp : Module.Basis (Fin m) R (Fin m → R) :=
  Module.Basis.ofRepr (funLinearEquivFinsupp (R := R) (m := m))

end ComputableBasis

noncomputable def SNF_of_cert [DecidableEq R] (cert : CertificateSNF A) :
    Module.Basis.SmithNormalForm (matRange (A := A)) (Fin m) (cert.r) :=
{
  bM := finBasisFunComp (R := R) (m := m)
  bN := sorry
  f := Fin.castLEEmb (le_trans cert.hr (Nat.min_le_left m n))
  a := fun i => diagEntry cert.D (Fin.castLE cert.hr i)
  snf := sorry
}

omit [IsDomain R] [IsPrincipalIdealRing R] in
@[simp] lemma SNF_of_cert_a [DecidableEq R] (cert : CertificateSNF A) (i : Fin cert.r) :
    (SNF_of_cert (A := A) cert).a i = diagEntry cert.D (Fin.castLE cert.hr i) := rfl
