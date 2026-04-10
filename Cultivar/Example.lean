import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Cultivar.Basic
import Cultivar.Tactic

def A : Matrix (Fin 3) (Fin 3) ℤ := !![2, 4, 4; -6, 6, 12; 10, 4, 16]

#snf !![2, 4, 4; -6, 6, 12; 10, 4, 16]
#snf A

#eval show IO _ from do
  let (U, D, V) ← callSageRpc A
  IO.println s!"U = {matStringList U}"
  IO.println s!"D = {matStringList D}"
  IO.println s!"V = {matStringList V}"

def U : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; -11, -1, 1; -297, -28, 27]
def Uinv : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 27, -1; 11, 28, -1]
def V : Matrix (Fin 3) (Fin 3) ℤ := !![1, -2, 6; -1, -5, 14; 1, 6, -17]
def Vinv : Matrix (Fin 3) (Fin 3) ℤ := !![1, 2, 2; -3, -23, -20; -1, -8, -7]
def D : Matrix (Fin 3) (Fin 3) ℤ := !![2, 0, 0; 0, 2, 0; 0, 0, 156]

def certA : CertificateSNF A where
  U := U
  Uinv := Uinv
  V := V
  Vinv := Vinv
  D := D
  r := 3
  hr := by omega
  hdiag := by trivial
  hrank := by
    intro i
    fin_cases i <;> simp [diagEntry, D]
  hUUinv := by native_decide
  hUinvU := by native_decide
  hVVinv := by native_decide
  hVinvV := by native_decide
  heq := by native_decide
  hdiv := by
    intro i hi
    fin_cases i <;> simp_all [diagEntry, D]

lemma hd : IsDiagonal D := by trivial

lemma heq : U * A * V = D := by trivial

def dVec : Fin 3 → ℤ := ![2, 2, 156]

lemma D_eq_diagonal_dVec : D = Matrix.diagonal dVec := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D, dVec]

def piZModEquivTriple :
    (∀ i : Fin 3, ZMod (dVec i).natAbs) ≃+ (ZMod 2 × ZMod 2 × ZMod 156) where
  toFun := fun x =>
    (by simpa [dVec] using x 0, by simpa [dVec] using x 1, by simpa [dVec] using x 2)
  invFun := fun t =>
    Fin.cons
      (by simpa [dVec] using t.1)
      (Fin.cons
        (by simpa [dVec] using t.2.1)
        (Fin.cons
          (by simpa [dVec] using t.2.2)
          finZeroElim))
  left_inv := by
    intro x
    ext i
    fin_cases i <;> rfl
  right_inv := by
    intro t
    rcases t with ⟨a, b, c⟩
    rfl
  map_add' := by
    intro x y
    ext <;> rfl

/-- Certificate-driven decomposition to `Π i, ZMod dᵢ` for the Wikipedia example. -/
def quotient_imA_equiv_piZMod
    (cert : CertificateSNF A)
    (hD : cert.D = D) :
    ((Fin 3 → ℤ) ⧸ matRange (A := A)) ≃+ (∀ i : Fin 3, ZMod (dVec i).natAbs) := by
  let e₁ :
      ((Fin 3 → ℤ) ⧸ matRange (A := A)) ≃+
        ((Fin 3 → ℤ) ⧸ matRange (A := cert.D)) :=
    (quotientLinearEquivOfCert (A := A) cert).toAddEquiv
  let e₂ :
      ((Fin 3 → ℤ) ⧸ matRange (A := cert.D)) ≃+
        ((Fin 3 → ℤ) ⧸ matRange (A := D)) :=
    (Submodule.quotEquivOfEq
      (matRange (A := cert.D))
      (matRange (A := D))
      (by simp [hD])).toAddEquiv
  let e₃ :
      ((Fin 3 → ℤ) ⧸ matRange (A := D)) ≃+
        ((Fin 3 → ℤ) ⧸ matRange (A := Matrix.diagonal dVec)) :=
    (Submodule.quotEquivOfEq
      (matRange (A := D))
      (matRange (A := Matrix.diagonal dVec))
      (by simp [D_eq_diagonal_dVec])).toAddEquiv
  let e₄ :
      ((Fin 3 → ℤ) ⧸ matRange (A := Matrix.diagonal dVec)) ≃+
        (∀ i : Fin 3, ZMod (dVec i).natAbs) :=
    quotientDiagonalEquivPiZMod (m := 3) dVec
  exact e₁.trans (e₂.trans (e₃.trans e₄))

/-- Quotient decomposition for the Wikipedia example matrix, using a certified SNF diagonal.

This is the concrete `ℤ^3 / im(A)` decomposition corresponding to diagonal entries
`(2, 2, 156)`. -/
def quotient_imA_equiv_zmod2_zmod2_zmod156
    (cert : CertificateSNF A)
    (hD : cert.D = D) :
    ((Fin 3 → ℤ) ⧸ matRange (A := A)) ≃+ (ZMod 2 × ZMod 2 × ZMod 156) :=
  (quotient_imA_equiv_piZMod cert hD).trans piZModEquivTriple
