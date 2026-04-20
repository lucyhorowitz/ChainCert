import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Data.ZMod.QuotientRing

variable {α : Type*} {m n : ℕ}

def IsDiagonal {m n : ℕ} (M : Matrix (Fin m) (Fin n) α) [Zero α] : Prop :=
  ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ j → M i j = 0

def diagEntry (D : Matrix (Fin m) (Fin n) α) (i : Fin (min m n)) : α :=
  D (Fin.castLE (by omega) i) (Fin.castLE (by omega) i)

instance {α : Type*} {m n : ℕ} [Zero α] [DecidableEq α] (M : Matrix (Fin m) (Fin n) α) :
      Decidable (IsDiagonal M) := by
    unfold IsDiagonal
    infer_instance

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [DecidableEq R]
variable (A : Matrix (Fin m) (Fin n) R)

/-- The first diagonal index where `D` is zero; returns `min m n` if no diagonal entry is zero. -/
def firstZeroDiag [DecidableEq R] (D : Matrix (Fin m) (Fin n) R) : ℕ :=
  let rec go : List (Fin (min m n)) → Option (Fin (min m n))
    | [] => none
    | i :: is => if diagEntry D i = 0 then some i else go is
  match go (List.finRange (min m n)) with
  | some i => i.val
  | none => min m n

/-- The linear map `R^n → R^m` represented by a matrix `A` via `mulVec`. -/
def matLin (A : Matrix (Fin m) (Fin n) R) :
    (Fin n → R) →ₗ[R] (Fin m → R) :=
  Matrix.mulVecLin A

/-- The image submodule of the matrix map `matLin A`. -/
def matRange (A : Matrix (Fin m) (Fin n) R) : Submodule R (Fin m → R) :=
  LinearMap.range (matLin A)

structure CertificateSNF [DecidableEq R] (A : Matrix (Fin m) (Fin n) R) where
  U : Matrix (Fin m) (Fin m) R
  Uinv : Matrix (Fin m) (Fin m) R
  V : Matrix (Fin n) (Fin n) R
  Vinv : Matrix (Fin n) (Fin n) R
  D : Matrix (Fin m) (Fin n) R
  r : ℕ := firstZeroDiag D
  hdiag : IsDiagonal D := by native_decide
  hrank : ∀ (i : Fin (min m n)), diagEntry D i = 0 ↔ r ≤ i.val := by native_decide
  hUUinv : U * Uinv = 1 := by native_decide
  hVVinv : V * Vinv = 1 := by native_decide
  heq : U * A * V = D  := by native_decide
  hdiv : ∀ i j : Fin (min m n), i.val + 1 = j.val →
           diagEntry D i ∣ diagEntry D j := by native_decide

namespace CertificateSNF

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

section QuotientFromCert

/-- The codomain change-of-basis linear equivalence induced by the certified matrix `U`. -/
def codomainLinearEquivOfCert (cert : CertificateSNF A) :
    (Fin m → R) ≃ₗ[R] (Fin m → R) where
  toLinearMap := matLin cert.U
  invFun := matLin cert.Uinv
  left_inv := by
    intro x
    change Matrix.mulVec cert.Uinv (Matrix.mulVec cert.U x) = x
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using
      congrArg (fun M => Matrix.mulVec M x) cert.hUinvU
  right_inv := by
    intro x
    change Matrix.mulVec cert.U (Matrix.mulVec cert.Uinv x) = x
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using
      congrArg (fun M => Matrix.mulVec M x) cert.hUUinv

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Transport of image submodules along the certified codomain equivalence. -/
lemma map_matRange_eq_matRange_D (cert : CertificateSNF A) :
    Submodule.map (codomainLinearEquivOfCert (A := A) cert).toLinearMap (matRange (A := A)) =
      matRange (A := cert.D) := by
  simpa [codomainLinearEquivOfCert] using (matRange_D_eq_map_matRange (A := A) cert).symm

/-- Quotient equivalence induced by a certificate `U * A * V = D`. -/
def quotientLinearEquivOfCert (cert : CertificateSNF A) :
    ((Fin m → R) ⧸ matRange (A := A)) ≃ₗ[R] ((Fin m → R) ⧸ matRange (A := cert.D)) :=
  Submodule.Quotient.equiv
    (matRange (A := A))
    (matRange (A := cert.D))
    (codomainLinearEquivOfCert (A := A) cert)
    (map_matRange_eq_matRange_D (A := A) cert)

end QuotientFromCert

section DiagonalInt

/-- The canonical product submodule corresponding to a diagonal integer family. -/
def diagSubmoduleInt (a : Fin m → ℤ) : Submodule ℤ (Fin m → ℤ) :=
  Submodule.pi Set.univ fun i => (Ideal.span ({a i} : Set ℤ) : Submodule ℤ ℤ)

/-- The image of a diagonal integer matrix is the product of the principal submodules it generates
coordinatewise. -/
theorem matRange_diagonal_eq_diagSubmoduleInt (a : Fin m → ℤ) :
    matRange (A := Matrix.diagonal a) = diagSubmoduleInt (m := m) a := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, rfl⟩
    rw [diagSubmoduleInt, Submodule.mem_pi]
    intro i hi
    rw [Ideal.mem_span_singleton]
    refine ⟨y i, ?_⟩
    simp [matLin, Matrix.mulVec_diagonal]
  · intro hx
    rw [diagSubmoduleInt, Submodule.mem_pi] at hx
    have hx' : ∀ i : Fin m, ∃ t : ℤ, x i = a i * t := by
      intro i
      simpa [Ideal.mem_span_singleton] using hx i (Set.mem_univ i)
    choose y hy using hx'
    refine ⟨y, ?_⟩
    ext i
    simp [matLin, Matrix.mulVec_diagonal, hy i]

/-- Computable decomposition of a quotient by the image of a diagonal integer matrix into a product
of principal ideal quotients. -/
def quotientDiagonalEquivPiSpan (a : Fin m → ℤ) :
    ((Fin m → ℤ) ⧸ matRange (A := Matrix.diagonal a)) ≃ₗ[ℤ]
      (∀ i : Fin m, ℤ ⧸ Ideal.span ({a i} : Set ℤ)) := by
  let e₁ :
      ((Fin m → ℤ) ⧸ matRange (A := Matrix.diagonal a)) ≃ₗ[ℤ]
        ((Fin m → ℤ) ⧸ diagSubmoduleInt (m := m) a) :=
    Submodule.quotEquivOfEq
      (matRange (A := Matrix.diagonal a))
      (diagSubmoduleInt (m := m) a)
      (matRange_diagonal_eq_diagSubmoduleInt (m := m) a)
  let e₂ :
      ((Fin m → ℤ) ⧸ diagSubmoduleInt (m := m) a) ≃ₗ[ℤ]
        (∀ i : Fin m, ℤ ⧸ Ideal.span ({a i} : Set ℤ)) :=
    Submodule.quotientPi (fun i : Fin m => Ideal.span ({a i} : Set ℤ))
  exact e₁.trans e₂

/-- Computable decomposition of a quotient by the image of a diagonal integer matrix into `ZMod`
factors. -/
def quotientDiagonalEquivPiZMod (a : Fin m → ℤ) :
    ((Fin m → ℤ) ⧸ matRange (A := Matrix.diagonal a)) ≃+
      (∀ i : Fin m, ZMod (a i).natAbs) :=
  (quotientDiagonalEquivPiSpan (m := m) a).toAddEquiv.trans
    (AddEquiv.piCongrRight fun i => (Int.quotientSpanEquivZMod (a i)).toAddEquiv)

end DiagonalInt
