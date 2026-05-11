import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Cultivar.SimplicialComplex
import Cultivar.Boundary.Basis
import Cultivar.SNF.Tactic

variable {α : Type*} {m n p : ℕ}
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
                     [DecidableEq R] [SageSerializable R]
variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

/-- `∂ₖ : Cₖ → Cₖ₋₁` -/
def boundaryKInt (X : FFC ι) (k : ℕ) :
    Matrix (Fin (if k = 0 then 0 else cellCount X (k - 1))) (Fin (cellCount X k)) ℤ :=
  match k with
  | 0 => 0
  | n + 1 => by
      simpa using (boundaryMatrix X n)

/-- `∂ₖ : Cₖ → Cₖ₋₁` with coefficients cast from `ℤ` to `R`. -/
def boundaryK (X : FFC ι) (k : ℕ) :
    Matrix (Fin (if k = 0 then 0 else cellCount X (k - 1))) (Fin (cellCount X k)) R :=
  (boundaryKInt X k).map (Int.castRingHom R)


/-- Certificate data for a quotient of the form `ker dₖ / im dₖ₊₁`, independent
of any specific simplicial complex model. -/
structure HomologyQuotientCert
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R) where
  certK : CertificateSNF (A := dk) := by snf dk
  hCC : dk * dk1 = 0 := by native_decide
  M : Matrix (Fin (n - certK.r)) (Fin p) R
  certM : CertificateSNF (A := M) := by snf M

/-- Homology certificate for an `FFC`: boundary data comes from `X`, and the
quotient computation is certified by `HomologyQuotientCert`. -/
structure CertificateHomology (X : FFC ι) (k : ℕ) where
  quotientCert :
    HomologyQuotientCert (R := R)
      (boundaryK (R := R) X k)
      (boundaryK (R := R) X (k + 1))
