import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ChainCert.SimplicialComplex
import ChainCert.Boundary.Basis
import ChainCert.SNF.Core
import ChainCert.SageEncode

variable {α : Type*} {m n p : ℕ}
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
                     [DecidableEq R] [SageSerializable R]
variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

/-- Number of rows in `∂ₖ : Cₖ → Cₖ₋₁`. -/
@[reducible]
def boundaryRowCount (X : FFC ι) : ℕ → ℕ
  | 0 => 0
  | Nat.succ k => cellCount X k

/-- `∂ₖ : Cₖ → Cₖ₋₁`, with coefficients in `R`. -/
def boundaryK (X : FFC ι) :
    (k : ℕ) → Matrix (Fin (boundaryRowCount X k)) (Fin (cellCount X k)) R
  | 0 => 0
  | Nat.succ n => by
      change Matrix (Fin (cellCount X n)) (Fin (cellCount X (n + 1))) R
      simpa using (boundaryMatrix X n).map (Int.castRingHom R)

/-- Row `r + i` of an `n`-row matrix, viewed as an index in `Fin n`.

The fallback branch is unreachable in the intended use, where `r` is the rank
cutoff of an SNF certificate and hence `r ≤ n`. Keeping this total avoids
threading arithmetic proofs through the certificate type. -/
def bottomRowIndex (r n : ℕ) (i : Fin (n - r)) : Fin n :=
  match n with
  | 0 => Fin.elim0 (i.cast (Nat.zero_sub r))
  | n' + 1 =>
      if h : r + i.val < n' + 1 then
        ⟨r + i.val, h⟩
      else
        0

/-- Keep the rows from `r` onward in an `n × p` matrix. -/
def bottomRows (r : ℕ) (A : Matrix (Fin n) (Fin p) R) :
    Matrix (Fin (n - r)) (Fin p) R :=
  fun i j => A (bottomRowIndex r n i) j

/-- The presentation matrix for `im ∂ₖ₊₁` after changing coordinates by the
SNF column basis for `∂ₖ`; this is the matrix whose cokernel presents homology. -/
def cyclePresentationMatrix
    {dk : Matrix (Fin m) (Fin n) R}
    (certK : CertificateSNF (A := dk))
    (dk1 : Matrix (Fin n) (Fin p) R) :
    Matrix (Fin (n - certK.r)) (Fin p) R :=
  bottomRows certK.r (certK.Vinv * dk1)

/-- Certificate data for a chain quotient of the form `ker dₖ / im dₖ₊₁`,
independent of any specific simplicial complex model. -/
structure ChainQuotientCert
    (dk : Matrix (Fin m) (Fin n) R)
    (dk1 : Matrix (Fin n) (Fin p) R) where
  certK : CertificateSNF (A := dk)
  hCC : dk * dk1 = 0
  M : Matrix (Fin (n - certK.r)) (Fin p) R
  hM : M = cyclePresentationMatrix certK dk1
  certM : CertificateSNF (A := M)

/-- Homology certificate for an `FFC`: boundary data comes from `X`, and the
quotient computation is certified by `ChainQuotientCert`. -/
structure CertificateHomology (X : FFC ι) (k : ℕ) where
  quotientCert :
    ChainQuotientCert (R := R)
      (boundaryK (R := R) X k)
      (boundaryK (R := R) X (k + 1))

namespace CertificateHomology

/-- The matrix whose cokernel presents the certified homology group. -/
def presentationMatrix {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    Matrix
      (Fin (cellCount X k - cert.quotientCert.certK.r))
      (Fin (cellCount X (k + 1)))
      R :=
  cert.quotientCert.M

/-- The SNF certificate for the homology presentation matrix. -/
def presentationCert {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    CertificateSNF (A := presentationMatrix cert) :=
  cert.quotientCert.certM

omit [IsDomain R] [IsPrincipalIdealRing R] [SageSerializable R] in
/-- The boundary maps in a certified homology computation compose to zero. -/
theorem boundary_comp_next {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    boundaryK (R := R) X k * boundaryK (R := R) X (k + 1) = 0 :=
  cert.quotientCert.hCC

omit [IsDomain R] [IsPrincipalIdealRing R] [SageSerializable R] in
/-- The stored presentation matrix is the cycle-presentation matrix. -/
theorem presentationMatrix_eq {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    cert.presentationMatrix =
      cyclePresentationMatrix cert.quotientCert.certK
        (boundaryK (R := R) X (k + 1)) :=
  cert.quotientCert.hM

/-- The homology presentation matrix has a certified Smith normal form. -/
def presentation_has_snf {X : FFC ι} {k : ℕ}
    (cert : CertificateHomology (R := R) X k) :
    CertificateSNF (A := cert.presentationMatrix) :=
  cert.presentationCert

end CertificateHomology
