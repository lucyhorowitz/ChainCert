import ChainCert.SNF.Tactic
import ChainCert.SNF.Verify
import ChainCert.Homology.Basic
import ChainCert.Examples.Complexes

/-!
High-value SNF examples:
* one `snf` tactic run on a full-rank matrix
* one `snf` tactic run on a rank-deficient matrix
* one `snf` tactic run on an FFC boundary matrix
* one hand-written nontrivial certificate
-/

def rank4A : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 2, 0, 0;
     0, 1, 3, 0;
     0, 0, 1, 4;
     5, 0, 0, 1]

def certRank4A : CertificateSNF rank4A := by
  snf rank4A as h
  exact h

example : certRank4A.r = 4 := by
  native_decide

/-- A nontrivial `2 × 2` swap matrix. -/
def swap2 : Matrix (Fin 2) (Fin 2) Int := fun i j =>
  if i.val = j.val then 0 else 1

/-- A `2 × 2` diagonal matrix with entries `(a,b)`. -/
def diag2 (a b : Int) : Matrix (Fin 2) (Fin 2) Int := fun i j =>
  if i = j then
    match i.val with
    | 0 => a
    | _ => b
  else
    0

/-- A rank-deficient matrix checked through the Sage-backed `snf` tactic. -/
def rankDeficient2 : Matrix (Fin 2) (Fin 2) Int :=
  diag2 2 0

def certRankDeficient2 : CertificateSNF rankDeficient2 := by
  snf rankDeficient2 as h
  exact h

example : certRankDeficient2.r = 1 := by
  native_decide

/-- SNF on the actual boundary matrix shape used by homology certificates. -/
def certTriangleBoundary1 :
    CertificateSNF (boundaryK (R := ℤ) triangleFFC 1) := by
  snf (boundaryK (R := ℤ) triangleFFC 1) as h
  exact h

example : certTriangleBoundary1.r = 2 := by
  native_decide

/-- SNF on a rectangular boundary matrix from the same complex. -/
def certTriangleBoundary2 :
    CertificateSNF (boundaryK (R := ℤ) triangleFFC 2) := by
  snf (boundaryK (R := ℤ) triangleFFC 2) as h
  exact h

example : certTriangleBoundary2.r = 1 := by
  native_decide

/-- A hand-written certificate for a simple conjugation-to-diagonal case. -/
def certInteresting :
    CertificateSNF (A := swap2 * diag2 2 0) where
  U := swap2
  Uinv := swap2
  V := 1
  Vinv := 1
  D := diag2 2 0

example : certInteresting.r = 1 := by
  native_decide
