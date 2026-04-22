import Cultivar.SNF.Tactic
import Cultivar.SNF.Verify

/-!
High-value SNF examples:
* one `snf` tactic run on a full-rank matrix
* one hand-written nontrivial certificate
-/

def rank4A : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 2, 0, 0;
     0, 1, 3, 0;
     0, 0, 1, 4;
     5, 0, 0, 1]

def certRank4A : CertificateSNF rank4A := by
  snf rank4A
  exact cert

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
