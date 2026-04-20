import Cultivar.SNF.Verify

/-! Focused tests for SNF verification helpers. -/

def diag3 (a b c : Int) : Matrix (Fin 3) (Fin 3) Int := fun i j =>
  if i = j then
    match i.val with
    | 0 => a
    | 1 => b
    | _ => c
  else
    0

def offDiagBad : Matrix (Fin 3) (Fin 3) Int := fun i j =>
  if i.val = 0 ∧ j.val = 1 then 7 else 0

/-- Stage 1: infer the first diagonal index where entries become zero. -/
example : firstZeroDiag (diag3 2 3 0) = 2 := by
  native_decide

example : firstZeroDiag (diag3 2 3 4) = 3 := by
  native_decide

/-- Stage 2: off-diagonal mismatch detection. -/
example :
    (mkOffDiagMismatch (diag3 2 3 0) ⟨0, by decide⟩ ⟨1, by decide⟩).mismatch = false := by
  native_decide

example :
    (mkOffDiagMismatch offDiagBad ⟨0, by decide⟩ ⟨1, by decide⟩).mismatch = true := by
  native_decide

/-- Stage 3: diagonal zero-tail mismatch detection. -/
example :
    (mkZeroTailMismatch (diag3 5 0 0) ⟨2, by decide⟩).mismatch = false := by
  native_decide

example :
    (mkZeroTailMismatch (diag3 5 0 7) ⟨2, by decide⟩).mismatch = true := by
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

/-- Stage 4: a nontrivial `CertificateSNF` using defaults for derived proof/data fields. -/
def certInteresting :
    CertificateSNF (A := swap2 * diag2 2 0) where
  U := swap2
  Uinv := swap2
  V := 1
  Vinv := 1
  D := diag2 2 0

example : certInteresting.r = firstZeroDiag certInteresting.D := by
  rfl

example : certInteresting.r = 1 := by
  native_decide
