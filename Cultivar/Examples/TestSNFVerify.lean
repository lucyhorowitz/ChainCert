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

example : firstZeroDiag (diag3 2 3 0) = 2 := by
  native_decide

example : firstZeroDiag (diag3 2 3 4) = 3 := by
  native_decide

example :
    (mkOffDiagMismatch (diag3 2 3 0) ⟨0, by decide⟩ ⟨1, by decide⟩).mismatch = false := by
  native_decide

example :
    (mkOffDiagMismatch offDiagBad ⟨0, by decide⟩ ⟨1, by decide⟩).mismatch = true := by
  native_decide

example :
    (mkZeroTailMismatch (diag3 5 0 0) ⟨2, by decide⟩).mismatch = false := by
  native_decide

example :
    (mkZeroTailMismatch (diag3 5 0 7) ⟨2, by decide⟩).mismatch = true := by
  native_decide
