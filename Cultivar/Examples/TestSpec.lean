import Cultivar.Boundary.Spec

/-! Small focused checks for `Boundary.Spec`. -/

example : deletionIndex ([0, 1, 2] : List Nat) [1, 2] = some 0 := by
  native_decide

example : deletionIndex ([0, 1, 2] : List Nat) [0, 2] = some 1 := by
  native_decide

example : deletionIndex ([0, 1, 2] : List Nat) [0, 1] = some 2 := by
  native_decide

example : boundaryCoeff ([0, 1, 2] : List Nat) [0, 2] = -1 := by
  native_decide

example : boundaryCoeff ([0, 1, 2] : List Nat) [1, 3] = 0 := by
  native_decide
