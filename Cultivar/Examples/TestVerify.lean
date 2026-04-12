import Cultivar.Boundary.Verify
import Cultivar.Examples.Examples

/-! End-to-end checks for boundary data verification. -/

/-- Correct `∂₂` data for the triangle in canonical basis order. -/
example : verifyBoundaryData triangleFFC 2
    [[0, 1, 2]]
    [[0, 1], [0, 2], [1, 2]]
    [[1], [-1], [1]] := by
  native_decide

/-- Correct `∂₁` data for the triangle in canonical basis order. -/
example : verifyBoundaryData triangleFFC 1
    [[0, 1], [0, 2], [1, 2]]
    [[0], [1], [2]]
    [[-1, -1, 0], [1, 0, -1], [0, 1, 1]] := by
  native_decide

/-- Negative test: one sign flipped in `∂₂` fails verification. -/
example : ¬ verifyBoundaryData triangleFFC 2
    [[0, 1, 2]]
    [[0, 1], [0, 2], [1, 2]]
    [[1], [1], [1]] := by
  native_decide

/-- Negative test: permuted domain basis fails strict basis validation. -/
example : ¬ verifyBoundaryData triangleFFC 1
    [[0, 2], [0, 1], [1, 2]]
    [[0], [1], [2]]
    [[-1, -1, 0], [1, 0, -1], [0, 1, 1]] := by
  native_decide

/-- Negative test: ragged/wrong-shape matrix fails. -/
example : ¬ verifyBoundaryData triangleFFC 1
    [[0, 1], [0, 2], [1, 2]]
    [[0], [1], [2]]
    [[-1, -1], [1, 0, -1], [0, 1, 1]] := by
  native_decide
