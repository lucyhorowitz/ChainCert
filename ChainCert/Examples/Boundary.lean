import ChainCert.Boundary.Tactic
import ChainCert.Boundary.Verify
import ChainCert.Examples.Complexes

/-!
High-value boundary examples:
* one small exact check (`triangleFFC`, dimensions 2 and 1)
* one larger real-world check (`kleinBottleFFC`, dimension 1)
-/

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
  boundary_verify

/-- Negative control: sign error in `∂₂` is rejected. -/
example : ¬ verifyBoundaryData triangleFFC 2
    [[0, 1, 2]]
    [[0, 1], [0, 2], [1, 2]]
    [[1], [1], [1]] := by
  native_decide

/-- Larger `∂₁` verification example on the Klein bottle triangulation. -/
example : verifyBoundaryData kleinBottleFFC 1
    [[0, 1], [0, 2], [0, 3], [0, 5], [0, 6], [0, 7], [1, 2], [1, 3], [1, 4], [1, 6], [1, 8],
     [2, 4], [2, 5], [2, 7], [2, 8], [3, 4], [3, 5], [3, 6], [3, 8], [4, 5], [4, 6], [4, 7],
     [5, 7], [5, 8], [6, 7], [6, 8], [7, 8]]
    [[0], [1], [2], [3], [4], [5], [6], [7], [8]]
    [[-1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 0],
     [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, -1, 0, 0, 0],
     [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -1, -1, 0],
     [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1],
     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1]] := by
  boundary_verify
