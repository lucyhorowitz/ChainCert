import Cultivar.SimplicialComplex
import Cultivar.Boundary.Boundary
import Cultivar.Boundary.Tactic

/-! Shared concrete simplicial complexes used across example/test files. -/

/-- 2-simplex on vertices `0,1,2`. -/
def triangleFFC : FiniteFacetComplex (Fin 3) where
  facets := { {0, 1, 2} }
  vertex_mem := by decide

/-- A small bow-tie-style complex used in project experiments. -/
def bowTieFFC : FiniteFacetComplex (Fin 5) where
  facets := { {0, 1, 2}, {0, 3}, {3, 4}, {0, 4} }
  vertex_mem := by decide

/-- Triangulation of the Klein bottle via a 3×3 grid on the fundamental polygon,
with left–right sides identified in the same direction and top–bottom sides
identified in the opposite direction. 9 vertices, 18 triangular facets. -/
def kleinBottleFFC : FiniteFacetComplex (Fin 9) where
  facets := { {0,1,3}, {1,3,4}, {1,2,4}, {2,4,5}, {0,2,5}, {0,3,5},
              {3,4,6}, {4,6,7}, {4,5,7}, {5,7,8}, {3,5,8}, {3,6,8},
              {0,6,7}, {0,2,7}, {2,7,8}, {1,2,8}, {1,6,8}, {0,1,6} }
  vertex_mem := by decide

#boundary bowTieFFC, 1
#boundary_check bowTieFFC, 1
#boundary_goal bowTieFFC, 1

#boundary_goal kleinBottleFFC, 1

example : verifyBoundaryData triangleFFC 1
    [[0, 1], [0, 2], [1, 2]]
    [[0], [1], [2]]
    [[-1, -1, 0], [1, 0, -1], [0, 1, 1]] := by
  boundary_verify

/- Negative case: one sign flipped in the last row. Uncomment to see the
`boundary_verify` failure message with `firstMismatch` diagnostics. -/
-- example : verifyBoundaryData triangleFFC 1
--     [[0, 1], [0, 2], [1, 2]]
--     [[0], [1], [2]]
--     [[-1, -1, 0], [1, 0, -1], [0, 1, -1]] := by
--   boundary_verify

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
