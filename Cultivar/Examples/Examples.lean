import Cultivar.SimplicialComplex
import Cultivar.Differential

/-! Shared concrete simplicial complexes used across example/test files. -/

/-- 2-simplex on vertices `0,1,2`. -/
def triangleFFC : FiniteFacetComplex (Fin 3) where
  facets := { {0, 1, 2} }
  vertex_mem := by decide

/-- A small bow-tie-style complex used in project experiments. -/
def bowTieFFC : FiniteFacetComplex (Fin 5) where
  facets := { {0, 1, 2}, {0, 3}, {3, 4}, {0, 4} }
  vertex_mem := by decide

#diff bowTieFFC, 1
