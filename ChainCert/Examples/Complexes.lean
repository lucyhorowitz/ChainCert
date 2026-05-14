import ChainCert.SimplicialComplex

/-!
Representative finite facet complexes used by example modules.
-/

/-- 2-simplex on vertices `0,1,2`. -/
def triangleFFC : FiniteFacetComplex (Fin 3) where
  facets := { {0, 1, 2} }
  vertex_mem := by decide

/-- A small bow-tie-style complex used in project experiments. -/
def bowTieFFC : FiniteFacetComplex (Fin 5) where
  facets := { {0, 1, 2}, {0, 3}, {3, 4}, {0, 4} }
  vertex_mem := by decide

/-- Triangulation of the Klein bottle via a 3×3 grid on the fundamental polygon. -/
def kleinBottleFFC : FiniteFacetComplex (Fin 9) where
  facets := { {0,1,3}, {1,3,4}, {1,2,4}, {2,4,5}, {0,2,5}, {0,3,5},
              {3,4,6}, {4,6,7}, {4,5,7}, {5,7,8}, {3,5,8}, {3,6,8},
              {0,6,7}, {0,2,7}, {2,7,8}, {1,2,8}, {1,6,8}, {0,1,6} }
  vertex_mem := by decide
