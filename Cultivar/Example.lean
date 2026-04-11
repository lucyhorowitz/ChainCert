import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Cultivar.SNF
import Cultivar.SNFCommand
import Cultivar.Differential
import Cultivar.SimplicialComplex

-- Testing out the `#snf` command

def A : Matrix (Fin 3) (Fin 3) ℤ := !![2, 4, 4; -6, 6, 12; 10, 4, 16]

#snf !![2, 4, 4; -6, 6, 12; 10, 4, 16]
#snf A

-- Homology of the bow tie:

def K' : FiniteFacetComplex (Fin 5) where
  facets := { {0,1,2}, {0,3}, {3,4}, {0,4} }
  vertex_mem := by decide

def K : AbstractSimplicialComplex (Fin 5) := ASC_of_FFC K'

def n := 1

#diff K', 1

-- TODO: prove in Lean that the matrices returned by Sage are the correct differentials.
-- This means showing that each column encodes the boundary of the corresponding simplex
-- with the right signs (alternating sum of face deletions).

-- TODO: use Sage to compute the Smith Normal Form of each differential.
-- We already have #snf for matrices; apply it to d₁ and d₂.

-- TODO: prove that the SNF gives the homology.
-- The diagonal entries of the SNF of dₙ (together with the rank of dₙ₊₁) determine Hₙ(K; ℤ).
-- State and prove the homology groups of K using the certified SNF.
