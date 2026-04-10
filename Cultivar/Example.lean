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

#diff K, 1

-- TODO: (low priority) write a tactic to automatically generate isRelLowerSet_faces and
-- singleton_mem proofs.
-- isRelLowerSet_faces, if you define the simplicial complex with the facets (max faces) as above,
-- will be the same proof every time, but the number of .imp s will depend on the number of faces.
-- the singleton_mem proof will be literally exactly the same every time.

-- TODO: (high priority) extract the boundary maps from K.
-- Send the face data to Sage (via the existing RPC bridge) and have Sage compute the
-- differentials d₁ : C₁ → C₀ and d₂ : C₂ → C₁ as integer matrices.

-- TODO: prove in Lean that the matrices returned by Sage are the correct differentials.
-- This means showing that each column encodes the boundary of the corresponding simplex
-- with the right signs (alternating sum of face deletions).

-- TODO: use Sage to compute the Smith Normal Form of each differential.
-- We already have #snf for matrices; apply it to d₁ and d₂.

-- TODO: prove that the SNF gives the homology.
-- The diagonal entries of the SNF of dₙ (together with the rank of dₙ₊₁) determine Hₙ(K; ℤ).
-- State and prove the homology groups of K using the certified SNF.
