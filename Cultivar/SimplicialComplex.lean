import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Cultivar.SNF
import Cultivar.SNFCommand

variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

/- In general I'll care about finite simplicial complexes -/

structure FiniteFacetComplex ι where
  facets : Finset (Finset ι)
  vertex_mem : ∀ v : ι, ∃ f ∈ facets, v ∈ f

def ASC_of_FFC (F : FiniteFacetComplex ι) : AbstractSimplicialComplex ι where
  faces := { s | s.Nonempty ∧ ∃ f ∈ F.facets, s ⊆ f }
  isRelLowerSet_faces := by
    intro s ⟨hne, hfacet⟩
    constructor
    · exact hne
    · intro t hts htne
      constructor
      · exact htne
      · obtain ⟨f, hf1, hf2⟩ := hfacet
        use f
        constructor
        · exact hf1
        · exact Finset.coe_subset.mp fun ⦃a⦄ a_1 ↦ hf2 (hts a_1)
  singleton_mem v := by
    refine ⟨Finset.singleton_nonempty _, ?_⟩
    obtain ⟨f, hf, hv⟩ := F.vertex_mem v
    exact ⟨f, hf,Finset.singleton_subset_iff.mpr hv⟩

def FiniteFacetComplex.toRawFacets (F : FiniteFacetComplex ι) : List (List ℕ) :=
  let order := (Finset.univ : Finset ι).sort (· ≤ ·)
  (F.facets.image (fun f => (f.sort (· ≤ ·)).map (order.idxOf ·))).sort (· ≤ ·)
