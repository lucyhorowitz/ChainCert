import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Cultivar.SNF.Core
import Cultivar.SNF.Command

variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

/- In general I'll care about finite simplicial complexes -/

structure FiniteFacetComplex ι where
  facets : Finset (Finset ι)
  vertex_mem : ∀ v : ι, ∃ f ∈ facets, v ∈ f

abbrev FFC (ι : Type u) := FiniteFacetComplex ι

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

/-- Serialize facets for Sage transport.

Each facet is canonically ordered by vertex (`sort (· ≤ ·)`), then each vertex
is encoded by its index in the global order on `Finset.univ`.

This is an interop encoding (`List (List Nat)`) used for JSON/Sage requests.
For boundary specification and sign conventions inside Lean, prefer
`Cultivar.Boundary.Spec.orientFace`, which stays in vertex type `ι`. -/
def FiniteFacetComplex.toRawFacets (F : FiniteFacetComplex ι) : List (List ℕ) :=
  let order := (Finset.univ : Finset ι).sort (· ≤ ·)
  (F.facets.image (fun f => (f.sort (· ≤ ·)).map (order.idxOf ·))).sort (· ≤ ·)
