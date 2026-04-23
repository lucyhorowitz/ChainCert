import Cultivar.Examples.Complexes
import Cultivar.Boundary.Verify
import Cultivar.SNF.Tactic

/-!
Outline toward computing simplicial homology of the Klein bottle over `ℤ`.

This file is intentionally staged and contains `sorry` placeholders.
The intended pipeline is:

1. Fix concrete `∂₂ : C₂ → C₁` and `∂₁ : C₁ → C₀` matrices in canonical bases.
2. Certify SNF data for `∂₂` and `∂₁` with `snf`.
3. Read off rank data (Betti/free-rank part).
4. Use SNF/quotient decomposition to identify torsion in `H₁`.

Target result:
* `H₀(Klein; ℤ) ≅ ℤ`
* `H₁(Klein; ℤ) ≅ ℤ ⊕ ℤ/2ℤ`
* `H₂(Klein; ℤ) = 0`
-/

namespace Cultivar
namespace Examples

/-! Stage 1: concrete chain data. -/

/-- `∂₁ : C₁ → C₀` for `kleinBottleFFC` in canonical bases. -/
def kleinBottleD1 : Matrix (Fin 9) (Fin 27) ℤ := by
  -- TODO: replace with the explicit matrix used by `verifyBoundaryData kleinBottleFFC 1`.
  sorry

/-- `∂₂ : C₂ → C₁` for `kleinBottleFFC` in canonical bases. -/
def kleinBottleD2 : Matrix (Fin 27) (Fin 18) ℤ := by
  -- TODO: replace with explicit matrix data for `verifyBoundaryData kleinBottleFFC 2`.
  sorry

/-! Stage 2: SNF certificates for the boundary maps. -/

def certD1 : CertificateSNF kleinBottleD1 := by
  -- TODO: either `snf kleinBottleD1` or provide a decoded certificate payload.
  sorry

def certD2 : CertificateSNF kleinBottleD2 := by
  -- TODO: either `snf kleinBottleD2` or provide a decoded certificate payload.
  sorry

/-! Stage 3: free-rank (Betti) bookkeeping from certified ranks. -/

def beta0 : Nat := 9 - certD1.r
def beta1 : Nat := (27 - certD1.r) - certD2.r
def beta2 : Nat := 18 - certD2.r

theorem kleinBottle_betti_targets :
    beta0 = 1 ∧ beta1 = 1 ∧ beta2 = 0 := by
  -- TODO: prove after `certD1.r` and `certD2.r` are concretely established.
  sorry

/-! Stage 4: full integral homology (torsion in `H₁`). -/

/-- Summary of expected integral homology invariants. -/
structure HomologySummary where
  H0_freeRank : Nat
  H1_freeRank : Nat
  H1_torsionInvariants : List Nat
  H2_freeRank : Nat

def expectedKleinBottleHomology : HomologySummary where
  H0_freeRank := 1
  H1_freeRank := 1
  H1_torsionInvariants := [2]
  H2_freeRank := 0

def computedKleinBottleHomology : HomologySummary := by
  -- TODO: compute from SNF/quotient decomposition for the chain complex.
  sorry

theorem kleinBottle_homology_overZ :
    computedKleinBottleHomology = expectedKleinBottleHomology := by
  -- TODO: final theorem once quotient decomposition is connected end-to-end.
  sorry

end Examples
end Cultivar
