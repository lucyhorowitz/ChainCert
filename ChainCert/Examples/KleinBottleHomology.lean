import ChainCert.Examples.Complexes
import ChainCert.Boundary.Verify
import ChainCert.SNF.Tactic
import ChainCert.Homology.Tactic
import ChainCert.Homology.Command

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

#homology kleinBottleFFC, 1

example : True := by
  homology triangleFFC, 1
  trivial

namespace ChainCert
namespace Examples

end Examples
end ChainCert
