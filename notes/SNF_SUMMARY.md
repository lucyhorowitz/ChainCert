# Smith Normal Form in Mathlib: Where Things Live

This note summarizes the SNF-related APIs in Mathlib and how they differ by level.

## 1. Core SNF over PIDs (submodule / basis level)

Primary file:

- `.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/PID.lean`

Key definitions/theorems:

- `Module.Basis.SmithNormalForm` (around line 408)
  - A structure packaging SNF data for an inclusion `N ↪ M`:
    - basis `bM` of `M`
    - basis `bN` of `N`
    - embedding `f`
    - coefficients `a`
    - relation `(bN i : M) = a i • bM (f i)`
- `Submodule.exists_smith_normal_form_of_le` (around line 487)
  - Existential theorem: inclusion is diagonal in suitable bases.
- `Submodule.smithNormalForm` (around line 533)
  - Noncomputable packaged version returning SNF structure.

Full-rank refinements (same file):

- `Submodule.smithNormalFormOfRankEq`
- `Submodule.smithNormalFormTopBasis`
- `Submodule.smithNormalFormBotBasis`
- `Submodule.smithNormalFormCoeffs`

These are the main bridge points to structure-theorem-style results.

## 2. Quotient decomposition consequences

Primary file:

- `.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean`

Key theorems:

- `Submodule.quotientEquivPiSpan` (around line 37)
  - For full-rank `N`, decomposes `M ⧸ N` as a product of cyclic PID quotients.
- `Submodule.quotientEquivPiZMod` (around line 83)
  - Over `ℤ`, gives product of `ZMod` factors from SNF coefficients.

This is often the closest API to algebraic-topology applications.

## 3. Integer-specific index consequences

Primary file:

- `.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Int.lean`

Key theorems:

- `Module.Basis.SmithNormalForm.toAddSubgroup_index_eq_pow_mul_prod`
- `Module.Basis.SmithNormalForm.toAddSubgroup_index_ne_zero_iff`

These convert SNF data into subgroup index formulas and finite-index criteria.