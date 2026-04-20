import Cultivar.SNF.Core
import Cultivar.SNF.Verify

/-!
# SNF Rank Readoff

This file is for lemmas that let us read rank information from SNF/diagonal
verification data.

Scope for this file:
- Bridge from diagonal-shape verification (`verifyDiagonalCore`) to rank facts.
- Keep statements proof-level and reusable by tactics/commands.
- Avoid tactic implementation details (those belong in `Cultivar/SNF/Tactic.lean`).

Suggested build order:
1. Define the rank witness you want to expose (typically `firstZeroDiag D`).
2. Prove local helper lemmas about diagonal entries and the zero-tail predicate.
3. Prove a main readoff theorem from `verifyDiagonalCore D`.
4. Add corollaries for the exact goal shapes your automation should close.
-/

namespace Cultivar
namespace SNF

/- TODO: rank-readoff lemmas go here. -/

end SNF
end Cultivar
