import Cultivar.SNF.Core
import Cultivar.SNF.Verify
import Cultivar.SageServer
import Cultivar.SageEncode
import Cultivar.SageDecode
import Lean.Elab.Tactic

/-! Plan for `snf` tactic UX and behavior.

Two tactics, sharing all internals (Sage call + Lean-side verification + term
construction) and differing only in the final step:

- `snf A` — workhorse, goal-agnostic. Asserts `cert : CertificateSNF A` into
  the local context. Primary driver inside real proofs.
- `verify_snf` — closes a goal of shape `CertificateSNF A`. Niche. Uses
  `MVarId.assign` instead of `MVarId.assert` at the end.

The rest of this comment describes `snf A`.

`snf A` is goal-agnostic: it can be run regardless of the current goal,
and should enrich the local context with certified SNF data for a concrete matrix `A`.

## Preconditions
- `A` should be actual evaluable matrix data (not a fully symbolic matrix variable).
- Matrix dimensions and entries should be recoverable at elaboration time.

## Core workflow
1. Serialize `A`, call Sage, and obtain `U`, `Uinv`, `D`, `V`, `Vinv`.
2. Decode back into Lean matrices.
3. Verify in Lean before introducing results:
   - diagonal/core checks (shape + zero tail),
   - inverse checks (`U * Uinv = 1`, `V * Vinv = 1`),
   - factorization check (`U * A * V = D`),
   - divisibility chain on diagonal entries.
4. If verification fails, throw a hard error with useful diagnostics.

## What to add to local context
Prefer introducing one main object first:
- `cert : CertificateSNF (A := A)`

Then optionally expose convenient projections/bindings:
- `cert.D`, `cert.r`
- diagonal accessor (e.g. `fun i => diagEntry cert.D i`)
- `cert.heq` (factorization)
- `cert.hdiv` (divisibility chain)

This keeps downstream use (e.g. homology computations) proof-friendly while
still allowing easy extraction of diagonal invariants.

## Suggested options
- default `snf A`: add only `cert`.
- `snf A (diag)`: also add explicit diagonal data binding/list.
- `snf A (verbose)`: print Sage payload + verification diagnostics.
- optional cache control later (`cache` / `no_cache`) if recomputation becomes expensive.

Design preference: center the tactic around `CertificateSNF`; diagonal lists are
derived convenience data, not the primary artifact. -/
