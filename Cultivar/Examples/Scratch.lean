import Cultivar.Homology.Basic
import Cultivar.SNF.Tactic
import Cultivar.Examples.Complexes

/-!
Scratch notes for the homology certificate work.

Do not build the final workflow by introducing local `M` terms and then running
`snf M`. The current SNF tactic serializes matrices by compiled evaluation, so
it needs closed matrix expressions. A local presentation matrix depending on a
local `certK` produces a free-variable error during evaluation.

The homology tactic should call the reusable SNF backend directly on expressions
it constructs, and should construct the presentation matrix expression itself.
-/

example :
    (boundaryK (R := ℤ) triangleFFC 1) * (boundaryK (R := ℤ) triangleFFC 2) = 0 := by
  native_decide

example : True := by
  snf (boundaryK (R := ℤ) triangleFFC 1) as certK
  trivial
