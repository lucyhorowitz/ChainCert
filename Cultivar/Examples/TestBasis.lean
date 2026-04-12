import Cultivar.Boundary.Basis
import Cultivar.Examples.Examples

/-! Focused checks for canonical basis construction/validation. -/

example : validDomainBasis triangleFFC 2 [[0, 1, 2]] := by
  native_decide

example : validCodomainBasis triangleFFC 2 [[0, 1], [0, 2], [1, 2]] := by
  native_decide

example : ¬ validDomainBasis triangleFFC 1 [[0, 2], [0, 1], [1, 2]] := by
  native_decide
