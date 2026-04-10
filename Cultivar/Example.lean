import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Cultivar.Basic
import Cultivar.Tactic

def A : Matrix (Fin 3) (Fin 3) ℤ := !![2, 4, 4; -6, 6, 12; 10, 4, 16]

#snf !![2, 4, 4; -6, 6, 12; 10, 4, 16]
#snf A
