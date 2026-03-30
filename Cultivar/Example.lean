import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Cultivar.Basic

def A : Matrix (Fin 3) (Fin 3) ℤ := !![2, 4, 4; -6, 6, 12; 10, 4, 16]
def U : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; -11, -1, 1; -297, -28, 27]
def V : Matrix (Fin 3) (Fin 3) ℤ := !![1, -2, 6; -1, -5, 14; 1, 6, -17]
def D : Matrix (Fin 3) (Fin 3) ℤ := !![2, 0, 0; 0, 2, 0; 0, 0, 156]

lemma hd : IsDiagonal D := by trivial

lemma heq : U * A * V = D := by trivial
