import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.List.Basic
import Init.Data.List.Basic
import Cultivar.SNF
import Cultivar.SNFCommand

variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

/-- `orientFace s` is the canonical orientation of a face `s`: its vertices
listed in increasing order with respect to the ambient `LinearOrder` on `ι`.

Use this in the specification/proof layer (incidence and sign checks), not
as a transport encoding for Sage JSON interop. -/
def orientFace (s : Finset ι) : List ι := s.sort (· ≤ ·)

def deletionMatches (σ τ : List ι) : List Nat :=
  (List.range σ.length).filter (fun i => σ.eraseIdx i = τ)

/-- index i if τ = σ with exactly the i-th vertex deleted; none otherwise -/
def deletionIndex (σ τ : List ι) : Option ℕ :=
  match deletionMatches σ τ with
  | [i] => some i
  | _ => none

def signOfIndex (i : Nat) : Int := if i % 2 = 0 then 1 else -1

def boundaryCoeff (σ τ : List ι) : Int :=
  match deletionIndex σ τ with
  | some i => signOfIndex i
  | none   => 0

/-- declarative entry predicate for external matrix verification -/
def isBoundaryEntry (σ τ : List ι) (a : Int) : Prop := a = boundaryCoeff σ τ

/-- Safe list indexing. -/
def getEntry? (d : List (List Int)) (i j : Nat) : Option Int := do
  let row ← d[i]?
  row[j]?

/-- Expected boundary entry from bases at `(i,j)`:
row `i` = codomain simplex `τ`, column `j` = domain simplex `σ`. -/
def expectedEntry? (dom cod : List (List ι)) (i j : Nat) : Option Int := do
  let τ ← cod[i]?
  let σ ← dom[j]?
  pure (boundaryCoeff σ τ)
