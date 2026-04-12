import Mathlib.Data.List.Basic
import Cultivar.SimplicialComplex
import Cultivar.Boundary.Basis
import Cultivar.Boundary.Spec

variable {ι : Type} [DecidableEq ι]

/-- Matrix-shape sanity check for matrix-as-data representation:
`d` should have one row per codomain simplex and one column per domain simplex. -/
def shapeOK (dom cod : List (List ι)) (d : List (List Int)) : Prop :=
  d.length = cod.length ∧ d.Forall (fun row => row.length = dom.length)

instance (dom cod : List (List ι)) (d : List (List Int)) : Decidable (shapeOK dom cod d) := by
  unfold shapeOK
  infer_instance

/-- Pointwise entry check at `(i,j)`: row `i` corresponds to codomain simplex,
column `j` to domain simplex. -/
def entryMatches (dom cod : List (List ι)) (d : List (List Int)) (i j : Nat) : Prop :=
  getEntry? d i j = expectedEntry? dom cod i j

instance (dom cod : List (List ι)) (d : List (List Int)) (i j : Nat) :
    Decidable (entryMatches dom cod d i j) := by
  unfold entryMatches
  infer_instance

/-- All in-bounds entries satisfy the boundary specification. -/
def entriesMatchAll (dom cod : List (List ι)) (d : List (List Int)) : Prop :=
  ((List.range cod.length).all (fun i =>
    (List.range dom.length).all (fun j => decide (entryMatches dom cod d i j)))) = true

instance (dom cod : List (List ι)) (d : List (List Int)) :
    Decidable (entriesMatchAll dom cod d) := by
  unfold entriesMatchAll
  infer_instance

/-- Core verifier predicate (shape + entry rule) for external boundary data.

Basis-canonicality checks are intentionally separate and should be conjoined in
the final `verifyBoundaryData` once `Basis.lean` provides:
- `validDomainBasis K k dom`
- `validCodomainBasis K k cod`. -/
def verifyBoundaryDataCore (dom cod : List (List ι)) (d : List (List Int)) : Prop :=
  shapeOK dom cod d ∧ entriesMatchAll dom cod d

instance (dom cod : List (List ι)) (d : List (List Int)) :
    Decidable (verifyBoundaryDataCore dom cod d) := by
  unfold verifyBoundaryDataCore
  infer_instance

def verifyBoundaryData [Fintype ι] [LinearOrder ι]
    (F : FiniteFacetComplex ι) (k : Nat)
    (dom cod : List (List Nat)) (d : List (List Int)) : Prop :=
  validDomainBasis F k dom ∧
  validCodomainBasis F k cod ∧
  verifyBoundaryDataCore dom cod d

instance [Fintype ι] [LinearOrder ι] (F : FiniteFacetComplex ι) (k : Nat)
    (dom cod : List (List Nat)) (d : List (List Int)) :
    Decidable (verifyBoundaryData F k dom cod d) := by
  unfold verifyBoundaryData
  infer_instance

def verifyBoundaryDataB [Fintype ι] [LinearOrder ι]
    (F : FiniteFacetComplex ι) (k : Nat)
    (dom cod : List (List Nat)) (d : List (List Int)) : Bool :=
  decide (verifyBoundaryData F k dom cod d)

structure BoundaryMismatch where
  i : Nat
  j : Nat
  actual : Option Int
  expected : Option Int
  τ : Option (List Nat)
  σ : Option (List Nat)

def isMismatched (b : BoundaryMismatch) : Prop := b.actual ≠ b.expected

def isMismatchedB (b : BoundaryMismatch) : Bool :=
  decide (b.actual ≠ b.expected)

def mkMismatch (dom cod : List (List Nat)) (d : List (List Int)) (i j : Nat) : BoundaryMismatch where
  i := i
  j := j
  actual := getEntry? d i j
  expected := expectedEntry? dom cod i j
  τ := cod[i]?
  σ := dom[j]?

def firstMismatchInCols (dom cod : List (List Nat)) (d : List (List Int)) (i : Nat) :
    List Nat → Option BoundaryMismatch
  | [] => none
  | j :: js =>
      let b := mkMismatch dom cod d i j
      if isMismatchedB b then some b else firstMismatchInCols dom cod d i js

def firstMismatchInRows (dom cod : List (List Nat)) (d : List (List Int)) :
    List Nat → Option BoundaryMismatch
  | [] => none
  | i :: is =>
      match firstMismatchInCols dom cod d i (List.range dom.length) with
      | some b => some b
      | none => firstMismatchInRows dom cod d is

/-- Return the first entry-level mismatch (row-major over codomain/ domain
bases) between actual and expected boundary coefficients, if any. -/
def firstMismatch (dom cod : List (List Nat)) (d : List (List Int)) : Option BoundaryMismatch :=
  firstMismatchInRows dom cod d (List.range cod.length)
