import Mathlib.Data.List.Basic
import Cultivar.SimplicialComplex
import Cultivar.Boundary.Basis
import Cultivar.Boundary.Spec

variable {ι : Type} [DecidableEq ι] [Fintype ι] [LinearOrder ι]

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

def verifyBoundaryData
    (F : FiniteFacetComplex ι) (k : Nat)
    (dom cod : List (List Nat)) (d : List (List Int)) : Prop :=
  validDomainBasis F k dom ∧
  validCodomainBasis F k cod ∧
  verifyBoundaryDataCore dom cod d

def validDomainBasisB
    (F : FiniteFacetComplex ι) (k : Nat) (dom : List (List Nat)) : Bool :=
  decide (validDomainBasis F k dom)

def validCodomainBasisB
    (F : FiniteFacetComplex ι) (k : Nat) (cod : List (List Nat)) : Bool :=
  decide (validCodomainBasis F k cod)

def verifyBoundaryDataCoreB
    (dom cod : List (List Nat)) (d : List (List Int)) : Bool :=
  decide (verifyBoundaryDataCore dom cod d)

instance (F : FiniteFacetComplex ι) (k : Nat)
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

/-- The mismatch flag for a constructed boundary-entry payload is false exactly when
the actual and expected optional entries agree. -/
lemma isMismatchedB_mkMismatch_eq_false_iff
    (dom cod : List (List Nat)) (d : List (List Int)) (i j : Nat) :
    isMismatchedB (mkMismatch dom cod d i j) = false ↔
      getEntry? d i j = expectedEntry? dom cod i j := by
  simp [mkMismatch, isMismatchedB]

/-- A fixed-row column scan returns `none` exactly when all scanned column indices
match the boundary entry specification at that row. -/
lemma firstMismatchInCols_eq_none_iff
    (dom cod : List (List Nat)) (d : List (List Int)) (i : Nat) (js : List Nat) :
    firstMismatchInCols dom cod d i js = none ↔
      ∀ j ∈ js, getEntry? d i j = expectedEntry? dom cod i j := by
  induction js with
  | nil => simp [firstMismatchInCols]
  | cons j js ih =>
      by_cases hm : isMismatchedB (mkMismatch dom cod d i j) = true
      · have hhead : getEntry? d i j ≠ expectedEntry? dom cod i j := by
          intro heq
          have hfalse :
              isMismatchedB (mkMismatch dom cod d i j) = false :=
            (isMismatchedB_mkMismatch_eq_false_iff dom cod d i j).2 heq
          rw [hm] at hfalse
          trivial
        simp [firstMismatchInCols, hm, hhead]
      · have hmfalse : isMismatchedB (mkMismatch dom cod d i j) = false := by
          cases h : isMismatchedB (mkMismatch dom cod d i j) <;> simp [h] at hm ⊢
        have hhead : getEntry? d i j = expectedEntry? dom cod i j :=
          (isMismatchedB_mkMismatch_eq_false_iff dom cod d i j).1 hmfalse
        simp [firstMismatchInCols, hmfalse, ih, hhead, List.mem_cons]

/-- A row scan returns `none` exactly when every scanned row and in-range column pair
matches the boundary entry specification. -/
lemma firstMismatchInRows_eq_none_iff
    (dom cod : List (List Nat)) (d : List (List Int)) (is : List Nat) :
    firstMismatchInRows dom cod d is = none ↔
      ∀ i ∈ is, ∀ j ∈ List.range dom.length, getEntry? d i j = expectedEntry? dom cod i j := by
  induction is with
  | nil =>
      simp [firstMismatchInRows]
  | cons i0 is ih =>
      constructor
      · intro h i' hi' j hj
        rcases List.mem_cons.mp hi' with rfl | hi_tail
        · have hcols : firstMismatchInCols dom cod d i' (List.range dom.length) = none := by
            cases hci : firstMismatchInCols dom cod d i' (List.range dom.length) with
            | none => exact Option.isNone_iff_eq_none.mp rfl
            | some b =>
                simp [firstMismatchInRows, hci] at h
          exact (firstMismatchInCols_eq_none_iff dom cod d i' (List.range dom.length)).1 hcols j hj
        · have hcols : firstMismatchInCols dom cod d i0 (List.range dom.length) = none := by
            cases hci : firstMismatchInCols dom cod d i0 (List.range dom.length) with
            | none => exact Option.isNone_iff_eq_none.mp rfl
            | some b =>
                simp [firstMismatchInRows, hci] at h
          have hrows : firstMismatchInRows dom cod d is = none := by
            simpa [firstMismatchInRows, hcols] using h
          exact (ih.1 hrows) i' hi_tail j hj
      · intro h
        have hcols : firstMismatchInCols dom cod d i0 (List.range dom.length) = none := by
          apply (firstMismatchInCols_eq_none_iff dom cod d i0 (List.range dom.length)).2
          intro j hj
          exact h i0 (by simp) j hj
        have hrows : firstMismatchInRows dom cod d is = none := by
          apply ih.2
          intro i' hi' j hj
          exact h i' (List.mem_cons_of_mem i0 hi') j hj
        simp [firstMismatchInRows, hcols, hrows]

/-- Boolean-form global entry check is equivalent to pointwise agreement on all
indices in the codomain/domain basis rectangle. -/
lemma entriesMatchAll_iff_all_entries_match
    (dom cod : List (List Nat)) (d : List (List Int)) :
    entriesMatchAll (ι := Nat) dom cod d ↔
      ∀ i ∈ List.range cod.length, ∀ j ∈ List.range dom.length,
        getEntry? d i j = expectedEntry? dom cod i j := by
  constructor
  · intro h i hi j hj
    simp_all only [entriesMatchAll, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    apply h i hi j hj
  · intro h
    simp_all only [List.mem_range, entriesMatchAll, List.all_eq_true, decide_eq_true_eq]
    intro i hi j hj
    exact (h i hi j ∘ fun a ↦ hj) dom

/-- Entry-level mismatch search succeeds (`none`) exactly when all in-range entries
satisfy `entriesMatchAll`. -/
theorem firstMismatch_eq_none_iff_entriesMatchAll
    (dom cod : List (List Nat)) (d : List (List Int)) :
    firstMismatch dom cod d = none ↔ entriesMatchAll (ι := Nat) dom cod d := by
  simp_all only [entriesMatchAll_iff_all_entries_match,
    List.mem_range, firstMismatch, firstMismatchInRows_eq_none_iff]

theorem verifyBoundaryDataB_eq_true_iff (F : FiniteFacetComplex ι) (k : Nat) (dom cod : List (List Nat)) (d : List (List Int)) :
    verifyBoundaryDataB F k dom cod d = true ↔ verifyBoundaryData F k dom cod d := by
  constructor
  · exact fun a ↦ of_decide_eq_true a
  · intro h
    exact decide_eq_true h

theorem validDomainBasisB_eq_true_iff (F : FiniteFacetComplex ι) (k : Nat) (dom : List (List Nat)) :
    validDomainBasisB F k dom = true ↔ validDomainBasis F k dom := by
  constructor
  · exact fun a ↦ of_decide_eq_true a
  · intro h
    exact decide_eq_true h

theorem validCodomainBasisB_eq_true_iff (F : FiniteFacetComplex ι) (k : Nat) (cod : List (List Nat)) :
    validCodomainBasisB F k cod = true ↔ validCodomainBasis F k cod := by
  constructor
  · exact fun a ↦ of_decide_eq_true a
  · intro h
    exact decide_eq_true h

theorem verifyBoundaryDataCoreB_eq_true_iff (dom cod : List (List Nat)) (d : List (List Int)) :
    verifyBoundaryDataCoreB dom cod d = true ↔ verifyBoundaryDataCore dom cod d := by
  constructor
  · exact fun a ↦ of_decide_eq_true a
  · intro h
    exact decide_eq_true h

theorem verified_of_check_true
    (F : FiniteFacetComplex ι) (k : Nat)
    (dom cod : List (List Nat)) (d : List (List Int)) :
    verifyBoundaryDataB F k dom cod d = true → verifyBoundaryData F k dom cod d := by
  intro h
  exact (verifyBoundaryDataB_eq_true_iff F k dom cod d).1 h
