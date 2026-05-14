import ChainCert.SNF.Core
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

variable {α : Type*} {m n : ℕ}
variable {R : Type*} [CommRing R] [DecidableEq R]

/-!
# SNF Verification Layers

This file is organized in layers:

1. `DiagShape`: diagonal-shape diagnostics, predicates, and correctness lemmas.
2. `DiagDivisibility`: diagonal divisibility predicate.
3. `DiagAssemble`: composition into `verifyDiag`.
4. `SNFPayload`: full payload predicate `verifySNF`.
-/

section DiagShape

/-! Mismatch catching, for diagnostics -/

/-- Diagnostic payload for an off-diagonal check at entry `(i,j)`. -/
structure OffDiagMismatch (m n : ℕ) (R : Type*) where
  i : ℕ
  j : ℕ
  actualZero : Bool
  expectedZero : Bool
  mismatch : Bool
  deriving Repr

/-- Compute the off-diagonal diagnostic payload for entry `(i,j)`. -/
def mkOffDiagMismatch (D : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    OffDiagMismatch m n R :=
  let actualZero := decide (D i j = 0)
  let expectedZero := true
  { i := i.val
    j := j.val
    actualZero := actualZero
    expectedZero := expectedZero
    mismatch := decide (actualZero != expectedZero) }

/-- Diagnostic payload for a diagonal zero-tail check at index `k`. -/
structure ZeroTailDiagMismatch (m n : ℕ) (R : Type*) where
  k : Nat
  cutoff : Nat
  actualZero : Bool
  expectedZero : Bool
  mismatch : Bool
  deriving Repr

/-- Compute the diagonal zero-tail diagnostic payload for diagonal index `k`. -/
def mkZeroTailMismatch (D : Matrix (Fin m) (Fin n) R) (k : Fin (min m n)) :
    ZeroTailDiagMismatch m n R :=
  let cutoff := firstZeroDiag D
  let i : Fin m := Fin.castLE (Nat.min_le_left m n) k
  let j : Fin n := Fin.castLE (Nat.min_le_right m n) k
  let actualZero := decide (D i j = 0)
  let expectedZero := decide (cutoff ≤ k.val)
  { k := k.val
    cutoff := cutoff
    actualZero := actualZero
    expectedZero := expectedZero
    mismatch := decide (actualZero != expectedZero) }

/-- Scan a fixed row `i` and return the first off-diagonal mismatch in that row, if any. -/
def firstOffDiagInCols (D : Matrix (Fin m) (Fin n) R) (i : Fin m) :
    List (Fin n) → Option (OffDiagMismatch m n R)
  | [] => none
  | j :: js =>
      if i.val ≠ j.val then
        let b := mkOffDiagMismatch D i j
        if b.mismatch then some b else firstOffDiagInCols D i js
      else
        firstOffDiagInCols D i js

/-- Scan rows in order and return the first off-diagonal mismatch, if any. -/
def firstOffDiagInRows (D : Matrix (Fin m) (Fin n) R) :
    List (Fin m) → Option (OffDiagMismatch m n R)
  | [] => none
  | i :: is =>
      match firstOffDiagInCols D i (List.finRange n) with
      | some b => some b
      | none => firstOffDiagInRows D is

/-- Return the first off-diagonal mismatch in row-major order, if any. -/
def firstOffDiagMismatch (D : Matrix (Fin m) (Fin n) R) :
    Option (OffDiagMismatch m n R) :=
  firstOffDiagInRows D (List.finRange m)

/-- Return the first diagonal zero-tail mismatch (in increasing diagonal index), if any. -/
def firstZeroTailMismatch (D : Matrix (Fin m) (Fin n) R) :
    Option (ZeroTailDiagMismatch m n R) :=
  let rec go : List (Fin (min m n)) → Option (ZeroTailDiagMismatch m n R)
    | [] => none
    | k :: ks =>
        let b := mkZeroTailMismatch D k
        if b.mismatch then some b else go ks
  go (List.finRange (min m n))


/-- Sum type for diagonal-shape mismatches (off-diagonal or zero-tail). -/
inductive DiagMismatch (m n : ℕ) (R : Type*) where
  | offDiag (b : OffDiagMismatch m n R)
  | zeroTail (b : ZeroTailDiagMismatch m n R)
  deriving Repr

/-- Return the first diagonal-shape mismatch, prioritizing off-diagonal failures. -/
def firstDiagMismatch (D : Matrix (Fin m) (Fin n) R) :
    Option (DiagMismatch m n R) :=
  match firstOffDiagMismatch D with
  | some b => some (.offDiag b)
  | none =>
      match firstZeroTailMismatch D with
      | some b => some (.zeroTail b)
      | none => none

/-! Core diagonal-shape verification lemmas. -/

/-- Predicate asserting all off-diagonal entries are zero. -/
def offDiagsZero (D : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ i : Fin m, ∀ j : Fin n, i.val ≠ j.val → D i j = 0

instance (D : Matrix (Fin m) (Fin n) R) : Decidable (offDiagsZero D) := by
  unfold offDiagsZero
  infer_instance

/-- Predicate asserting diagonal entries are zero exactly from cutoff `r` onward. -/
def zeroTailAt (D : Matrix (Fin m) (Fin n) R) (r : ℕ) : Prop :=
  ∀ k : Fin (min m n), (diagEntry D k = 0 ↔ r ≤ k.val)

instance (D : Matrix (Fin m) (Fin n) R) (r : ℕ) : Decidable (zeroTailAt D r) := by
  unfold zeroTailAt
  infer_instance

/-- Core diagonal-shape verifier: off-diagonal zeros plus zero-tail at the inferred cutoff. -/
def verifyDiagonalCore (D : Matrix (Fin m) (Fin n) R) : Prop :=
  offDiagsZero D ∧ zeroTailAt D (firstZeroDiag D)

instance (D : Matrix (Fin m) (Fin n) R) : Decidable (verifyDiagonalCore D) := by
  unfold verifyDiagonalCore
  infer_instance

/-- Boolean checker form of `verifyDiagonalCore`. -/
def verifyDiagonalCoreB (D : Matrix (Fin m) (Fin n) R) : Bool :=
  decide (verifyDiagonalCore D)

/-- Diagnostic checker returning either the first mismatch or success. -/
def verifyDiagonal? (D : Matrix (Fin m) (Fin n) R) :
    Except (DiagMismatch m n R) Unit :=
  match firstDiagMismatch D with
  | some e => .error e
  | none => .ok ()

/-- Off-diagonal mismatch boolean is true exactly when the matrix entry is nonzero. -/
lemma mkOffDiagMismatch_mismatch_eq_true_iff
    (D : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    (mkOffDiagMismatch D i j).mismatch = true ↔ D i j ≠ 0 := by
  simp [mkOffDiagMismatch]

/-- Off-diagonal mismatch boolean is false exactly when the matrix entry is zero. -/
lemma mkOffDiagMismatch_mismatch_eq_false_iff
    (D : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    (mkOffDiagMismatch D i j).mismatch = false ↔ D i j = 0 := by
  simp [mkOffDiagMismatch]

/-- Column-scan returns `none` iff all inspected off-diagonal entries satisfy the spec. -/
lemma firstOffDiagInCols_eq_none_iff
    (D : Matrix (Fin m) (Fin n) R) (i : Fin m) (js : List (Fin n)) :
    firstOffDiagInCols D i js = none ↔
      ∀ j ∈ js, i.val ≠ j.val → D i j = 0 := by
  induction js with
  | nil =>
      simp [firstOffDiagInCols]
  | cons j js ih =>
      by_cases hij : i.val ≠ j.val
      · by_cases h0 : D i j = 0
        · simp [firstOffDiagInCols, hij, h0, ih, mkOffDiagMismatch]
        · simp [firstOffDiagInCols, hij, h0, mkOffDiagMismatch]
      · simp [firstOffDiagInCols, hij, ih]

/-- Row-scan returns `none` iff all inspected rows satisfy off-diagonal zero constraints. -/
lemma firstOffDiagInRows_eq_none_iff
    (D : Matrix (Fin m) (Fin n) R) (is : List (Fin m)) :
    firstOffDiagInRows D is = none ↔
      ∀ i ∈ is, ∀ j : Fin n, i.val ≠ j.val → D i j = 0 := by
  induction is with
  | nil => simp [firstOffDiagInRows]
  | cons i0 is ih =>
      constructor
      · intro h i' hi' j hij
        rcases List.mem_cons.mp hi' with rfl | hi_tail
        · have hcols : firstOffDiagInCols D i' (List.finRange n) = none := by
            cases hci : firstOffDiagInCols D i' (List.finRange n) with
            | none =>
                simp
            | some b =>
                simp [firstOffDiagInRows, hci] at h
          exact
            (firstOffDiagInCols_eq_none_iff D i' (List.finRange n)).1 hcols j
              (by simp only [List.mem_finRange j]) hij
        · have hcols : firstOffDiagInCols D i0 (List.finRange n) = none := by
            cases hci : firstOffDiagInCols D i0 (List.finRange n) with
            | none =>
                simp
            | some b =>
                simp [firstOffDiagInRows, hci] at h
          have hrows : firstOffDiagInRows D is = none := by
            simpa [firstOffDiagInRows, hcols] using h
          exact (ih.1 hrows) i' hi_tail j hij
      · intro h
        have hcols : firstOffDiagInCols D i0 (List.finRange n) = none := by
          apply (firstOffDiagInCols_eq_none_iff D i0 (List.finRange n)).2
          intro j hj hij
          exact h i0 (by simp) j hij
        have hrows : firstOffDiagInRows D is = none := by
          apply ih.2
          intro i' hi' j hij
          exact h i' (List.mem_cons_of_mem i0 hi') j hij
        simp [firstOffDiagInRows, hcols, hrows]

/-- Off-diagonal mismatch search succeeds (`none`) iff `offDiagsZero` holds. -/
theorem firstOffDiagMismatch_eq_none_iff_offDiagsZero (D : Matrix (Fin m) (Fin n) R) :
    firstOffDiagMismatch D = none ↔ offDiagsZero D := by
  unfold firstOffDiagMismatch offDiagsZero
  simp [firstOffDiagInRows_eq_none_iff]

/-- Zero-tail mismatch search succeeds (`none`) iff all scanned diagonal checks
 report no mismatch. -/
lemma firstZeroTailMismatch_eq_none_iff_all_false
    (D : Matrix (Fin m) (Fin n) R) :
    firstZeroTailMismatch D = none ↔
      ∀ k ∈ List.finRange (min m n), (mkZeroTailMismatch D k).mismatch = false := by
  unfold firstZeroTailMismatch
  suffices hgo :
      ∀ ks : List (Fin (min m n)),
        firstZeroTailMismatch.go D ks = none ↔
          ∀ k ∈ ks, (mkZeroTailMismatch D k).mismatch = false by
    simpa using hgo (List.finRange (min m n))
  intro ks
  induction ks with
  | nil =>
      simp [firstZeroTailMismatch.go]
  | cons k ks ih =>
      cases hmk : (mkZeroTailMismatch D k).mismatch <;>
        simp [firstZeroTailMismatch.go, hmk, ih]

/-- Zero-tail mismatch boolean is false exactly when the diagonal entry
matches the expected cutoff rule. -/
lemma mkZeroTailMismatch_mismatch_eq_false_iff
    (D : Matrix (Fin m) (Fin n) R) (k : Fin (min m n)) :
    (mkZeroTailMismatch D k).mismatch = false ↔
      (diagEntry D k = 0 ↔ firstZeroDiag D ≤ k.val) := by
  simp [mkZeroTailMismatch, diagEntry]

/-- Zero-tail mismatch search succeeds (`none`) iff `zeroTailAt` holds at the inferred cutoff. -/
theorem firstZeroTailMismatch_eq_none_iff_zeroTailAt (D : Matrix (Fin m) (Fin n) R) :
    firstZeroTailMismatch D = none ↔ zeroTailAt D (firstZeroDiag D) := by
  constructor
  · intro h k
    have hall := (firstZeroTailMismatch_eq_none_iff_all_false D).1 h
    have hkFalse : (mkZeroTailMismatch D k).mismatch = false := by
      exact hall k (by simp [List.mem_finRange k])
    exact (mkZeroTailMismatch_mismatch_eq_false_iff D k).1 hkFalse
  · intro hz
    apply (firstZeroTailMismatch_eq_none_iff_all_false D).2
    intro k hk
    exact (mkZeroTailMismatch_mismatch_eq_false_iff D k).2 (hz k)

/-- Combined mismatch search succeeds (`none`) iff the core diagonal verifier holds. -/
theorem firstDiagMismatch_eq_none_iff_verifyDiagonalCore (D : Matrix (Fin m) (Fin n) R) :
    firstDiagMismatch D = none ↔ verifyDiagonalCore D := by
  constructor
  · intro h
    have hoff : firstOffDiagMismatch D = none := by
      cases h1 : firstOffDiagMismatch D with
      | none => rfl
      | some b =>
          simp [firstDiagMismatch, h1] at h
    have hzero : firstZeroTailMismatch D = none := by
      cases hz : firstZeroTailMismatch D with
      | none => rfl
      | some b =>
          rw [firstDiagMismatch, hoff, hz] at h
          simp at h
    exact ⟨
      (firstOffDiagMismatch_eq_none_iff_offDiagsZero D).1 hoff,
      (firstZeroTailMismatch_eq_none_iff_zeroTailAt D).1 hzero
    ⟩
  · rintro ⟨hoffCore, hzeroCore⟩
    have hoff : firstOffDiagMismatch D = none :=
      (firstOffDiagMismatch_eq_none_iff_offDiagsZero D).2 hoffCore
    have hzero : firstZeroTailMismatch D = none :=
      (firstZeroTailMismatch_eq_none_iff_zeroTailAt D).2 hzeroCore
    simp [firstDiagMismatch, hoff, hzero]

theorem verifyDiagonalCoreB_eq_true_iff (D : Matrix (Fin m) (Fin n) R) :
    verifyDiagonalCoreB D = true ↔ verifyDiagonalCore D := by
  constructor
  · exact fun h => of_decide_eq_true h
  · intro h
    exact decide_eq_true h

theorem verifiedDiagonal_of_check_true (D : Matrix (Fin m) (Fin n) R) :
    verifyDiagonalCoreB D = true → verifyDiagonalCore D := by
  intro h
  exact (verifyDiagonalCoreB_eq_true_iff D).1 h

end DiagShape

section DiagDivisibility

/-- Adjacent diagonal divisibility condition for SNF, restricted to entries
within the rank prefix (`j < firstZeroDiag D`). -/
def divChainWithinRank (D : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ i j : Fin (min m n), i.val + 1 = j.val →
    j.val < firstZeroDiag D → diagEntry D i ∣ diagEntry D j

structure DivMismatch (m n : ℕ) (R : Type*) where
  i : Fin (min m n)
  j : Fin (min m n)
  cutoff : ℕ
  withinRank : Bool
  actualDivides : Bool
  mismatch : Bool
  deriving Repr

/-- Divisibility diagnostic payload for an adjacent pair `(i,j)` with `j=i+1`. -/
def mkDivMismatch
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)]
    (i j : Fin (min m n))
    (_hAdj : i.val + 1 = j.val) : DivMismatch m n R :=
  let cutoff := firstZeroDiag D
  let withinRank : Bool := decide (j.val < cutoff)
  let actualDivides : Bool := decide (diagEntry D i ∣ diagEntry D j)
  { i := i
    j := j
    cutoff := cutoff
    withinRank := withinRank
    actualDivides := actualDivides
    mismatch := decide (j.val < cutoff ∧ ¬ (diagEntry D i ∣ diagEntry D j)) }

/-- Scan a fixed `i` against candidate `j`s and return the first adjacent
divisibility mismatch, if any. -/
def firstDivInCols
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)]
    (i : Fin (min m n)) :
    List (Fin (min m n)) → Option (DivMismatch m n R)
  | [] => none
  | j :: js =>
      if hAdj : i.val + 1 = j.val then
        let b := mkDivMismatch D i j hAdj
        if b.mismatch then some b else firstDivInCols D i js
      else
        firstDivInCols D i js

/-- Scan `i`s in order and return the first adjacent divisibility mismatch, if any. -/
def firstDivInRows
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] :
    List (Fin (min m n)) → Option (DivMismatch m n R)
  | [] => none
  | i :: is =>
      match firstDivInCols D i (List.finRange (min m n)) with
      | some b => some b
      | none => firstDivInRows D is

/-- Return the first adjacent divisibility mismatch in row-major order, if any. -/
def firstDivMismatch
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] :
    Option (DivMismatch m n R) :=
  firstDivInRows D (List.finRange (min m n))

/-- The divisibility mismatch boolean is true exactly when the pair is inside
the rank prefix and divisibility fails. -/
lemma mkDivMismatch_mismatch_eq_true_iff
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)]
    (i j : Fin (min m n)) (hAdj : i.val + 1 = j.val) :
    (mkDivMismatch D i j hAdj).mismatch = true ↔
      j.val < firstZeroDiag D ∧ ¬ (diagEntry D i ∣ diagEntry D j) := by
  simp [mkDivMismatch]

/-- The divisibility mismatch boolean is false exactly when divisibility holds
whenever the pair is inside the rank prefix. -/
lemma mkDivMismatch_mismatch_eq_false_iff
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)]
    (i j : Fin (min m n)) (hAdj : i.val + 1 = j.val) :
    (mkDivMismatch D i j hAdj).mismatch = false ↔
      (j.val < firstZeroDiag D → diagEntry D i ∣ diagEntry D j) := by
  simp [mkDivMismatch, imp_iff_not_or]

/-- Column-scan returns `none` iff all adjacent candidates satisfy the
within-rank divisibility rule. -/
lemma firstDivInCols_eq_none_iff
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)]
    (i : Fin (min m n)) (js : List (Fin (min m n))) :
    firstDivInCols D i js = none ↔
      ∀ j ∈ js, ∀ hAdj : i.val + 1 = j.val,
        (mkDivMismatch D i j hAdj).mismatch = false := by
  induction js with
  | nil =>
      simp [firstDivInCols]
  | cons j js ih =>
      by_cases hAdj : i.val + 1 = j.val
      · cases hmis : (mkDivMismatch D i j hAdj).mismatch <;>
          simp [firstDivInCols, hAdj, hmis, ih]
      · simp [firstDivInCols, hAdj, ih]

/-- Row-scan returns `none` iff all inspected rows satisfy the adjacent
within-rank divisibility rule. -/
lemma firstDivInRows_eq_none_iff
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)]
    (is : List (Fin (min m n))) :
    firstDivInRows D is = none ↔
      ∀ i ∈ is, ∀ j : Fin (min m n), ∀ hAdj : i.val + 1 = j.val,
        (mkDivMismatch D i j hAdj).mismatch = false := by
  induction is with
  | nil =>
      simp [firstDivInRows]
  | cons i0 is ih =>
      constructor
      · intro h i' hi' j hAdj
        rcases List.mem_cons.mp hi' with rfl | hi_tail
        · have hcols : firstDivInCols D i' (List.finRange (min m n)) = none := by
            cases hci : firstDivInCols D i' (List.finRange (min m n)) with
            | none =>
                simp
            | some b =>
                simp [firstDivInRows, hci] at h
          exact
            (firstDivInCols_eq_none_iff D i' (List.finRange (min m n))).1 hcols j
              (by simp [List.mem_finRange]) hAdj
        · have hcols : firstDivInCols D i0 (List.finRange (min m n)) = none := by
            cases hci : firstDivInCols D i0 (List.finRange (min m n)) with
            | none =>
                simp
            | some b =>
                simp [firstDivInRows, hci] at h
          have hrows : firstDivInRows D is = none := by
            simpa [firstDivInRows, hcols] using h
          exact (ih.1 hrows) i' hi_tail j hAdj
      · intro h
        have hcols : firstDivInCols D i0 (List.finRange (min m n)) = none := by
          apply (firstDivInCols_eq_none_iff D i0 (List.finRange (min m n))).2
          intro j hj hAdj
          exact h i0 (by simp) j hAdj
        have hrows : firstDivInRows D is = none := by
          apply ih.2
          intro i' hi' j hAdj
          exact h i' (List.mem_cons_of_mem i0 hi') j hAdj
        simp [firstDivInRows, hcols, hrows]

/-- Divisibility mismatch search succeeds (`none`) iff `divChainWithinRank` holds. -/
theorem firstDivMismatch_eq_none_iff_divChainWithinRank
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] :
    firstDivMismatch D = none ↔ divChainWithinRank D := by
  unfold firstDivMismatch divChainWithinRank
  constructor
  · intro h i j hAdj
    have hall :
        ∀ i ∈ List.finRange (min m n), ∀ j : Fin (min m n), ∀ hAdj : i.val + 1 = j.val,
          (mkDivMismatch D i j hAdj).mismatch = false :=
      (firstDivInRows_eq_none_iff D (List.finRange (min m n))).1 h
    exact (mkDivMismatch_mismatch_eq_false_iff D i j hAdj).1
      (hall i (by simp [List.mem_finRange]) j hAdj)
  · intro h
    apply (firstDivInRows_eq_none_iff D (List.finRange (min m n))).2
    intro i hi j hAdj
    exact (mkDivMismatch_mismatch_eq_false_iff D i j hAdj).2 (h i j hAdj)

/-- Backward-compatible name; prefer `divChainWithinRank`. -/
abbrev divChainAdjacent (D : Matrix (Fin m) (Fin n) R) : Prop :=
  divChainWithinRank D


end DiagDivisibility

section DiagAssemble

/-- Core diagonal SNF condition: diagonal shape plus divisibility chain. -/
def verifyDiag (D : Matrix (Fin m) (Fin n) R) : Prop :=
  verifyDiagonalCore D ∧ divChainWithinRank D

instance
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] : Decidable (divChainWithinRank D) := by
  unfold divChainWithinRank
  infer_instance

instance
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] : Decidable (verifyDiag D) := by
  unfold verifyDiag
  infer_instance

/-- Sum type for full diagonal verification mismatches (shape or divisibility). -/
inductive VerifyDiagMismatch (m n : ℕ) (R : Type*) where
  | shape (b : DiagMismatch m n R)
  | div (b : DivMismatch m n R)
  deriving Repr

/-- Return the first full diagonal mismatch, prioritizing shape failures. -/
def firstVerifyDiagMismatch
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] :
    Option (VerifyDiagMismatch m n R) :=
  match firstDiagMismatch D with
  | some b => some (.shape b)
  | none =>
      match firstDivMismatch D with
      | some b => some (.div b)
      | none => none

/-- Diagnostic checker for full diagonal verification. -/
def verifyDiag?
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] :
    Except (VerifyDiagMismatch m n R) Unit :=
  match firstVerifyDiagMismatch D with
  | some e => .error e
  | none => .ok ()

/-- Full diagonal mismatch search succeeds (`none`) iff `verifyDiag` holds. -/
theorem firstVerifyDiagMismatch_eq_none_iff_verifyDiag
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] :
    firstVerifyDiagMismatch D = none ↔ verifyDiag D := by
  constructor
  · intro h
    have hshape : firstDiagMismatch D = none := by
      cases hs : firstDiagMismatch D with
      | none => rfl
      | some b =>
          simp [firstVerifyDiagMismatch, hs] at h
    have hdiv : firstDivMismatch D = none := by
      cases hd : firstDivMismatch D with
      | none => rfl
      | some b =>
          rw [firstVerifyDiagMismatch, hshape, hd] at h
          simp at h
    exact ⟨
      (firstDiagMismatch_eq_none_iff_verifyDiagonalCore D).1 hshape,
      (firstDivMismatch_eq_none_iff_divChainWithinRank D).1 hdiv
    ⟩
  · rintro ⟨hshapeCore, hdivCore⟩
    have hshape : firstDiagMismatch D = none :=
      (firstDiagMismatch_eq_none_iff_verifyDiagonalCore D).2 hshapeCore
    have hdiv : firstDivMismatch D = none :=
      (firstDivMismatch_eq_none_iff_divChainWithinRank D).2 hdivCore
    simp [firstVerifyDiagMismatch, hshape, hdiv]

theorem verifyDiag?_ok_iff_verifyDiag
    (D : Matrix (Fin m) (Fin n) R)
    [DecidableRel (fun a b : R => a ∣ b)] :
    verifyDiag? D = .ok () ↔ verifyDiag D := by
  unfold verifyDiag?
  cases hmis : firstVerifyDiagMismatch D with
  | none =>
      have hdiag : verifyDiag D :=
        (firstVerifyDiagMismatch_eq_none_iff_verifyDiag D).1 hmis
      simp [hdiag]
  | some b =>
      have hnot : ¬ verifyDiag D := by
        intro hdiag
        have hnone : firstVerifyDiagMismatch D = none :=
          (firstVerifyDiagMismatch_eq_none_iff_verifyDiag D).2 hdiag
        simp [hmis] at hnone
      simp [hnot]

/-- Backward-compatible alias; prefer `verifyDiag`. -/
abbrev verifyCore (D : Matrix (Fin m) (Fin n) R) : Prop := verifyDiag D

end DiagAssemble

section SNFPayload

/-- SNF payload verification predicate:
`verifyDiag` plus inverse and factorization checks. -/
def verifySNF
    (A : Matrix (Fin m) (Fin n) R)
    (U Uinv : Matrix (Fin m) (Fin m) R)
    (V Vinv : Matrix (Fin n) (Fin n) R)
    (D : Matrix (Fin m) (Fin n) R) : Prop :=
  verifyDiag D ∧ U * Uinv = 1 ∧ V * Vinv = 1 ∧ U * A * V = D

/-- Backward-compatible alias; prefer `verifySNF`. -/
abbrev verifySNFCore
    (A : Matrix (Fin m) (Fin n) R)
    (U Uinv : Matrix (Fin m) (Fin m) R)
    (V Vinv : Matrix (Fin n) (Fin n) R)
    (D : Matrix (Fin m) (Fin n) R) : Prop :=
  verifySNF A U Uinv V Vinv D

end SNFPayload
