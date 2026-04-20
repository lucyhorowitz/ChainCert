import Cultivar.SNF.Core
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

variable {α : Type*} {m n : ℕ}
variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [DecidableEq R]



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

/-! Now "core" verificaiton for automated things -/

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

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Off-diagonal mismatch boolean is true exactly when the matrix entry is nonzero. -/
lemma mkOffDiagMismatch_mismatch_eq_true_iff
    (D : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    (mkOffDiagMismatch D i j).mismatch = true ↔ D i j ≠ 0 := by
  simp [mkOffDiagMismatch]

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Off-diagonal mismatch boolean is false exactly when the matrix entry is zero. -/
lemma mkOffDiagMismatch_mismatch_eq_false_iff
    (D : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    (mkOffDiagMismatch D i j).mismatch = false ↔ D i j = 0 := by
  simp [mkOffDiagMismatch]

omit [IsDomain R] [IsPrincipalIdealRing R] in
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

omit [IsDomain R] [IsPrincipalIdealRing R] in
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

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Off-diagonal mismatch search succeeds (`none`) iff `offDiagsZero` holds. -/
theorem firstOffDiagMismatch_eq_none_iff_offDiagsZero (D : Matrix (Fin m) (Fin n) R) :
    firstOffDiagMismatch D = none ↔ offDiagsZero D := by
  unfold firstOffDiagMismatch offDiagsZero
  simp [firstOffDiagInRows_eq_none_iff]

omit [IsDomain R] [IsPrincipalIdealRing R] in
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

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- Zero-tail mismatch boolean is false exactly when the diagonal entry
matches the expected cutoff rule. -/
lemma mkZeroTailMismatch_mismatch_eq_false_iff
    (D : Matrix (Fin m) (Fin n) R) (k : Fin (min m n)) :
    (mkZeroTailMismatch D k).mismatch = false ↔
      (diagEntry D k = 0 ↔ firstZeroDiag D ≤ k.val) := by
  simp [mkZeroTailMismatch, diagEntry]

omit [IsDomain R] [IsPrincipalIdealRing R] in
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

omit [IsDomain R] [IsPrincipalIdealRing R] in
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

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem verifyDiagonalCoreB_eq_true_iff (D : Matrix (Fin m) (Fin n) R) :
    verifyDiagonalCoreB D = true ↔ verifyDiagonalCore D := by
  constructor
  · exact fun h => of_decide_eq_true h
  · intro h
    exact decide_eq_true h

omit [IsDomain R] [IsPrincipalIdealRing R] in
theorem verifiedDiagonal_of_check_true (D : Matrix (Fin m) (Fin n) R) :
    verifyDiagonalCoreB D = true → verifyDiagonalCore D := by
  intro h
  exact (verifyDiagonalCoreB_eq_true_iff D).1 h

/-- Core SNF payload verification predicate: diagonal shape plus inverse and
factorization checks. -/
def verifySNFCore
    (A : Matrix (Fin m) (Fin n) R)
    (U Uinv : Matrix (Fin m) (Fin m) R)
    (V Vinv : Matrix (Fin n) (Fin n) R)
    (D : Matrix (Fin m) (Fin n) R) : Prop :=
  verifyDiagonalCore D ∧ U * Uinv = 1 ∧ V * Vinv = 1 ∧ U * A * V = D
