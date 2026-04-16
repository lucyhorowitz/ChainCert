import Cultivar.SNF.Core
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

variable {α : Type*} {m n : ℕ}
variable {R : Type*} [Zero R] [DecidableEq R]

def hasDiagZeroTail (D : Matrix (Fin m) (Fin n) R) : Prop :=
  ∃ r : ℕ, ∀ (i : Fin (min m n)), diagEntry D i = 0 ↔ r ≤ i.val

def diagOK (D : Matrix (Fin m) (Fin n) R) : Prop :=
  IsDiagonal D ∧ hasDiagZeroTail D

def firstZeroDiag (D : Matrix (Fin m) (Fin n) R) : ℕ :=
  let rec go : List (Fin (min m n)) → Option (Fin (min m n))
    | [] => none
    | i :: is => if diagEntry D i = 0 then some i else go is
  match go (List.finRange (min m n)) with
  | some i => i.val
  | none => min m n

structure OffDiagMismatch (m n : ℕ) (R : Type*) where
  i : ℕ
  j : ℕ
  actualZero : Bool
  expectedZero : Bool
  mismatch : Bool
  deriving Repr

def mkOffDiagMismatch (D : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    OffDiagMismatch m n R where
  i := i.val
  j := j.val
  actualZero := decide (D i j = 0)
  expectedZero := decide (i.val ≠ j.val)
  mismatch := decide ((decide (D i j = 0)) != (decide (i.val ≠ j.val)))

structure ZeroTailDiagMismatch (m n : ℕ) (R : Type*) where
  k : Nat
  cutoff : Nat
  actualZero : Bool
  expectedZero : Bool
  mismatch : Bool
  deriving Repr

def mkZeroTailMismatch (D : Matrix (Fin m) (Fin n) R) (k : Fin (min m n)) :
    ZeroTailDiagMismatch m n R where
  k := k.val
  cutoff := firstZeroDiag D
  actualZero := by
    let i : Fin m := Fin.castLE (Nat.min_le_left m n) k
    let j : Fin n := Fin.castLE (Nat.min_le_right m n) k
    exact decide (D i j = 0)
  expectedZero := decide (firstZeroDiag D ≤ k.val)
  mismatch := by
    let i : Fin m := Fin.castLE (Nat.min_le_left m n) k
    let j : Fin n := Fin.castLE (Nat.min_le_right m n) k
    exact decide ((decide (firstZeroDiag D ≤ k.val)) != (decide (D i j = 0)))

def firstOffDiagInCols (D : Matrix (Fin m) (Fin n) R) (i : Fin m) :
    List (Fin n) → Option (OffDiagMismatch m n R)
  | [] => none
  | j :: js =>
      if i.val ≠ j.val then
        let b := mkOffDiagMismatch D i j
        if b.mismatch then some b else firstOffDiagInCols D i js
      else
        firstOffDiagInCols D i js

def firstOffDiagInRows (D : Matrix (Fin m) (Fin n) R) :
    List (Fin m) → Option (OffDiagMismatch m n R)
  | [] => none
  | i :: is =>
      match firstOffDiagInCols D i (List.finRange n) with
      | some b => some b
      | none => firstOffDiagInRows D is

def firstOffDiagMismatch (D : Matrix (Fin m) (Fin n) R) :
    Option (OffDiagMismatch m n R) :=
  firstOffDiagInRows D (List.finRange m)

def firstZeroTailMismatch (D : Matrix (Fin m) (Fin n) R) :
    Option (ZeroTailDiagMismatch m n R) :=
  let cutoff := firstZeroDiag D
  let rec go : List (Fin (min m n)) → Option (ZeroTailDiagMismatch m n R)
    | [] => none
    | k :: ks =>
        if cutoff < k.val then
          let b := mkZeroTailMismatch D k
          if b.mismatch then some b else go ks
        else
          go ks
  go (List.finRange (min m n))

inductive DiagMismatch (m n : ℕ) (R : Type*) where
  | offDiag (b : OffDiagMismatch m n R)
  | zeroTail (b : ZeroTailDiagMismatch m n R)
  deriving Repr

def firstDiagMismatch (D : Matrix (Fin m) (Fin n) R) :
    Option (DiagMismatch m n R) :=
  match firstOffDiagMismatch D with
  | some b => some (.offDiag b)
  | none =>
      match firstZeroTailMismatch D with
      | some b => some (.zeroTail b)
      | none => none
