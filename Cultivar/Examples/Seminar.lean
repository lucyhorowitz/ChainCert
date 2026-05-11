import Mathlib.Tactic.Ring

/-!
# Seminar companion file

Live-demo snippets for the comp-math seminar talk (2026-04-28).
Organized in the order of the outline: simple types → dependent types →
propositions-as-types → a tiny proof.
-/

namespace Seminar

/-! ## 1. Types classify terms -/

#check 3              -- Nat
#check "hi"           -- String
#check true           -- Bool
#check (3, "hi")      -- Nat × String


/-! ## 2. Simple types: functions, products, sums -/

-- function type A → B
def double (n : Nat) : Nat := n + n
#check double         -- Nat → Nat
#eval double 7        -- 14

#check fun x ↦ x + 2  -- Nat → Nat (NOTICE HOW LEAN INFERRED THE TYPE OF
                      -- `x` WITHOUT ME HAVING TO SAY ANYTHING)

-- product type A × B
def pair : Nat × String := (3, "hi")
#check pair.fst       -- Nat
#check pair.snd       -- String

-- sum type A ⊕ B
def left : Nat ⊕ String := .inl 3
def right : Nat ⊕ String := .inr "hi"

#check left


/-! ## 3. Dependent types: types depending on values

The type of a term can depend on a *value*, not just on other types.
-/

-- Vec α n: vectors of length n. The type knows the length.
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

#check Vec.nil                            -- Vec ?α 0
#check Vec.cons 1 (Vec.cons 2 Vec.nil)    -- Vec Nat 2

-- The type of `cons` itself: a *dependent function type*.
-- Without dependency we couldn't even write this down.
#check @Vec.cons    -- {α : Type} → {n : Nat} → α → Vec α n → Vec α (n + 1)

-- Pi-type notation: (x : A) → B x
def replicate (α : Type) : (n : Nat) → α → Vec α n
  | 0,     _ => .nil
  | n + 1, a => .cons a (replicate α n a)

def test := replicate String 4 "hi"
#check test
#eval test

/-! ## 4. Propositions as types

In Lean, propositions are types and proofs are terms of those types.
The kernel checks the term has the type — that check IS the verification.
-/

-- A proposition is a type living in the universe `Prop`.
#check (2 + 2 = 4)        -- Prop
#check Nat.add_comm       -- ∀ (n m : Nat), n + m = m + n
#check ∀ (n m : Nat), n + m = m + n

-- A proof is a term of that type.
example : 2 + 2 = 4 := rfl

-- Implication P → Q is a function from proofs of P to proofs of Q.
example (P Q : Prop) (h : P → Q) (hP : P) : Q := h hP

-- ∀ x, P x is a *dependent function* (x : α) → P x.
-- A proof is literally a function taking x and returning a proof of P x.
example : ∀ n : Nat, n + 0 = n := fun n => Nat.add_zero n


/-! ## 5. Prop-irrelevance: the hinge

Lean only cares THAT a proposition is inhabited, not WHICH term inhabits it.
Two proofs of the same proposition are definitionally interchangeable.
This is why a proof works as a checkable certificate of truth.
-/

example (p q : 2 + 2 = 4) : p = q := rfl


/-! ## 6. Find vs. check, made concrete

Hard to find a factorization; easy to check one.
The `decide` tactic just runs the check.
-/

example : 2491 = 47 * 53 := by decide


/-! ## 7. Easy theorems, proved interactively

Try these. Put your cursor inside the `by` block to see the goal state
in the InfoView. Each tactic transforms the goal until there's nothing left.
-/

-- The simplest possible proof: both sides reduce to the same thing.
example : 2 + 3 = 5 := by rfl

-- A tiny logical proof: modus ponens.
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

-- Conjunction: split the goal into two pieces.
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

-- Commutativity of `and`.
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.right
  · exact h.left

-- A tiny arithmetic fact, by induction.
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Nat.add_succ, ih]

-- `simp` and `ring` do a lot of work for free.
example (a b : Nat) : (a + b) * (a + b) = a*a + 2*a*b + b*b := by ring

example : 47 * 53 = 2491 := by decide


end Seminar
