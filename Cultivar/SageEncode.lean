-- SageEncode.lean
-- Outgoing serialization: how Lean values are turned into something
-- Sage can read. Contains the `SageSerializable` typeclass, instances
-- for `ℤ` and `ℚ`, matrix-to-string helpers used when building requests,
-- and the meta-level `evalExpr` utilities used by the `#snf` / `#diff`
-- commands to run serialization code on an `Expr` at elaboration time.

import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Fin.VecNotation
import Lean

open Lean Elab Tactic Meta Term IO Process

/-- Typeclass for things whose elements can be represented as strings
    that are readable by Sage -/
class SageSerializable (R : Type*) where
  toSageString : R → String
  fromSageString : String → Option R
  sageName : String

/-- The integers are `SageSerializable` -/
instance : SageSerializable ℤ where
  toSageString := fun n ↦ toString n
  fromSageString := fun s => s.toInt?
  sageName := "ZZ"

/-- The rationals are `SageSerializable` -/
instance : SageSerializable ℚ where
  toSageString := fun q => s!"{q.num}/{q.den}"
  fromSageString :=
    fun s => match s.splitOn "/" with
    | [n, d] => do
        let num ← n.toInt?
        let den ← d.toInt?
        return (num : ℚ) / (den : ℚ)
    | [n] => do
        let num ← n.toInt?
        return (num : ℚ)
    | _ => none
  sageName := "QQ"

-- TODO: add instances for other rings (e.g. ℤ[x] → "ZZ['x']", GaussianIntegers, etc.)

variable {m n : ℕ} {R : Type} [SageSerializable R] [Inhabited R]

def matStringList (A : Matrix (Fin m) (Fin n) R) :=
 List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => SageSerializable.toSageString (A i j)))

def toMatString (A : Matrix (Fin m) (Fin n) R) :=
  "[" ++ ", ".intercalate ((matStringList A).map (fun row => "[" ++ ", ".intercalate row ++ "]")) ++ "]"

/-- Evaluate a `SageSerializable.toSageString` call at the meta level: given an `Expr`
representing a value of some `SageSerializable` type, build the application
`SageSerializable.toSageString entry` and reduce it to a `String`.

Marked `unsafe` because `Lean.Meta.evalExpr` requires it — it evaluates compiled code
at elaboration time. This is fine for our purposes since the result is only used to
build a Sage query string, which we don't trust anyway (Sage's output gets verified
in Lean separately). -/
unsafe def evalSageString (entry : Expr) : MetaM String := do
    let callExpr ← mkAppM ``SageSerializable.toSageString #[entry]
    Lean.Meta.evalExpr String (.const ``String []) callExpr

/-- Safe wrapper around `evalSageString`. The `@[implemented_by]` attribute tells the
compiler to use the `unsafe` implementation at runtime while keeping the kernel happy
with an `opaque` signature. -/
@[implemented_by evalSageString]
  opaque evalSageStringSafe (entry : Expr) : MetaM String

def stringListToMatString (rows : List (List String)) : String :=
  "[" ++ ", ".intercalate (rows.map (fun row => "[" ++ ", ".intercalate row ++ "]")) ++ "]"

/-- Meta-level evaluation of an arbitrary `Nat`-valued `Expr`. Used by command
elaborators that accept a `Nat` argument and need the numeric value at elab
time (e.g. the dimension in `#boundary K, n`). Handles any term form — literals,
named definitions, or arithmetic expressions — because it actually compiles
and runs the expression rather than pattern-matching on `.lit`. -/
unsafe def evalNatExpr (e : Expr) : MetaM Nat :=
  Lean.Meta.evalExpr Nat (mkConst ``Nat) e

@[implemented_by evalNatExpr]
opaque evalNatSafe (e : Expr) : MetaM Nat

unsafe def evalMatStringList (A : Expr) : MetaM (List (List String)) := do
    let call ← mkAppM ``matStringList #[A]
    Lean.Meta.evalExpr (List (List String))
      (mkApp (.const ``List [0]) (mkApp (.const ``List [0]) (.const ``String [])))
      call

@[implemented_by evalMatStringList]
opaque evalMatStringListSafe (A : Expr) : MetaM (List (List String))
