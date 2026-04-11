-- SageServer.lean
-- Subprocess/JSON-RPC infrastructure adapted from SageTacticNoRing.lean
-- in https://github.com/mkaratarakis/sagestuff

import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Fin.VecNotation
import Lean

open Lean Elab Tactic Meta Term IO Process

initialize sageServerRef : IO.Ref (Option (Child {stdin := .piped, stdout := .piped, stderr := .piped})) ← IO.mkRef none

def getSageServer : IO (IO.Process.Child {stdin := .piped, stdout := .piped, stderr := .piped}) := do
  let current ← sageServerRef.get
  match current with
  | some child => return child
  | none =>
    -- This ensures we find sage_server.py in your current directory
    let serverScript := "scripts/snf_server.py"
    let child ← IO.Process.spawn {
      -- Use the absolute path to the Conda sage binary
      cmd := "sage",
      args := #["-python", serverScript],
      stdin := .piped, stdout := .piped, stderr := .piped
    }
    sageServerRef.set (some child)
    return child

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

/-- Send a JSON request to the persistent Sage server and return the parsed
response object. Handles the write/read/parse/status-check plumbing so callers
only need to build the request and pull fields out of the result.

Throws on JSON parse errors and on responses with `status ≠ "ok"`. -/
def sendSageRequest (req : Lean.Json) : MetaM Lean.Json := do
  let server ← getSageServer
  server.stdin.putStr (req.compress ++ "\n")
  server.stdin.flush
  let respStr ← server.stdout.getLine
  match Lean.Json.parse respStr with
  | .error err =>
    throwError s!"Sage JSON parse error: {err}\nRaw response: {respStr}"
  | .ok json =>
    match json.getObjVal? "status" with
    | .ok (.str "ok") => return json
    | _ =>
      let errMsg := (json.getObjVal? "message").toOption.map (·.compress)
                      |>.getD "unknown error"
      throwError s!"Sage server error: {errMsg}"
