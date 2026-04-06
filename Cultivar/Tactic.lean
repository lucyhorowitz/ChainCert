-- Tactic.lean
-- Subprocess/JSON-RPC infrastructure adapted from SageTacticNoRing.lean
-- in https://github.com/mkaratarakis/sagestuff
-- Changes: sends a matrix instead of a polynomial, parses U/D/V from response,
-- constructs a CertificateSNF term.

import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Defs
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

class SageSerializableRing (R : Type*) where
  toSageString : R → String
  fromSageString : String → Option R
  sageName : String

instance : SageSerializableRing ℤ where
  toSageString := fun n ↦ toString n
  fromSageString := fun s => s.toInt?
  sageName := "ZZ"

instance : SageSerializableRing ℚ where
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

variable {m n : ℕ} {R : Type} [SageSerializableRing R] [Inhabited R]

def matStringList (A : Matrix (Fin m) (Fin n) R) :=
 List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => SageSerializableRing.toSageString (A i j)))

def toMatString (A : Matrix (Fin m) (Fin n) R) :=
  "[" ++ ", ".intercalate ((matStringList A).map (fun row => "[" ++ ", ".intercalate row ++ "]")) ++ "]"

def fromJsonMatrix {m n : ℕ} [Inhabited R] (j : Lean.Json) : IO (Matrix (Fin m) (Fin n) R) := do
  match j with
  | Lean.Json.arr rows =>
    if rows.size ≠ m then
      throw <| IO.userError s!"Expected {m} rows, got {rows.size}"
    let mat : Array (Array R) ← (Array.ofFn (n := m) id).mapM fun i => do
      match rows[i.val]? with
      | none => throw <| IO.userError s!"Missing row {i.val}"
      | some rowJson =>
        match rowJson with
        | Lean.Json.arr cols =>
          if cols.size ≠ n then
            throw <| IO.userError s!"Row {i.val}: expected {n} cols, got {cols.size}"
          (Array.ofFn (n := n) id).mapM fun j => do
            match cols[j.val]? with
            | none => throw <| IO.userError s!"Missing entry ({i.val}, {j.val})"
            | some entryJson =>
              let s := match entryJson with
                | Lean.Json.str s => s
                | _ => entryJson.compress
              match SageSerializableRing.fromSageString s with
              | some v => return v
              | none => throw <| IO.userError s!"Could not parse entry: {s}"
        | _ => throw <| IO.userError s!"Row {i.val} is not a JSON array"
    return Matrix.of (fun i j => mat[i.val]![j.val]!)
  | _ => throw <| IO.userError "Expected JSON array for matrix"


-- Testing out the fromJsonMatrix function
#eval show IO _ from do
  let mat ← fromJsonMatrix (m := 2) (n := 2) (R := ℤ)
    (Lean.Json.arr #[
      Lean.Json.arr #[Lean.Json.str "1", Lean.Json.str "2"],
      Lean.Json.arr #[Lean.Json.str "3", Lean.Json.str "4"]])
  return (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin 2 => mat i j)

def callSageRpc (A : Matrix (Fin m) (Fin n) R) : IO (Matrix (Fin m) (Fin m) R × Matrix (Fin m) (Fin n) R × Matrix (Fin n) (Fin n) R) := do
  let server ← getSageServer

  let matStr := toMatString A

  let reqJson := Lean.Json.mkObj [("matrix", Lean.Json.str matStr)]
  let reqStr := reqJson.compress ++ "\n"

  server.stdin.putStr reqStr
  server.stdin.flush

  let respStr ← server.stdout.getLine

  match Lean.Json.parse respStr with
  | Except.ok json =>
    match json.getObjVal? "status" with
    | Except.ok (Lean.Json.str "ok") =>
      let U_json ← IO.ofExcept <| json.getObjVal? "U"
      let D_json ← IO.ofExcept <| json.getObjVal? "D"
      let V_json ← IO.ofExcept <| json.getObjVal? "V"
      let U ← fromJsonMatrix U_json
      let D ← fromJsonMatrix D_json
      let V ← fromJsonMatrix V_json
      return (U, D, V)
    | _ =>
        let errMsg := (json.getObjVal? "message").toOption.map (·.compress) |>.getD "Unknown Error"
        throw <| IO.userError s!"Sage Server Error: {errMsg}"
  | Except.error err =>
    throw <| IO.userError s!"JSON Parse Error: {err}\nRaw string: {respStr}"

-- TODO: Figure out what the tactic should actually look like
/- elab "sage_factor' " origTerm:term : tactic => do
  let fmt ← PrettyPrinter.ppTerm origTerm
  let polyStr := fmt.pretty

  let factoredStr ← callSageRpc polyStr
  logInfo s!"[Sage RPC] Factored to: {factoredStr}"

  let env ← getEnv
  let factSyntax ← Lean.ofExcept <| Parser.runParserCategory env `term factoredStr
  let factTerm : TSyntax `term := ⟨factSyntax⟩

  let stx ← `(tactic|
    ( --have h_sage : $origTerm = $factTerm := by ring_nf
      have H : $origTerm = $factTerm := by sorry
      rw [H] )
  )

  evalTactic stx -/
