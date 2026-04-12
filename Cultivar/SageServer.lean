-- SageServer.lean
-- Transport layer: owns the persistent Sage subprocess and exposes a
-- request/response helper. Serialization helpers live in `SageEncode.lean`
-- and `SageDecode.lean`; this file deliberately has no opinions about
-- what Lean values become.
-- Adapted from SageTacticNoRing.lean in
-- https://github.com/mkaratarakis/sagestuff

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
