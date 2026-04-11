# snf_server.py
# Adapted from sage_server.py in https://github.com/mkaratarakis/sagestuff
#
# Persistent Sage subprocess that dispatches JSON requests by an "op" field.
# To add a new operation: define a function and decorate it with @op("name").
# The function receives the parsed request dict and returns a dict; the
# framework handles JSON encoding and error reporting.
#
# Currently supported ops:
#   "snf"      -> {"matrix": [[...]]}         returns U, D, V, Uinv, Vinv
#   "boundary" -> {"facets": [[...]], "n":k}  returns d_k and the bases used

import sys
import json
from sage.all import matrix, ZZ, SimplicialComplex

HANDLERS = {}

def op(name):
    def register(fn):
        HANDLERS[name] = fn
        return fn
    return register

def mat_to_rows(M):
    return [[str(x) for x in row] for row in M.rows()]

def _maybe_json(x):
    return json.loads(x) if isinstance(x, str) else x

@op("snf")
def handle_snf(req):
    A = matrix(ZZ, _maybe_json(req["matrix"]))
    D, U, V = A.smith_form()
    return {
        "status": "ok",
        "D": mat_to_rows(D),
        "U": mat_to_rows(U),
        "Uinv": mat_to_rows(U.inverse()),
        "V": mat_to_rows(V),
        "Vinv": mat_to_rows(V.inverse()),
    }

@op("boundary")
def handle_boundary(req):
    # We compute the boundary map ourselves instead of calling Sage's
    # `chain_complex().differential(n)`. Sage's differential matrix is indexed
    # by an internal basis order that did NOT match `X.n_cells(k)`, so the
    # matrix and bases we returned to Lean were inconsistent. Rather than
    # reverse-engineer Sage's convention, we enumerate simplices in lex order
    # and apply the alternating-sum face-deletion formula directly. This
    # guarantees the matrix and the bases we return are built against the
    # same order, and decouples us from Sage's chain-complex internals.
    facets = _maybe_json(req["facets"])
    n = int(req["n"])
    X = SimplicialComplex(facets)

    # Lex-sorted bases. Each simplex is stored as a sorted tuple so its
    # vertices are canonically ordered; the outer sort gives a canonical
    # order on the collection of simplices.
    def simplices(k):
        if k < 0:
            return []
        return sorted(tuple(sorted(s)) for s in X.n_cells(k))

    dom = simplices(n)
    cod = simplices(n - 1)
    cod_index = {s: i for i, s in enumerate(cod)}

    # Build the differential against those lex-sorted bases via the
    # alternating-sum face-deletion formula: for sigma = (v_0, ..., v_k),
    #   d(sigma) = sum_i (-1)^i * (v_0, ..., v̂_i, ..., v_k).
    # For n = 0 the codomain is empty (unreduced convention: d_0 : C_0 → 0),
    # so we skip the loop and return a zero-row matrix — matching how Sage's
    # `chain_complex().differential(0)` behaves by default.
    entries = [[0] * len(dom) for _ in range(len(cod))]
    if cod:
        for j, sigma in enumerate(dom):
            for i in range(len(sigma)):
                face = sigma[:i] + sigma[i + 1:]
                entries[cod_index[face]][j] += (-1) ** i

    return {
        "status": "ok",
        "d": [[str(x) for x in row] for row in entries],
        "domain_basis": [list(s) for s in dom],
        "codomain_basis": [list(s) for s in cod],
    }

def process_request(line):
    try:
        req = json.loads(line)
        if "op" not in req:
            return json.dumps({"status": "error", "message": "missing required field: op"})
        name = req["op"]
        handler = HANDLERS.get(name)
        if handler is None:
            return json.dumps({"status": "error", "message": f"unknown op: {name}"})
        return json.dumps(handler(req))
    except Exception as e:
        return json.dumps({"status": "error", "message": str(e)})

# Persistent loop (unchanged from sage_server.py)
while True:
    line = sys.stdin.readline()
    if not line:
        break
    print(process_request(line), flush=True)
