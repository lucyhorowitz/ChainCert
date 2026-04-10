# snf_server.py
# Adapted from sage_server.py in https://github.com/mkaratarakis/sagestuff
# Changes: receives a matrix (list of lists) instead of a polynomial string,
# calls .smith_form(), and returns U, D, V as lists of lists.

import sys
import json
from sage.all import *

def process_request(line):
    try:
        req = json.loads(line)
        entries = req.get("matrix")
        if isinstance(entries, str):
            entries = json.loads(entries)
        A = matrix(ZZ, entries)
        D, U, V = A.smith_form()
        Uinv = U.inverse()
        Vinv = V.inverse()
        return json.dumps({
            "status": "ok",
            "D": [[str(x) for x in row] for row in D.rows()],
            "U": [[str(x) for x in row] for row in U.rows()],
            "Uinv": [[str(x) for x in row] for row in Uinv.rows()],
            "V": [[str(x) for x in row] for row in V.rows()],
            "Vinv": [[str(x) for x in row] for row in Vinv.rows()]
        })
    except Exception as e:
        return json.dumps({"status": "error", "message": str(e)})

# Persistent loop (unchanged from sage_server.py)
while True:
    line = sys.stdin.readline()
    if not line:
        break
    print(process_request(line), flush=True)
