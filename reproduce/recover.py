"""Recover and independently expand a characteristic-zero Laurent identity."""
import json
import subprocess
import tempfile
from collections import defaultdict
from functools import reduce
from math import gcd, lcm
from pathlib import Path
from flint import fmpq_mat

here = Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as work:
    matrix_file = Path(work) / "orbits.json"
    subprocess.run(["node", str(here / "orbits.cjs"), "--export", str(matrix_file)], check=True)
    data = json.loads(matrix_file.read_text(encoding="utf8"))
rows = data["selected"]
n = len(rows)
matrix = fmpq_mat(2*n, 2*n)
rhs = fmpq_mat(2*n, 1)
rhs[data["constantColumn"], 0] = 1
for j, row in enumerate(rows):
    for k, a, b in row["entries"]:
        matrix[k,j], matrix[k,n+j] = a,-b
        matrix[n+k,j], matrix[n+k,n+j] = b,a
solution = matrix.solve(rhs, algorithm="dixon")
assert matrix*solution == rhs
den = lcm(*(int(solution[j,0].denominator) for j in range(2*n)))
weights = [(int(solution[j,0]*den),int(solution[n+j,0]*den)) for j in range(n)]

def rotate(pair, n):
    a,b = pair
    return [(a,b),(-b,a),(-a,-b),(b,-a)][n % 4]

def plus_into(table, key, pair):
    a,b = table[key]
    table[key] = a+pair[0],b+pair[1]

def canonical(r):
    return tuple((x-r[0])%4 for x in r)

matrices = data["matrices"]
bases = [r for mat in matrices for r in mat]
which_row = {canonical(r):j for j,r in enumerate(bases)}
mult = defaultdict(lambda:(0,0))
for row, weight in zip(rows,weights):
    if weight == (0,0):
        continue
    m = row["exponents"]
    r = matrices[row["seed"][0]][row["seed"][1]]
    for g in data["group"]:
        perm, ph, sign = g["p"],g["ph"],g["anti"]
        s, ex = [0]*10, [0]*10
        for j in range(10):
            s[perm[j]] = sign*(r[j]-ph[j])%4
            ex[perm[j]] = sign*m[j]
        q = sum(a*b for a,b in zip(m,ph))
        plus_into(mult,(which_row[canonical(s)],tuple(ex)),rotate(weight,q))

terms=[(j,m,a,b) for (j,m),(a,b) in sorted(mult.items()) if a or b]
constant=den*len(data["group"])
factor=reduce(gcd,(v for j,m,a,b in terms for v in (a,b)),constant)
constant//=factor
terms=[(j,m,a//factor,b//factor) for j,m,a,b in terms]

# Check the original equations with ten independent, signed exponent
# coordinates. Neither orbit compression nor reduction mod 13 is used here.
expanded=defaultdict(lambda:(0,0))
for row,m,a,b in terms:
    r=bases[row]
    for j in range(10):
        for k in range(10):
            if j==k:
                continue
            key=list(m)
            key[j]+=1
            key[k]-=1
            plus_into(expanded,tuple(key),rotate((a,b),r[k]-r[j]))
assert {k:v for k,v in expanded.items() if any(v)} == {(0,)*10:(constant,0)}
weight_indices = {}
lines = []
for row, exponents, real, imag in terms:
    index = weight_indices.setdefault((real, imag), len(weight_indices))
    key = sum((v+3)*8**j for j,v in enumerate(exponents))
    lines.append(f"{row} {key} {index}")
blocks = [";".join(lines[i:i+40]) for i in range(0,len(lines),40)]
pages = ["\n".join(blocks[i:i+24]) for i in range(0,len(blocks),24)]
rebuilt = {
    "weights.txt":"\n".join(f"{a} {b}" for a,b in weight_indices),
    "multipliers.txt":"\n\n".join(pages),
}
for name, contents in rebuilt.items():
    assert contents == (here.parent/name).read_text(encoding="ascii"), name
assert str(constant) in (here.parent/"Certificate.lean").read_text(encoding="utf8")
print("Both Lean input files reproduced exactly, ignoring text line endings.")
print("rows",n,"terms",len(terms),"expanded monomials",len(expanded),
      "constant digits",len(str(constant)),"L1 height",sum(abs(a)+abs(b) for _,_,a,b in terms)/constant,flush=True)
