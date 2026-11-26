# Verifying the certificate data

The default `lake build` checks the four plain-text files below. The optional commands here regenerate the finite witnesses and the integer identity independently of the Lean evaluator. Run them from the repository root in a clean checkout.

| File | Contents and origin | Checked by |
| --- | --- | --- |
| [aalto-bh4-10.txt](../aalto-bh4-10.txt) | Ten order-ten Hadamard representatives in Aalto catalogue order. Each line contains ten rows. The digits 0 through 3 denote powers of $i$. | [Catalogue.lean](../Catalogue.lean), [MainResult.lean](../MainResult.lean), [Distinct.lean](../Distinct.lean) |
| [single-leaf-certificates.txt](../single-leaf-certificates.txt) | An explicit coordinate permutation and row and column phases for each of the 1,284 terminal matrices in the search. | [LeafCertificates.lean](../LeafCertificates.lean), [LeafCoverage.lean](../LeafCoverage.lean) |
| [weights.txt](../weights.txt) | Gaussian-integer coefficients in the Laurent identity for the reference triple. | [Certificate.lean](../Certificate.lean) |
| [multipliers.txt](../multipliers.txt) | The equation row, encoded Laurent monomial and coefficient index for each of the 24,140 terms in that identity. | [Certificate.lean](../Certificate.lean), [StrongTriple.lean](../StrongTriple.lean) |

The single-matrix representatives come from the order-ten catalogue of Lampio, Szöllősi and Östergård. The two reference matrices used for the Laurent identity are transcribed in `phaseTable` from Table 1 of Best and Kharaghani. [Aalto catalogue](https://wiki.aalto.fi/pages/viewpage.action?pageId=63546913) · [Catalogue paper](https://arxiv.org/abs/1204.5164) · [Table 1](https://arxiv.org/pdf/1209.4315) · [Lean phase table](../ComplexBridge.lean)

## Regenerate the catalogue witnesses

With Node.js available, run

~~~sh
node reproduce/leaf-certificates.mjs
git diff --exit-code -- single-leaf-certificates.txt
~~~

The script writes `single-leaf-certificates.txt`. In a clean checkout the second command exits successfully with an empty diff. The separate Lean search proves that these witnesses cover all terminal matrices.

## Recompute the Laurent identity

Use Python 3.12 with Node.js on the same PATH. In a Python environment, run

~~~sh
python -m pip install -r reproduce/requirements.txt
python reproduce/recover.py
~~~

The script reads the two reference matrices, uses reduction modulo 13 to select independent rows, solves an exact rational system, then expands the original ten-variable Laurent expression with integer arithmetic. It checks the nonzero constant and compares the reconstructed weights and multipliers with both tracked files, ignoring line-ending differences. A successful run reports 610 selected rows, 24,140 multiplier terms and a constant with 313 decimal digits. [Rational reconstruction and expansion](recover.py) · [Orbit computation](orbits.cjs)
