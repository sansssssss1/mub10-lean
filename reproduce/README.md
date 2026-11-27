# Verifying the certificate data

Run the commands below from the repository root. They reproduce the finite witnesses and the integer identity independently of the Lean evaluator.

## Fourth-root certificate data

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

## Reproduce the eighth-root classification and pair counts

With Node.js 20 or later, run the read-only check

~~~sh
node reproduce/octonary.mjs
~~~

It checks the original Aalto file, verifies orthogonality of its 60 representatives, regenerates all three witness files in memory, and compares them byte for byte with the tracked files. The terminal matrices occur in lexicographic order. For each fixed catalogue representative, a ray has first coordinate 1 and a mate is an unordered orthogonal set of ten such rays. In the **one-based Aalto order**, representative 9 has 36 mates and representative 28 has one. The other 58 have none. The Lean checks also identify mates by their underlying sets of rays. [Generator](octonary.mjs) · [Search certificate](../OctSixtyScan.lean) · [Exact set counts](../OctSixtyExact.lean)

| File | Origin and contents | SHA-256 |
| --- | --- | --- |
| [BH-10-8.txt](../BH-10-8.txt) | Original Aalto attachment, 6,420 bytes. Each of the 60 lines begins with `BH1::8` and encodes 100 eighth-root exponents in row-major order. | `c1e2f93df98d7954f56cbd859fce7efdd28391e818746302d22b3ddc256907cb` |
| [oct-leaf-certificates.txt](../oct-leaf-certificates.txt) | For each of 15,564 leaves, ten rows, a zero-based catalogue index, the inverse column permutation and two vectors of phase shifts. | `d658c3e8611f6e9b74b23ad226469c1e5c6a299e52d0259ad1660e38ceb26ac3` |
| [oct-ray-witnesses.txt](../oct-ray-witnesses.txt) | One line per catalogue matrix, containing the space-separated normalized rays unbiased to it. A dash records an empty list. | `b7bf7af78476db0fa3c2d414f406e2df4657fe129a50bd823d5ffb1bfc169373` |
| [oct-mate-witnesses.txt](../oct-mate-witnesses.txt) | One line per catalogue matrix. Each mate has ten space-separated rows and a semicolon separates successive mates. A dash records an empty list. | `43889eddd8cd5c8aa044b8c70afed55f5cfb48bc44a99d9fe2bdd558d483aa39` |

The catalogue is the electronic supplement to *Orderly generation of Butson Hadamard matrices* by Pekka H. J. Lampio, Patric R. J. Östergård and Ferenc Szöllősi. Aalto lists the published dataset under CC BY 4.0. The copy of `BH-10-8.txt` in this repository preserves the original attachment byte for byte. [Aalto dataset and licence](https://research.aalto.fi/en/datasets/dataset-for-orderly-generation-of-butson-hadamard-matrices/) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) · [Original attachment](https://wiki.aalto.fi/download/attachments/120482261/BH-10-8.txt) · [Paper](https://arxiv.org/abs/1707.02287)

For an independent check of terminal coverage, run

~~~sh
node reproduce/octonary.mjs --forward
~~~

The reverse search dephases every choice of anchor row and column in the published catalogue, orders the columns within each equal prefix, and records an explicit monomial equivalence for every resulting leaf. The forward search starts from a zero-exponent row. It generates all 992,376 normalized orthogonal rows from their exponent multiplicities, finds 35 possible sorted second rows, and extends each choice by mutually orthogonal rows while keeping rows and columns lexicographically ordered. It compares the two **sets of matrices**, including all 15,564 entries. [Reverse search](octonary-leaves.mjs) · [Forward search](octonary-forward.mjs)

The ray search splits the nine free coordinates into four and five. It matches their overlap sums against the first two anchor rows, checks each match against the remaining eight rows, and enumerates the ten-cliques of the orthogonality graph. All computations use integers. For a sum expressed as `a + bi + ζ(c + di)`, where `ζ` is a primitive eighth root, the four coefficients are encoded with radix 32. The squared modulus equals 10 for exactly 16 possible coefficient tuples. [Ray and mate enumeration](octonary-rays.mjs) · [Complex overlap equivalence](../OctSixtyPhysical.lean)

To regenerate the three witness files in a separate directory, use

~~~sh
node reproduce/octonary.mjs --output-dir ./regenerated
~~~

`--data-dir DIR` selects a different directory containing the input catalogue and, in comparison mode, the tracked witnesses. All commands use local files and Node.js built-ins.
