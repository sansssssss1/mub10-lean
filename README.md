# Strong unextendibility of octonary mutually unbiased triples in dimension ten

[中文说明](README.zh-CN.md)

Let $E,H,K$ be three pairwise mutually unbiased orthonormal bases of $\mathbb C^{10}$. Fix the coordinate phases of $E$. If every ray of $H$ and $K$ has all coordinate ratios $v_j/v_0$ in $\mu_8$, the eighth roots of unity, **no complex unit vector is unbiased to all three bases**. A ray may carry any overall phase. The vector tested for extension ranges over all of $\mathbb C^{10}$. [Paper (PDF)](paper/mub10-octonary.pdf) · [LaTeX source](paper/mub10-octonary.tex) · [Lean statements](OctSixtyConclusions.lean)

## What this excludes for eleven bases

Suppose a complete family of eleven bases exists. Take **any** member as $E$ and use one choice of its coordinate phases for the other ten. At least nine of the ten must each contain a vector $v$ and a coordinate $j$ with $(v_j/v_0)^8\ne1$. Thus a complete family could contain a single octonary basis relative to $E$, or none. The same obstruction already rules out adjoining a fourth basis to an octonary triple. The unrestricted eleven-basis existence problem remains open. [Power-form counting theorem](OctSixtyConclusions.lean) · [Yang et al. on the dimension-ten problem](https://arxiv.org/abs/2611.21188)

Lean verifies that the 60 published order-ten octonary Hadamard representatives are valid, pairwise inequivalent and cover all inputs. The proof checks 15,564 terminal matrices. In the published order, only representatives 9 and 28 admit an octonary unbiased mate, with respectively 36 and 1 such mates when the anchor is fixed and the mate is an unordered set of dephased rays. In each case both matrices become quaternary under a common change of coordinates and separate row phases. [Classification coverage](OctSingleClassification.lean) · [Inequivalence](OctDistinct.lean) · [Exact mate counts](OctSixtyExact.lean) · [Published classification](https://doi.org/10.1090/mcom/3453)

## The quaternary neighbourhood theorem

Fix the phases of the coordinate basis $E$. Write the twenty vectors of $H$ and $K$ as rows in these coordinates and multiply every entry by $\sqrt{10}$, giving unit-modulus entries $X_{rj}$. Let $\mu_4=\{1,i,-1,-i\}$. The triple is strongly unextendible whenever

$$
\max_{r,j}\min_{\omega\in\mu_4}|X_{rj}-\omega| < \frac{1}{8{,}855{,}600}.
$$

Both matrices use the same coordinate phases. The bound is a chordal distance in the complex plane and includes the case where every entry lies in $\mu_4$. The candidate fourth ray may have arbitrary complex phases. [MainResult.lean](MainResult.lean)

**Consequence for eleven bases.** If a complete set exists, choose any one of its bases as $E$ and fix the coordinate phases. Of the ten remaining bases, at least nine must each have an entry whose distance from $\mu_4$, after the same scaling, is at least $1/8{,}855{,}600$. The existence of a complete set in dimension ten remains open. A companion theorem gives a phase-invariant obstruction using products over four entries of the two matrices. [Counting theorem](MainResult.lean) · [Four-entry obstruction](Rectangle.lean) · [Yang et al., §4](https://arxiv.org/html/2611.21188v1#S4)

## How the quaternary proof works

1. Lean reduces arbitrary quaternary Hadamard matrices of order ten to 1,284 leaves of a lexicographic search. A checked equivalence witness maps each leaf to one of ten catalogue representatives. [Coverage proof](LeafCoverage.lean) · [Inequivalence proof](Distinct.lean) · [Original classification by Lampio, Szöllősi and Östergård](https://arxiv.org/abs/1204.5164)
2. For each representative the search checks all $4^9$ possible rows with first entry fixed to 1 and enumerates mutually orthogonal ten-row mates. Two representatives admit mates, with counts 36 and 1. Allowing a swap of $H$ and $K$, all 37 outputs are equivalent to the same Best–Kharaghani pair. [Mate enumeration](Catalogue.lean) · [Best and Kharaghani, Table 1](https://arxiv.org/pdf/1209.4315) · [Published mate counts, Table 4](https://doi.org/10.1002/jcd.70006)
3. For a state unbiased to $E$, an integer Laurent-polynomial certificate forces at least one of the twenty probabilities for the reference pair to differ from $1/10$ by at least $1/4{,}427{,}800$. Rounding nearby phases preserves the required integer squared overlaps. Moving one measurement row by an entrywise phase error of $\delta$ changes its probability by at most $2\delta$, giving the stated radius. [Probability gap](Gap.lean) · [Rounding and stability](Robust.lean)

Two earlier calculations are also available in Lean 4. One gives a parity obstruction for integer encodings with an odd denominator. The other checks the exact overlaps of three pairwise unbiased flat rays. [Parity.lean](Earlier/Parity.lean) · [RayExample.lean](Earlier/RayExample.lean)

## Fourier deformation

The project also constructs an explicit family of triples with a Fourier endpoint. Lean checks that the bases are mutually unbiased throughout the family. The strong unextendibility result along the curve takes the Fourier endpoint obstruction from Yang et al., Theorem B(iv), as an explicit hypothesis. The quaternary theorem above is independent of that hypothesis. [Deformation.lean](Deformation.lean) · [CurveNeighbourhood.lean](CurveNeighbourhood.lean) · [Yang et al.](https://arxiv.org/abs/2611.21188) · [Phase-deformed Fourier construction](https://arxiv.org/html/2610.12180v1#S6)

## Verify locally

With elan installed, run these commands from the repository root. The toolchain and mathlib are pinned to version 4.19.0.

~~~sh
lake exe cache get
lake build
~~~

The default build includes the octonary and quaternary theorems, the certificate data and the axiom audit. Both main exclusions report `propext`, `Classical.choice`, `Quot.sound` and `Lean.ofReduceBool`. The last dependency comes from `native_decide`, which uses Lean's native evaluator for the finite searches and integer identities. [Axiom audit](CheckAxioms.lean) · [GitHub Actions workflow](.github/workflows/verify.yml)

To independently recompute the octonary data and repeat the forward search, run the following command from the same directory. The reproduction guide also covers the earlier quaternary witnesses and the Laurent identity. [Data, sources and reproduction commands](reproduce/README.md)

~~~sh
node reproduce/octonary.mjs --forward
~~~

To build the paper from its source, run `tectonic paper/mub10-octonary.tex` from the repository root.
