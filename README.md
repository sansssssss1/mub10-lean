# A quaternary phase obstruction for mutually unbiased bases in dimension ten

[中文说明](README.zh-CN.md)

Suppose three orthonormal bases $E,H,K$ of $\mathbb C^{10}$ are pairwise mutually unbiased. This means that every squared overlap between vectors from different bases equals $1/10$. This Lean 4 project proves an explicit condition under which **no complex unit vector is unbiased to all three bases**.

## The theorem

Fix the phases of the coordinate basis $E$. Write the twenty vectors of $H$ and $K$ as rows in these coordinates and multiply every entry by $\sqrt{10}$, giving unit-modulus entries $X_{rj}$. Let $\mu_4=\{1,i,-1,-i\}$. The triple is strongly unextendible whenever

$$
\max_{r,j}\min_{\omega\in\mu_4}|X_{rj}-\omega| < \frac{1}{8{,}855{,}600}.
$$

Both matrices use the same coordinate phases. The bound is a chordal distance in the complex plane and includes the case where every entry lies in $\mu_4$. The candidate fourth ray may have arbitrary complex phases. [MainResult.lean](MainResult.lean)

**Consequence for eleven bases.** If a complete set exists, choose any one of its bases as $E$ and fix the coordinate phases. Of the ten remaining bases, at least nine must each have an entry whose distance from $\mu_4$, after the same scaling, is at least $1/8{,}855{,}600$. The existence of a complete set in dimension ten remains open. A companion theorem gives a phase-invariant obstruction using products over four entries of the two matrices. [Counting theorem](MainResult.lean) · [Four-entry obstruction](Rectangle.lean) · [Yang et al., §4](https://arxiv.org/html/2611.21188v1#S4)

## How the proof works

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

The build checks the committed certificate data and audits the axiom dependencies of the principal results. For the quaternary main theorem, `#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` and `Lean.ofReduceBool`. The last dependency comes from `native_decide`, which uses Lean's native evaluator for the finite searches and integer identities. [Axiom audit](CheckAxioms.lean) · [GitHub Actions workflow](.github/workflows/verify.yml)

The reproduction guide identifies the four data files and gives commands for regenerating the 1,284 equivalence witnesses and the Laurent certificate using Node.js and Python with python-flint 0.9.0. [Certificates and data](reproduce/README.md)

## License

The original Lean code, reproduction scripts and documentation are released under the MIT License. The data guide credits the published matrices and their authors. [License](LICENSE) · [Data sources](reproduce/README.md)
