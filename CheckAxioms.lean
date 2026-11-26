import Lean.Util.CollectAxioms
import Rectangle
import Distinct
import CurveNeighbourhood
import Earlier.Parity
import Earlier.RayExample

/-! Audit the axiom dependencies of the public conclusions. The Fourier
endpoint is a premise in the type of `positive_curve`, visible to its caller. -/
open Lean

run_cmd
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let finiteComputation := standard.push ``Lean.ofReduceBool
  let results := #[
    (``MUB10Radius.single_bh_classification, finiteComputation),
    (``MUB10Radius.catalogue_inequivalent, finiteComputation),
    (``MUB10Radius.quaternary_strongly_unextendible, finiteComputation),
    (``MUB10Radius.near_quaternary_strongly_unextendible, finiteComputation),
    (``MUB10Radius.complete_at_least_nine_far, finiteComputation),
    (``MUB10Radius.rectangle_far, finiteComputation),
    (``MUB10Curve.actual_triple, standard),
    (``MUB10Curve.positive_curve, standard),
    (``MUB10.Earlier.Parity.no_three_integer_phase_vectors, standard),
    (``MUB10.Earlier.RayExample.three_unbiased_rays, standard)]
  for (result, allowed) in results do
    let unexpected := (← collectAxioms result).filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{result} depends on unexpected axioms {unexpected}"
