import Lean.Util.CollectAxioms
import Rectangle
import Distinct
import CurveNeighbourhood
import Earlier.Parity
import Earlier.RayExample
import OctSixtyConclusions
import OctSixtyExact
import OctRepresentatives
import OctDistinct

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
    (``MUB10.Earlier.RayExample.three_unbiased_rays, standard),
    (``MUB10Oct.Sixty.representatives_hadamard, finiteComputation),
    (``MUB10Oct.Sixty.catalogue_inequivalent, finiteComputation),
    (``MUB10Oct.Sixty.single_oct_classification, finiteComputation),
    (``MUB10Oct.Sixty.exact_cardinalities, finiteComputation),
    (``MUB10Oct.Sixty.ray_iff, finiteComputation),
    (``MUB10Oct.Sixty.mate_set_iff, finiteComputation),
    (``MUB10Oct.Sixty.eight_pair_descends, finiteComputation),
    (``MUB10Oct.Sixty.every_rectangular_cross_ratio_even, finiteComputation),
    (``MUB10Oct.Sixty.eight_relative_no_vector, finiteComputation),
    (``MUB10Oct.Sixty.complete_other_nine_outside_eighth, finiteComputation),
    (``MUB10Oct.Sixty.complete_at_least_nine_outside_eighth, finiteComputation),
    (``MUB10Oct.Sixty.complete_at_least_nine_violating_eighth_power, finiteComputation)]
  for (result, allowed) in results do
    let unexpected := (← collectAxioms result).filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{result} depends on unexpected axioms {unexpected}"
