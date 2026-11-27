import OctSixtyGlobal
import OctSingleClassification

/-! Closed statements about all order-ten octonary mutually unbiased bases. -/
namespace MUB10Oct.Sixty
open MUB10 MUB10Robust MUB10Radius
noncomputable section

/-- Both listed bases become quaternary under one common coordinate transformation
and independent scalar phases for their rays. -/
theorem eight_pair_descends (P : Ix → OQ) (hm : MUBPair (fun a => phase8 (P a))) :
    ∃ (π : Equiv.Perm (Fin 10)) (col : OQ) (s : Ix → O),
      ∀ a j, bit (gauge8 π col (s a) (P a) j)=false :=
  pair_gauge_even single_oct_classification sixty_mates_verified P hm

/-- Every rectangular cross-ratio across the twenty rows is a fourth root.
This also applies when the two rows come from different bases. -/
theorem every_rectangular_cross_ratio_even (P : Ix → OQ) (hm : MUBPair (fun a => phase8 (P a)))
    (a b : Ix) (i j : Fin 10) :
    bit ((P a i-P a j)-(P b i-P b j))=false :=
  rectangular_cross_ratio_even_of_coverage single_oct_classification P hm a b i j

/-- No physical vector, with unrestricted complex phases, can extend this
mutually unbiased triple (coordinate basis together with the two listed bases). -/
theorem eight_relative_no_vector (X : Ix → V) (hm : MUBPair X) (hx : ∀ a, RelativeOct (X a)) (v : V)
    (flat : ∀ j, Complex.normSq (v j)=1/10) :
    ¬ ∀ a, Complex.normSq (rowSum (MUB10Robust.normalized (X a)) v)=1/10 :=
  eight_relative_no_vector_of_coverage single_oct_classification X hm hx v flat

/-- In a complete eleven-basis family, with the standard basis fixed, if one of the
other ten bases has every ray eighth-root relative to its first entry, then each of
the remaining nine bases has a relative phase outside all eighth roots. -/
theorem complete_other_nine_outside_eighth (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F)
    (p : Fin 10) (hp : ∀ r, RelativeOct (F p r)) (q : Fin 10) (hq : q≠p) :
    ∃ r j, ∀ k : O, F q r j≠F q r 0*val8 k :=
  complete_other_nine_outside_eighth_of_coverage single_oct_classification F hf p hp q hq

open Classical in
theorem complete_at_least_nine_outside_eighth (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) :
    9 ≤ (Finset.univ.filter (fun p => ¬ ∀ r, RelativeOct (F p r))).card :=
  complete_nine_count_of_coverage single_oct_classification F hf

#print axioms complete_at_least_nine_outside_eighth

open Classical in
theorem complete_at_least_nine_violating_eighth_power (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) :
    9 ≤ (Finset.univ.filter (fun p => ∃ r j, (F p r j / F p r 0)^8 ≠ 1)).card :=
  complete_nine_eighth_power_of_coverage single_oct_classification F hf

#print axioms complete_at_least_nine_violating_eighth_power
#print axioms eight_pair_descends
#print axioms every_rectangular_cross_ratio_even
#print axioms eight_relative_no_vector
#print axioms complete_other_nine_outside_eighth

end
end MUB10Oct.Sixty
