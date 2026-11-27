import OctSixtyGlobalCore
import OctSixtyScan
import OctAlphabet

open scoped ComplexConjugate
namespace MUB10Oct.Sixty
open MUB10 MUB10Robust MUB10Radius

theorem sixty_mates_verified : SixtyMates := catalogue8_mate

theorem eight_relative_no_vector_of_coverage (hc : SingleOctClassification)
    (X : Ix → V) (hm : MUBPair X) (hx : ∀ a, RelativeOct (X a)) (v : V)
    (flat : ∀ j, Complex.normSq (v j)=1/10) :
    ¬ ∀ a, Complex.normSq (rowSum (MUB10Robust.normalized (X a)) v)=1/10 :=
  relative_oct_exclusion hc sixty_mates_verified X hm hx v flat

theorem complete_other_nine_outside_eighth_of_coverage (hc : SingleOctClassification)
    (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) (p : Fin 10)
    (hp : ∀ r, RelativeOct (F p r)) (q : Fin 10) (hq : q≠p) :
    ∃ r j, ∀ k : O, F q r j≠F q r 0*val8 k :=
  complete_other_nine hc sixty_mates_verified F hf p hp q hq

/-- Every rectangular cross-ratio across the twenty rows is a fourth root.
This also applies when the two rows come from different bases. -/
theorem rectangular_cross_ratio_even_of_coverage (hc : SingleOctClassification) (P : Ix → OQ) (hm : MUBPair (fun a => phase8 (P a)))
    (a b : Ix) (i j : Fin 10) :
    bit ((P a i-P a j)-(P b i-P b j))=false := by
  obtain ⟨π,col,s,he⟩ := pair_gauge_even hc sixty_mates_verified P hm
  have closed : ∀ u v w t : O, bit u=false → bit v=false → bit w=false → bit t=false →
      bit ((u-v)-(w-t))=false := by decide
  have hh := closed _ _ _ _ (he a (π.symm i)) (he a (π.symm j)) (he b (π.symm i)) (he b (π.symm j))
  simp only [gauge8,Equiv.apply_symm_apply] at hh
  convert hh using 2; abel

open Classical in
theorem complete_nine_count_of_coverage (hc : SingleOctClassification)
    (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) :
    9 ≤ (Finset.univ.filter (fun p => ¬ ∀ r, RelativeOct (F p r))).card := by
  classical
  have small : (Finset.univ.filter (fun p => ∀ r, RelativeOct (F p r))).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    by_contra hn
    obtain ⟨r,j,hbad⟩ := complete_other_nine_outside_eighth_of_coverage hc F hf p
      (Finset.mem_filter.mp hp).2 q (Ne.symm hn)
    obtain ⟨k,he⟩ := (Finset.mem_filter.mp hq).2 r j
    exact hbad k he
  rw [Finset.filter_not,Finset.card_sdiff (Finset.subset_univ _)]
  simp only [Finset.card_univ,Fintype.card_fin]
  omega

open Classical in
theorem complete_nine_eighth_power_of_coverage (hc : SingleOctClassification)
    (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) :
    9 ≤ (Finset.univ.filter (fun p => ∃ r j, (F p r j / F p r 0)^8 ≠ 1)).card := by
  classical
  have hp (p : Fin 10) : (¬ ∀ r, RelativeOct (F p r)) ↔ ∃ r j, (F p r j / F p r 0)^8 ≠ 1 := by
    simp only [relative_eighth_power _ (hf.1 p _),not_forall]
  simpa only [hp] using complete_nine_count_of_coverage hc F hf

#print axioms sixty_mates_verified
#print axioms eight_relative_no_vector_of_coverage
#print axioms complete_other_nine_outside_eighth_of_coverage

end MUB10Oct.Sixty
