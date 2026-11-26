import LeafCoverage
import LexNormal
import Complete

/-! All claims in this file are closed theorems. In particular the completeness
of the list of single four-phase matrices is an output of the proof. -/
namespace MUB10Radius
open MUB10 MUB10Catalogue MUB10Robust
noncomputable section

theorem single_bh_classification : SingleBHClassification := by
  intro A hA
  obtain ⟨σ,π,c,r,hz,hcol,hweak,hlex⟩ := lex_normal A
  let T := fun k => changeQ π c (r (σ k)) (A (σ k))
  have orth (i j : Fin 10) (hne : i ≠ j) : gramSq (pack (T i)) (pack (T j)) = 0 :=
    (gramSq_changeQ _ _ _ _ _ _).trans (hA _ _ (σ.injective.ne hne))
  obtain ⟨m,α,d,t,hm⟩ := certified_leaf_gauge T (normalized_leaf T hz hcol hweak hlex orth)
  let v := fun j => d j + c (α j)
  let w := fun j => t (σ.symm j) + r j
  refine ⟨m, α.trans π, v, w, ?_⟩
  let f := fun i => pack (changeQ (α.trans π) v (w i) (A i))
  apply (Equiv.Perm.ofFn_comp_perm σ f).symm.trans
  unfold f
  simpa only [Function.comp_def, T, changeQ_comp, w, v, Equiv.symm_apply_apply] using hm

/-- No other flat complex ray is unbiased to two ten-dimensional MUBs whose
raw entries all lie at distance at most δ from fourth roots in one common
coordinate system, for any δ strictly below 1/8855600. -/
theorem near_quaternary_no_ray (X : Ix → V) (P : Ix → Q) (hm : MUBPair X)
    {δ : ℝ} (hδ : δ < radius) (hc : ∀ a, near (X a) (phaseOf (P a)) δ)
    (z : V) (hz : unitRow z) : ¬ ∀ a, Complex.normSq (rowSum (X a) z) = 10 :=
  global_radius single_bh_classification X P hm hδ hc z hz

/-- The same assertion for ordinary normalized states and Born probabilities. -/
theorem near_quaternary_strongly_unextendible (X : Ix → V) (P : Ix → Q) (hm : MUBPair X)
    {δ : ℝ} (hδ : δ < radius) (hc : ∀ a, near (X a) (phaseOf (P a)) δ)
    (v : V) (flat : ∀ j, Complex.normSq (v j) = 1/10) :
    ¬ ∀ a, Complex.normSq (rowSum (MUB10Robust.normalized (X a)) v) = 1/10 := by
  intro hv
  let z := phaseCoordinates v
  have hz : unitRow z := by
    intro j
    have h := flat_coordinates v flat j
    change Complex.normSq (z j) = 1 at h
    rw [← Complex.sq_norm] at h
    nlinarith [norm_nonneg (z j)]
  have root_ne : rootTen ≠ 0 := by
    intro h
    have hh := rootTen_norm
    rw [h] at hh
    norm_num at hh
  have back : MUB10Robust.normalized z = v := by
    funext j
    simp [MUB10Robust.normalized,z,phaseCoordinates, mul_div_cancel_left₀,root_ne]
  apply near_quaternary_no_ray X P hm hδ hc z hz
  intro a
  have h := normalized_probability (X a) z
  rw [back, hv] at h
  linarith

theorem quaternary_strongly_unextendible (P : Ix → Q)
    (hm : MUBPair (fun a => phaseOf (P a))) (v : V)
    (flat : ∀ j, Complex.normSq (v j) = 1/10) :
    ¬ ∀ a, Complex.normSq (rowSum (MUB10Robust.normalized (phaseOf (P a))) v) = 1/10 :=
  near_quaternary_strongly_unextendible _ P hm (δ := 0) (by norm_num [radius])
    (by intro a j; simp) v flat

theorem complete_at_most_one (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) :
    Set.Subsingleton {p | CloseToFourth (F p)} := by
  apply at_most_one_of_exclusion _ F hf
  intro X P δ hm hδ hc z hz
  exact near_quaternary_no_ray X P hm hδ hc z hz

open Classical in
theorem complete_at_least_nine_far (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) :
    9 ≤ (Finset.univ.filter (fun p => ¬ CloseToFourth (F p))).card :=
  nine_far_of_subsingleton F (complete_at_most_one F hf)

#print axioms single_bh_classification
#print axioms near_quaternary_strongly_unextendible
#print axioms complete_at_least_nine_far
end
end MUB10Radius
