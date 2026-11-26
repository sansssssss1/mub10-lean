import Deformation
import Neighbourhood

/-! The actual circle of triples and the open pair obstruction in the same
physical coordinates. The external Fourier theorem is an explicit premise of
the final implication; the existence of each displayed triple is unconditional. -/
namespace MUB10Curve
open MUB10 MUB10.Deformation MUB10Neighbourhood
open scoped BigOperators ComplexConjugate Topology
noncomputable section

private def slot (j : Fin 10) : Index := (j.val : Fin 5)
private def bit (j : Fin 10) := decide (5 ≤ j.val)
private def entry (u : Vec) (j : Fin 10) : ℂ :=
  if bit j then (u (slot j)).2 else (u (slot j)).1

private theorem same_index : ∀ i j : Fin 10, slot i = slot j ∧ bit i = bit j ↔ i = j := by decide

private lemma flat_entry (u : Vec) (hu : Flat u) (j : Fin 10) :
    Complex.normSq (entry u j) = 1/10 := by
  unfold entry
  split
  · exact (hu _).2
  · exact (hu _).1

private def row (u : Vec) (hu : Flat u) : Row := fun j => ⟨rootTen * entry u j, by
  change dist (rootTen * entry u j) 0 = 1
  rw [dist_zero_right]
  have h : ‖rootTen * entry u j‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_mul, rootTen_norm, flat_entry u hu]; norm_num
  nlinarith [norm_nonneg (rootTen * entry u j)]⟩

private lemma row_vector (u : Vec) (hu : Flat u) : vector (row u hu) = entry u := by
  funext j
  change rootTen * entry u j / rootTen = entry u j
  apply mul_div_cancel_left₀
  intro eqn
  have hh := rootTen_norm
  rw [eqn] at hh
  norm_num at hh

private lemma entry_dot (u v : Vec) : rowSum (entry u) (entry v) = overlap u v := by
  have fst (w : Vec) (i : Fin 5) : entry w (Fin.castAdd 5 i) = (w i).1 := by fin_cases i <;> rfl
  have snd (w : Vec) (i : Fin 5) : entry w (Fin.natAdd 5 i) = (w i).2 := by fin_cases i <;> rfl
  unfold rowSum
  rw [Fin.sum_univ_add (a := 5) (b := 5)]
  simp only [fst,snd,overlap,dot,Finset.sum_add_distrib]

private lemma prob_rows (u v : Vec) (hu : Flat u) (hv : Flat v) :
    prob (row u hu) (row v hv) = Complex.normSq (overlap u v) := by
  rw [prob_eq_overlap, row_vector, row_vector, entry_dot]

def phases (t : UnitPhase) := deformedPhases (curveX t) (curveY t)
def seed (t : UnitPhase) := explicitSeed (curveX t) (curveY t)
def anchorBasis (t : UnitPhase) : Basis := fun i =>
  row (anchor (phases t) (slot i) (bit i)) (anchor_flat _ _ _)
def thirdBasis (t : UnitPhase) : Basis := fun i =>
  row (companion (phases t) (seed t) (slot i) (bit i)) (companion_flat _ _ (circle_seed t).1 _ _)

theorem actual_triple (t : UnitPhase) : IsBasis (anchorBasis t) ∧ Third (anchorBasis t) (thirdBasis t) := by
  constructor
  · intro i j
    simp only [anchorBasis, prob_rows, anchor_gram, same_index]
    split <;> simp
  constructor
  · intro i j
    simp only [thirdBasis, prob_rows]
    rw [companion_gram (phases t) (seed t) (circle_seed t).1 (slot i) (bit i) (slot j) (bit j)]
    simp only [same_index]
    split <;> simp
  · intro i j
    rw [anchorBasis, thirdBasis, prob_rows]
    exact companion_unbiased _ _ (circle_seed t).2 _ _ _ _

theorem anchor_continuous : ContinuousAt anchorBasis onePhase := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
  change ContinuousAt (fun t => rootTen * entry (anchor (phases t) (slot i) (bit i)) j) onePhase
  have hconj : ContinuousAt (fun t => conj (deformedPhases (curveX t) (curveY t) (slot j) : ℂ))
      onePhase := Complex.continuous_conj.continuousAt.comp (anchor_phases_continuous_at_fourier _)
  cases hi : bit i <;> cases hj : bit j <;>
    simp only [entry, anchor, first, clock, scale, hi, hj, Bool.false_eq_true,
      if_false, if_true, phases] <;> fun_prop (disch := assumption)

/-- Yang et al., Theorem B(iv), supplies the antecedent for this Fourier endpoint.
The same parameter neighbourhood works simultaneously for every third basis. -/
theorem near_fourier_curve
    (fourier : ∀ B, Third (anchorBasis onePhase) B →
      ∀ x, ¬ UnbiasedRay (anchorBasis onePhase) B x) :
    ∀ᶠ t in 𝓝 onePhase, Third (anchorBasis t) (thirdBasis t) ∧
      ∀ B, Third (anchorBasis t) B → ∀ x, ¬ UnbiasedRay (anchorBasis t) B x := by
  obtain ⟨ε,hε,h⟩ := pair_neighbourhood _ (actual_triple onePhase).1 fourier
  have ev := anchor_continuous (Metric.ball_mem_nhds _ hε)
  filter_upwards [ev] with t ht
  exact ⟨(actual_triple t).2, h _ ht (actual_triple t).1⟩

/-- On a positive real interval the anchor escapes the n-th root matrices;
the triple really exists and the Fourier hypothesis rules out any fourth ray. -/
theorem positive_curve (n : ℕ) (hn : 0 < n)
    (fourier : ∀ B, Third (anchorBasis onePhase) B →
      ∀ x, ¬ UnbiasedRay (anchorBasis onePhase) B x) :
    ∀ᶠ s : ℝ in 𝓝 0, 0 < s →
      let t := realParameter s
      ¬ RephasableToRoots (phases t) n ∧ Third (anchorBasis t) (thirdBasis t) ∧
        ∀ x, ¬ UnbiasedRay (anchorBasis t) (thirdBasis t) x := by
  have hc : Filter.Tendsto realParameter (𝓝 0) (𝓝 onePhase) := by
    simpa only [← realParameter_zero] using realParameter_continuous.continuousAt (x := 0)
  filter_upwards [hc (near_fourier_curve fourier), near_fourier_non_equivalent n hn] with s hs hr
  intro hpos
  exact ⟨hr hpos, hs.1, hs.2 _ hs.1⟩

#print axioms actual_triple
#print axioms near_fourier_curve
#print axioms positive_curve
end
end MUB10Curve
