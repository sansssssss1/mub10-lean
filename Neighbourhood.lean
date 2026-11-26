import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic.Linarith
import ComplexBridge

/-!
Openness of the obstruction to adding one ray together with a third unbiased basis.
Entries of each row are unnormalized phases. Dividing them by √10 gives physical
unit vectors flat in the standard basis. The metric is maximum entrywise chordal distance.

The Fourier-pair hypothesis is established externally by Yang, Liu, Li and Deng,
arXiv:2611.21188, Theorem B(iv). Their Section 4 already notes the ordinary
open neighbourhood excluding four entire bases. Here compactness also treats
one putative unbiased ray, while allowing error in all simultaneous equations.
-/
open scoped BigOperators ComplexConjugate
namespace MUB10Neighbourhood
noncomputable section

abbrev Row := Fin 10 → Circle
abbrev Basis := Fin 10 → Row

/-- Squared overlap after dividing both phase rows by √10. -/
def prob (a b : Row) : ℝ :=
  Complex.normSq (∑ j, conj (a j : ℂ) * (b j : ℂ)) / 100

def vector (a : Row) (j : Fin 10) : ℂ := (a j : ℂ) / MUB10.rootTen

theorem prob_eq_overlap (a b : Row) : prob a b = Complex.normSq (MUB10.rowSum (vector a) (vector b)) := by
  unfold MUB10.rowSum vector
  simp only [map_div₀, MUB10.conj_rootTen, div_mul_div_comm]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Complex.normSq_mul, Complex.normSq_inv,
    MUB10.rootTen_norm]
  unfold prob
  ring

/-- Every physical vector unbiased to the coordinate basis is represented by a phase row. -/
theorem represents_all_flat (v : Fin 10 → ℂ) (hv : ∀ j, Complex.normSq (v j) = 1/10) :
    ∃ a : Row, vector a = v := by
  have hp := MUB10.flat_coordinates v hv
  have unit (j) : ‖MUB10.phaseCoordinates v j‖ = 1 := by
    have eq := (Complex.sq_norm _).trans (hp j)
    nlinarith [norm_nonneg (MUB10.phaseCoordinates v j)]
  let a : Row := fun j => ⟨MUB10.phaseCoordinates v j, by
    change dist (MUB10.phaseCoordinates v j) 0 = 1
    simpa using unit j⟩
  refine ⟨a,funext fun j => ?_⟩
  change MUB10.rootTen * v j / MUB10.rootTen = v j
  have hne : MUB10.rootTen ≠ 0 := by
    intro he
    have hh := MUB10.rootTen_norm
    rw [he] at hh
    norm_num at hh
  field_simp

def IsBasis (H : Basis) : Prop :=
  ∀ i j, prob (H i) (H j) = if i = j then 1 else 0

def Third (H B : Basis) : Prop :=
  IsBasis B ∧ ∀ i j, prob (H i) (B j) = 1/10

def UnbiasedRay (H B : Basis) (x : Row) : Prop :=
  (∀ i, prob (H i) x = 1/10) ∧ ∀ i, prob (B i) x = 1/10

def ThirdWithin (H B : Basis) (t : ℝ) : Prop :=
  (∀ i j, |prob (B i) (B j) - (if i = j then 1 else 0)| ≤ t) ∧
  ∀ i j, |prob (H i) (B j) - 1/10| ≤ t

def RayWithin (H B : Basis) (x : Row) (t : ℝ) : Prop :=
  (∀ i, |prob (H i) x - 1/10| ≤ t) ∧ ∀ i, |prob (B i) x - 1/10| ≤ t

@[simp] theorem thirdWithin_zero (H B : Basis) : ThirdWithin H B 0 ↔ Third H B := by
  simp [ThirdWithin, Third, IsBasis, abs_nonpos_iff, sub_eq_zero]

@[simp] theorem rayWithin_zero (H B : Basis) (x : Row) : RayWithin H B x 0 ↔ UnbiasedRay H B x := by
  simp [RayWithin, UnbiasedRay, abs_nonpos_iff, sub_eq_zero]

private lemma prob_cont {X : Type*} [TopologicalSpace X] (a b : X → Row)
    (ha : Continuous a) (hb : Continuous b) : Continuous fun x => prob (a x) (b x) := by
  unfold prob
  apply Continuous.div_const
  apply Complex.continuous_normSq.comp
  apply continuous_finset_sum
  intro j _
  exact (Complex.continuous_conj.comp (continuous_subtype_val.comp
    ((continuous_apply j).comp ha))).mul (continuous_subtype_val.comp ((continuous_apply j).comp hb))

private lemma closed_forall {X I : Type*} [TopologicalSpace X] {P : I → X → Prop}
    (h : ∀ i, IsClosed {x | P i x}) : IsClosed {x | ∀ i, P i x} := by
  simpa only [Set.setOf_forall] using isClosed_iInter h

private abbrev WitnessSpace := (Basis × ℝ) × (Basis × Row)

private def admissible : Set WitnessSpace :=
  {q | ThirdWithin q.1.1 q.2.1 q.1.2 ∧ RayWithin q.1.1 q.2.1 q.2.2 q.1.2}

private lemma admissible_closed : IsClosed admissible := by
  have hh (i : Fin 10) : Continuous (fun q : WitnessSpace => q.1.1 i) :=
    (continuous_apply i).comp (continuous_fst.comp continuous_fst)
  have hb (i : Fin 10) : Continuous (fun q : WitnessSpace => q.2.1 i) :=
    (continuous_apply i).comp (continuous_fst.comp continuous_snd)
  have hx : Continuous (fun q : WitnessSpace => q.2.2) := continuous_snd.comp continuous_snd
  have ht : Continuous (fun q : WitnessSpace => q.1.2) := continuous_snd.comp continuous_fst
  unfold admissible ThirdWithin RayWithin
  apply IsClosed.inter
  · apply IsClosed.inter
    · exact closed_forall fun i => closed_forall fun j =>
        isClosed_le ((prob_cont _ _ (hb i) (hb j)).sub continuous_const).abs ht
    · exact closed_forall fun i => closed_forall fun j =>
        isClosed_le ((prob_cont _ _ (hh i) (hb j)).sub continuous_const).abs ht
  · apply IsClosed.inter
    · exact closed_forall fun i =>
        isClosed_le ((prob_cont _ _ (hh i) hx).sub continuous_const).abs ht
    · exact closed_forall fun i =>
        isClosed_le ((prob_cont _ _ (hb i) hx).sub continuous_const).abs ht

/-- Even the simultaneous approximate equations for an arbitrary third basis and
an arbitrary flat ray have no solution for a positive common error tolerance.
No choice of a third basis or bounds on its distance from any named basis are needed. -/
theorem robust_pair_neighbourhood (H₀ : Basis)
    (h₀ : ∀ B, Third H₀ B → ∀ x, ¬ UnbiasedRay H₀ B x) :
    ∃ ε > (0 : ℝ), ∀ H, dist H H₀ < ε → ∀ B x,
      ¬ (ThirdWithin H B ε ∧ RayWithin H B x ε) := by
  have hc : IsClosed (Prod.fst '' admissible) :=
    isClosedMap_fst_of_compactSpace _ admissible_closed
  have outside : (H₀, (0 : ℝ)) ∈ (Prod.fst '' admissible)ᶜ := by
    rintro ⟨⟨⟨H,t⟩,B,x⟩,hq,heq⟩
    change (H,t) = (H₀,0) at heq
    cases heq
    obtain ⟨hthird,hray⟩ := hq
    exact h₀ B ((thirdWithin_zero _ _).mp hthird) x ((rayWithin_zero _ _ _).mp hray)
  obtain ⟨r,hr,ball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl _ outside
  refine ⟨r/2, by linarith, ?_⟩
  intro H hd B x hw
  have hball : (H,r/2) ∈ Metric.ball (H₀,0) r := by
    change max (dist H H₀) (dist (r/2) 0) < r
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    exact max_lt (by linarith) (by linarith)
  exact (ball hball) ⟨((H,r/2),B,x), hw, rfl⟩

/-- Ordinary exact formulation for valid pairs of the standard basis with H₀ or H. -/
theorem pair_neighbourhood (H₀ : Basis) (_hBasis₀ : IsBasis H₀)
    (h₀ : ∀ B, Third H₀ B → ∀ x, ¬ UnbiasedRay H₀ B x) :
    ∃ ε > (0 : ℝ), ∀ H, dist H H₀ < ε → IsBasis H → ∀ B, Third H B →
      ∀ x, ¬ UnbiasedRay H B x := by
  obtain ⟨ε,hε,hh⟩ := robust_pair_neighbourhood H₀ h₀
  refine ⟨ε,hε,?_⟩
  intro H hd _ B hB x hx
  refine hh H hd B x ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i j; rw [hB.1 i j, sub_self, abs_zero]; exact hε.le
  · intro i j; rw [hB.2 i j, sub_self, abs_zero]; exact hε.le
  · intro i; rw [hx.1 i, sub_self, abs_zero]; exact hε.le
  · intro i; rw [hx.2 i, sub_self, abs_zero]; exact hε.le

#print axioms robust_pair_neighbourhood
#print axioms pair_neighbourhood
end
end MUB10Neighbourhood
