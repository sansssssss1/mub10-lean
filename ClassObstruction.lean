import Catalogue
import UniformGap

/-! Transport of the complex probability obstruction through the finite quaternary catalogue. -/
open scoped BigOperators ComplexConjugate
namespace MUB10Catalogue
open MUB10

noncomputable def normalized (r : Row) (j : Fin 10) : ℂ :=
  Complex.I ^ (r.getD j.val 0).val / rootTen

private def sourceRow (s : Fin 20) : Row :=
  (phaseTable.getD s.val []).map fun x => (x : Phase)

private def coord (w : Witness) (j : Fin 10) : Fin 10 := w.perm.getD j.val 0
private def uncoord (w : Witness) (j : Fin 10) : Fin 10 := (w.perm.idxOf j : Fin 10)
private def anchorAt (w : Witness) (j : Fin 10) : Phase :=
  ((baseRows w.swap).getD w.anchor.val []).getD j.val 0
private def shift (w : Witness) (s : Fin 20) : Phase :=
  (phase s.val (coord w 0) : Phase) - anchorAt w (coord w 0)

private def witnessFacts (w : Witness) : Prop :=
  (∀ j, uncoord w (coord w j) = j ∧ coord w (uncoord w j) = j) ∧
  (∀ s, transformed w (sourceRow s) ∈ sourceH w ++ sourceK w) ∧
  (∀ s j, (transformed w (sourceRow s)).getD j.val 0 =
    (phase s.val (coord w j) : Phase) - anchorAt w (coord w j) - shift w s)

private instance (w : Witness) : Decidable (witnessFacts w) := by
  unfold witnessFacts
  infer_instance

set_option maxRecDepth 100000 in
private theorem witness_tables :
    witnesses.all (fun w => decide (witnessFacts w)) = true := by native_decide

private theorem facts (w : Witness) (hw : w ∈ witnesses) : witnessFacts w :=
  of_decide_eq_true (List.all_eq_true.mp witness_tables w hw)

private def permEquiv (w : Witness) (hw : w ∈ witnesses) : Fin 10 ≃ Fin 10 where
  toFun := coord w
  invFun := uncoord w
  left_inv j := ((facts w hw).1 j).1
  right_inv j := ((facts w hw).1 j).2

private noncomputable def unitPhase (a : Phase) : ℂ := Complex.I ^ a.val

private lemma unit_sub (a b : Phase) :
    unitPhase (a-b) = unitPhase a * conj (unitPhase b) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [unitPhase, Fin.sub_def, Fin.neg_def, pow_succ, Complex.I_mul_I, map_mul,
      Complex.conj_I]

private lemma unit_norm (a : Phase) : Complex.normSq (unitPhase a) = 1 := by
  simp [unitPhase, map_pow]

private theorem unit_original (s : Fin 20) (j : Fin 10) :
    unitPhase ((phase s.val j : Nat) : Phase) = phaseRow s.val j := by
  simp [unitPhase, phaseRow, Nat.mod_eq_of_lt (phase_lt_four s.val j)]

private noncomputable def pull (w : Witness) (v : Fin 10 → ℂ) (j : Fin 10) : ℂ :=
  unitPhase (anchorAt w j) * v (uncoord w j)

private theorem pull_prob (w : Witness) (v : Fin 10 → ℂ) (j : Fin 10) :
    Complex.normSq (pull w v j) = Complex.normSq (v (uncoord w j)) := by
  simp [pull, Complex.normSq_mul, unit_norm]

private theorem row_transport (w : Witness) (hw : w ∈ witnesses) (s : Fin 20) (v : Fin 10 → ℂ) :
    Complex.normSq (rowSum (normalized (transformed w (sourceRow s))) v) =
    Complex.normSq (rowSum (normalizedRow s.val) (pull w v)) := by
  have amp : rowSum (normalized (transformed w (sourceRow s))) v =
      unitPhase (shift w s) * rowSum (normalizedRow s.val) (pull w v) := by
    unfold rowSum
    rw [Finset.mul_sum]
    conv_rhs => rw [← Equiv.sum_comp (permEquiv w hw)]
    apply Finset.sum_congr rfl
    intro j _
    change conj (unitPhase ((transformed w (sourceRow s)).getD j.val 0) / rootTen) * v j =
      unitPhase (shift w s) * (conj (phaseRow s.val (coord w j) / rootTen) * pull w v (coord w j))
    rw [(facts w hw).2.2 s j, unit_sub, unit_sub, unit_original, pull,
      ((facts w hw).1 j).1]
    simp only [map_div₀, map_mul, starRingEnd_self_apply]
    ring
  rw [amp, Complex.normSq_mul, unit_norm, one_mul]

private theorem row_mem (i : Fin 10) (B : Basis) (w : Witness) (hw : w ∈ witnesses)
    (hA : (catalogue i).Perm (sourceH w)) (hB : B.Perm (sourceK w)) (s : Fin 20) :
    transformed w (sourceRow s) ∈ catalogue i ++ B :=
  ((hA.append hB).mem_iff).mpr ((facts w hw).2.1 s)

/-- A coordinate-flat state differs measurably from uniform on some row of either matrix. -/
theorem catalogue_probability_gap (i : Fin 10) (B : Basis)
    (hlen : B.length = 10) (hd : B.Nodup)
    (hshape : ∀ r ∈ B, ∃ tail : Row, r = 0 :: tail ∧ tail.length = 9)
    (hcross : ∀ r ∈ B, ∀ a ∈ catalogue i, gramSq a r = 10)
    (horth : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → gramSq a b = 0)
    (v : Fin 10 → ℂ) (flat : ∀ j, Complex.normSq (v j) = 1/10) :
    ∃ r ∈ catalogue i ++ B, (1/4427800 : ℝ) ≤
      |Complex.normSq (rowSum (normalized r) v) - 1/10| := by
  obtain ⟨w,hw,_,hA,hB⟩ := catalogue_pair i B hlen hd hshape hcross horth
  obtain ⟨s,hs⟩ := MUB10.Certificate.probability_gap (pull w v)
    (fun j => (pull_prob w v j).trans (flat _))
  exact ⟨_, row_mem i B w hw hA hB s, by rwa [row_transport w hw]⟩

/-- Uniform bound for arbitrary normalized pure states, across all thirty probabilities. -/
theorem catalogue_uniform_gap (i : Fin 10) (B : Basis)
    (hlen : B.length = 10) (hd : B.Nodup)
    (hshape : ∀ r ∈ B, ∃ tail : Row, r = 0 :: tail ∧ tail.length = 9)
    (hcross : ∀ r ∈ B, ∀ a ∈ catalogue i, gramSq a r = 10)
    (horth : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → gramSq a b = 0)
    (v : Fin 10 → ℂ) (hv : (∑ j, Complex.normSq (v j)) = 1) :
    (∃ j, (1/92983800 : ℝ) ≤ |Complex.normSq (v j) - 1/10|) ∨
    ∃ r ∈ catalogue i ++ B, (1/92983800 : ℝ) ≤
      |Complex.normSq (rowSum (normalized r) v) - 1/10| := by
  obtain ⟨w,hw,_,hA,hB⟩ := catalogue_pair i B hlen hd hshape hcross horth
  have hu : (∑ j, Complex.normSq (pull w v j)) = 1 := by
    simp_rw [pull_prob]
    exact ((permEquiv w hw).symm.sum_comp (fun j => Complex.normSq (v j))).trans hv
  rcases MUB10.Certificate.uniform_probability_gap (pull w v) hu with ⟨j,hj⟩|⟨s,hs⟩
  · exact Or.inl ⟨_, by rwa [pull_prob] at hj⟩
  · exact Or.inr ⟨_, row_mem i B w hw hA hB s, by rwa [row_transport w hw]⟩

theorem catalogue_no_unbiased (i : Fin 10) (B : Basis)
    (hlen : B.length = 10) (hd : B.Nodup)
    (hshape : ∀ r ∈ B, ∃ tail : Row, r = 0 :: tail ∧ tail.length = 9)
    (hcross : ∀ r ∈ B, ∀ a ∈ catalogue i, gramSq a r = 10)
    (horth : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → gramSq a b = 0)
    (v : Fin 10 → ℂ) (flat : ∀ j, Complex.normSq (v j) = 1/10) :
    ¬ ∀ r ∈ catalogue i ++ B, Complex.normSq (rowSum (normalized r) v) = 1/10 := by
  intro hall
  obtain ⟨r,hr,hgap⟩ := catalogue_probability_gap i B hlen hd hshape hcross horth v flat
  rw [hall r hr] at hgap
  norm_num at hgap

#print axioms catalogue_uniform_gap
#print axioms catalogue_probability_gap
#print axioms catalogue_no_unbiased
end MUB10Catalogue
