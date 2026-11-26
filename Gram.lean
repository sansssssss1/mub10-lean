import ComplexBridge

/-! The physical Gram matrices of the two displayed bases. Rows `0,…,9` belong to H,
and rows `10,…,19` to K. The inner product is conjugate-linear in the first slot. -/

open scoped BigOperators ComplexConjugate

namespace MUB10

private def gramRe (r s : Nat) : ℤ := ∑ j : Fin 10,
  (gaussianPhase (phase s j + 4 - phase r j)).1

private def gramIm (r s : Nat) : ℤ := ∑ j : Fin 10,
  (gaussianPhase (phase s j + 4 - phase r j)).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem sum_matches_table : ∀ r s : Fin 20,
    (gramRe r.val s.val, gramIm r.val s.val) = integerGram r.val s.val := by decide

private theorem gaussianPhase_value (e : Nat) :
    Complex.I ^ (e % 4) = ((gaussianPhase e).1 : ℂ) + (gaussianPhase e).2 * Complex.I := by
  have h := Nat.mod_lt e (by decide : 0 < 4)
  unfold gaussianPhase
  generalize e % 4 = a at *
  interval_cases a <;> norm_num [pow_succ, Complex.I_mul_I]

private lemma phase_gram (r s : Fin 20) :
    rowSum (phaseRow r.val) (phaseRow s.val) =
      ((integerGram r.val s.val).1 : ℂ) + (integerGram r.val s.val).2 * Complex.I := by
  unfold rowSum phaseRow
  simp_rw [phase_difference _ _ (phase_lt_four _ _) (phase_lt_four _ _), gaussianPhase_value]
  rw [← sum_matches_table r s]
  simp [gramRe, gramIm, Finset.sum_add_distrib, Finset.sum_mul]

private lemma rootTen_square : rootTen * rootTen = 10 := by
  have h := Complex.mul_conj rootTen
  simpa using h

theorem normalized_gram_entry (r s : Fin 20) :
    rowSum (normalizedRow r.val) (normalizedRow s.val) =
      (((integerGram r.val s.val).1 : ℂ) + (integerGram r.val s.val).2 * Complex.I) / 10 := by
  have right_scale : rowSum (phaseRow r.val) (normalizedRow s.val) =
      rowSum (phaseRow r.val) (phaseRow s.val) / rootTen := by
    unfold rowSum normalizedRow
    simp only [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [normalized_row_sum, right_scale, div_div, rootTen_square, phase_gram]

/-- The ten rows in each of H and K have the identity Gram matrix in `ℂ¹⁰`. -/
theorem normalized_same_group (r s : Fin 20) (h : r.val / 10 = s.val / 10) :
    rowSum (normalizedRow r.val) (normalizedRow s.val) = if r = s then 1 else 0 := by
  have hc := integer_gram_check r s
  dsimp only at hc
  rw [normalized_gram_entry]
  split_ifs with he
  · rw [if_pos he] at hc
    rw [hc]; norm_num
  · rw [if_neg he, if_pos h] at hc
    rw [hc]; norm_num

private lemma normSq_gaussian (a b : ℤ) :
    Complex.normSq ((a : ℂ) + b * Complex.I) = ((a * a + b * b : ℤ) : ℝ) := by
  simp [Complex.normSq_apply]

/-- Each of the hundred cross-basis measurement probabilities is 1/10. -/
theorem normalized_cross_group (r s : Fin 20) (h : r.val / 10 ≠ s.val / 10) :
    Complex.normSq (rowSum (normalizedRow r.val) (normalizedRow s.val)) = 1 / 10 := by
  have he : r ≠ s := fun hrs => h (congrArg (fun n : Fin 20 => n.val / 10) hrs)
  have hc := integer_gram_check r s
  dsimp only at hc
  rw [if_neg he, if_neg h] at hc
  rw [normalized_gram_entry, Complex.normSq_div, normSq_gaussian, hc]
  norm_num [Complex.normSq_apply]

/-- All rows in both bases also give uniform probabilities in the standard basis. -/
theorem normalized_standard (r : Fin 20) (j : Fin 10) :
    Complex.normSq (normalizedRow r.val j) = 1 / 10 := by
  simp [normalizedRow, phaseRow]

end MUB10
