import Gap
import Mathlib.Tactic.FieldSimp

/-! The explicit three-measurement probability gap for every normalized pure state. -/
namespace MUB10.Certificate
open scoped BigOperators ComplexConjugate

noncomputable section

private def radius : ℝ := (Real.sqrt 10)⁻¹

private lemma radius_pos : 0 < radius := by
  unfold radius
  positivity

private lemma radius_sq : radius^2 = (1/10 : ℝ) := by
  unfold radius
  rw [inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma row_coordinate_norm (r : Nat) (j : Fin 10) :
    ‖normalizedRow r j‖ = radius := by
  simp [normalizedRow, phaseRow, rootTen, radius, Complex.norm_div, Complex.norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

private lemma norm_sum_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ j ∈ s, f j‖ ≤ ∑ j ∈ s, ‖f j‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (norm_add_le _ _).trans (add_le_add_left ih _)

/-- All normalized-row overlaps of a unit state have modulus at most one.
This proof uses 2*c*x ≤ c²+x², where c is the common coordinate radius. -/
private lemma row_overlap_le_one (r : Nat) (v : Fin 10 → ℂ)
    (hv : (∑ j, Complex.normSq (v j)) = 1) :
    ‖rowSum (normalizedRow r) v‖ ≤ 1 := by
  have h (j : Fin 10) : radius * ‖v j‖ ≤ (1/10 + Complex.normSq (v j))/2 := by
    rw [← Complex.sq_norm]
    nlinarith [sq_nonneg (radius-‖v j‖), radius_sq]
  calc
    ‖rowSum (normalizedRow r) v‖ ≤ ∑ j, ‖conj (normalizedRow r j) * v j‖ :=
      norm_sum_bound _ _
    _ = ∑ j, radius * ‖v j‖ := by simp only [Complex.norm_mul, Complex.norm_conj, row_coordinate_norm]
    _ ≤ ∑ j : Fin 10, (1/10 + Complex.normSq (v j))/2 :=
      Finset.sum_le_sum fun j _ => h j
    _ = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, hv]
      norm_num

private def flattenPhase (a : ℂ) : ℂ := ((radius / ‖a‖ : ℝ) : ℂ) * a

private lemma flatten_norm (a : ℂ) (h : 0 < ‖a‖) : ‖flattenPhase a‖ = radius := by
  rw [flattenPhase, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos radius_pos h)]
  field_simp

private lemma flatten_distance (a : ℂ) (h : 0 < ‖a‖) :
    ‖a - flattenPhase a‖ = |‖a‖ - radius| := by
  have he : a - flattenPhase a = (((1 - radius / ‖a‖ : ℝ) : ℂ)) * a := by
    unfold flattenPhase
    push_cast
    ring
  rw [he, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |1 - radius / ‖a‖| * ‖a‖ = |(1 - radius / ‖a‖) * ‖a‖| := by
      rw [abs_mul, abs_of_pos h]
    _ = |‖a‖ - radius| := by
      congr 1
      field_simp

private lemma coordinate_error (a : ℂ) (h : 0 < ‖a‖) :
    radius * ‖a - flattenPhase a‖ ≤ |Complex.normSq a - 1/10| := by
  rw [flatten_distance a h, ← radius_sq, ← Complex.sq_norm,
      sq_sub_sq, abs_mul, abs_of_pos (add_pos h radius_pos)]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_right (show radius ≤ ‖a‖ + radius by linarith) (abs_nonneg (‖a‖-radius))

private lemma squared_overlap_difference (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |Complex.normSq a - Complex.normSq b| ≤ 2 * ‖a-b‖ := by
  rw [← Complex.sq_norm, ← Complex.sq_norm, sq_sub_sq, abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]
  have hh := mul_le_mul (abs_norm_sub_norm_le a b) (show ‖a‖ + ‖b‖ ≤ 2 by linarith)
    (add_nonneg (norm_nonneg a) (norm_nonneg b)) (norm_nonneg (a-b))
  simpa [mul_comm] using hh

/-- Among the thirty probabilities of these three orthonormal measurements, at least
one differs from the unbiased value by at least 1/92,983,800. -/
theorem uniform_probability_gap (v : Fin 10 → ℂ) (hv : (∑ j, Complex.normSq (v j)) = 1) :
    (∃ j : Fin 10, (1/92983800 : ℝ) ≤ |Complex.normSq (v j) - 1/10|) ∨
    (∃ r : Fin 20, (1/92983800 : ℝ) ≤
      |Complex.normSq (rowSum (normalizedRow r.val) v) - 1/10|) := by
  by_contra! h
  obtain ⟨hcoord,hrow⟩ := h
  let u : Fin 10 → ℂ := fun j => flattenPhase (v j)
  have pos (j : Fin 10) : 0 < ‖v j‖ := by
    have aux := hcoord j
    by_contra! hn
    have eq := le_antisymm hn (norm_nonneg (v j))
    rw [← Complex.sq_norm, eq] at aux
    norm_num at aux
    linarith [le_abs_self (1/10 : ℝ)]
  have flat (j : Fin 10) : Complex.normSq (u j) = 1/10 := by
    rw [← Complex.sq_norm, show ‖u j‖ = radius from flatten_norm _ (pos j), radius_sq]
  have hu : (∑ j, Complex.normSq (u j)) = 1 := by simp_rw [flat]; norm_num
  obtain ⟨r,hr⟩ := probability_gap u flat
  let a := normalizedRow r.val
  have hd : ‖rowSum a u - rowSum a v‖ ≤ 10 * (1/92983800 : ℝ) := by
    have he : rowSum a u - rowSum a v = ∑ j, conj (a j) * (u j - v j) := by
      simp only [rowSum, mul_sub, Finset.sum_sub_distrib]
    rw [he]
    calc
      ‖∑ j, conj (a j) * (u j-v j)‖ ≤ ∑ j, ‖conj (a j) * (u j-v j)‖ :=
        norm_sum_bound _ _
      _ ≤ ∑ _j : Fin 10, (1/92983800 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [Complex.norm_mul, Complex.norm_conj, show ‖a j‖ = radius from row_coordinate_norm _ _,
          norm_sub_rev]
        exact (coordinate_error _ (pos j)).trans (hcoord j).le
      _ = _ := by norm_num
  have hs := squared_overlap_difference (rowSum a u) (rowSum a v)
    (row_overlap_le_one _ u hu) (row_overlap_le_one _ v hv)
  have ht := abs_sub_le (Complex.normSq (rowSum a u)) (Complex.normSq (rowSum a v)) (1/10)
  have hm := hrow r
  change (1 / 4427800 : ℝ) ≤ |Complex.normSq (rowSum a u) - 1 / 10| at hr
  change |Complex.normSq (rowSum a v) - 1 / 10| < (1 / 92983800 : ℝ) at hm
  linarith

#print axioms uniform_probability_gap
end
end MUB10.Certificate
