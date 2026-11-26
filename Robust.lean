import Gap
import Mathlib.Tactic.FinCases

/-! Uniform entrywise perturbation in unnormalised phase coordinates.
All distances here are chordal distances in the complex plane. -/
namespace MUB10Robust
open MUB10
open scoped BigOperators ComplexConjugate
noncomputable section

abbrev V := Fin 10 → ℂ
def unitRow (x : V) := ∀ j, ‖x j‖ = 1
def near (x y : V) (δ : ℝ) := ∀ j, ‖x j - y j‖ ≤ δ
def phaseOf (p : Fin 10 → Fin 4) : V := fun j => Complex.I ^ (p j).val
def normalized (x : V) : V := fun j => x j / rootTen

theorem phase_unit (p : Fin 10 → Fin 4) : unitRow (phaseOf p) := by
  intro j; simp [phaseOf, Complex.norm_pow]

private lemma overlap_le (x y : V) (hx : unitRow x) (hy : unitRow y) :
    ‖rowSum x y‖ ≤ 10 := by
  calc
    _ ≤ ∑ j, ‖conj (x j) * y j‖ := norm_sum_le _ _
    _ = _ := by simp only [Complex.norm_mul, Complex.norm_conj, hx _, hy _, one_mul]; norm_num

private lemma overlap_diff (x y a b : V) (ha : unitRow a) (hy : unitRow y)
    {d e : ℝ} (hx : near x a d) (hb : near y b e) :
    ‖rowSum x y - rowSum a b‖ ≤ 10 * (d + e) := by
  have eqn : rowSum x y - rowSum a b =
      ∑ j, (conj (x j - a j) * y j + conj (a j) * (y j - b j)) := by
    unfold rowSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_sub]
    ring
  rw [eqn]
  calc
    _ ≤ ∑ j, ‖conj (x j - a j) * y j + conj (a j) * (y j - b j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 10, (d+e) := by
      apply Finset.sum_le_sum
      intro j _
      apply (norm_add_le _ _).trans
      simpa only [Complex.norm_mul, Complex.norm_conj, hy j, ha j, one_mul, mul_one] using
        add_le_add (hx j) (hb j)
    _ = _ := by simp; ring

theorem normSq_overlap_error (x y a b : V)
    (hx : unitRow x) (hy : unitRow y) (ha : unitRow a) (hb : unitRow b)
    {d e : ℝ} (hxa : near x a d) (hyb : near y b e) :
    |Complex.normSq (rowSum x y) - Complex.normSq (rowSum a b)| ≤ 200 * (d+e) := by
  rw [← Complex.sq_norm, ← Complex.sq_norm, sq_sub_sq, abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hd := (abs_norm_sub_norm_le (rowSum x y) (rowSum a b)).trans
    (overlap_diff x y a b ha hy hxa hyb)
  have hh : ‖rowSum x y‖ + ‖rowSum a b‖ ≤ 20 := by
    linarith [overlap_le x y hx hy, overlap_le a b ha hb]
  have := mul_le_mul hd hh (add_nonneg (norm_nonneg _) (norm_nonneg _))
    ((norm_nonneg _).trans (overlap_diff x y a b ha hy hxa hyb))
  nlinarith only [this]

lemma gaussian_term (s t : Fin 4) :
    conj (Complex.I ^ s.val) * Complex.I ^ t.val =
      ((gaussianPhase (t-s).val).1 : ℂ) + (gaussianPhase (t-s).val).2 * Complex.I := by
  fin_cases s <;> fin_cases t <;> norm_num [gaussianPhase, Fin.sub_def, pow_succ, Complex.I_mul_I]

theorem integral_gram (s t : Fin 10 → Fin 4) :
    ∃ n : ℤ, Complex.normSq (rowSum (phaseOf s) (phaseOf t)) = (n : ℝ) := by
  let A : ℤ := ∑ j, (gaussianPhase (t j - s j).val).1
  let B : ℤ := ∑ j, (gaussianPhase (t j - s j).val).2
  have eqn : rowSum (phaseOf s) (phaseOf t) = (A : ℂ) + B * Complex.I := by
    simp only [rowSum, phaseOf, gaussian_term, Finset.sum_add_distrib]
    simp [A, B, Finset.sum_mul]
  refine ⟨A*A+B*B, ?_⟩
  rw [eqn]
  simp [Complex.normSq_apply]

/-- Two rows can be rounded independently. If their squared raw Gram modulus was an
integer, entrywise error strictly below 1/400 preserves that integer exactly. -/
theorem rounding_preserves_gram (x y : V) (s t : Fin 10 → Fin 4)
    (hx : unitRow x) (hy : unitRow y) {δ : ℝ} (hδ : δ < 1/400)
    (hs : near x (phaseOf s) δ) (ht : near y (phaseOf t) δ)
    (k : ℤ) (hk : Complex.normSq (rowSum x y) = (k : ℝ)) :
    Complex.normSq (rowSum (phaseOf s) (phaseOf t)) = (k : ℝ) := by
  obtain ⟨n, hn⟩ := integral_gram s t
  have err := normSq_overlap_error x y _ _ hx hy (phase_unit s) (phase_unit t) hs ht
  rw [hk, hn] at err
  have hab : |(k : ℝ) - n| < 1 := by linarith
  obtain ⟨lo,hi⟩ := abs_lt.mp hab
  have low : n < k+1 := by exact_mod_cast (show (n : ℝ) < (k : ℝ)+1 by linarith)
  have high : k < n+1 := by exact_mod_cast (show (k : ℝ) < (n : ℝ)+1 by linarith)
  have : k=n := by omega
  simpa [this] using hn

theorem normalized_probability (x y : V) :
    Complex.normSq (rowSum (normalized x) (normalized y)) =
      Complex.normSq (rowSum x y) / 100 := by
  have eqn : rowSum (normalized x) (normalized y) = rowSum x y / rootTen / rootTen := by
    unfold rowSum normalized
    simp only [map_div₀, div_eq_mul_inv, Finset.sum_mul, map_mul, map_inv₀, conj_rootTen]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [eqn, Complex.normSq_div, Complex.normSq_div, rootTen_norm]
  ring

def radius : ℝ := 1/8855600

/-- A flat fourth ray excludes even a nearby pair of rows whenever the rounded
measurement has the certified probability gap. -/
theorem transfer_gap {ι : Type*} (x a : ι → V) (z : V)
    (hx : ∀ i, unitRow (x i)) (ha : ∀ i, unitRow (a i)) (hz : unitRow z)
    {δ : ℝ} (hδ : δ < radius) (hclose : ∀ i, near (x i) (a i) δ)
    (gap : ∃ i, (1/4427800 : ℝ) ≤
      |Complex.normSq (rowSum (normalized (a i)) (normalized z)) - 1/10|) :
    ¬ ∀ i, Complex.normSq (rowSum (x i) z) = 10 := by
  intro hall
  obtain ⟨i, hg⟩ := gap
  have he := normSq_overlap_error (x i) z (a i) z (hx i) hz (ha i) hz (hclose i)
    (show near z z 0 by intro j; simp)
  rw [hall i, add_zero, abs_sub_comm] at he
  rw [normalized_probability] at hg
  have eqn : Complex.normSq (rowSum (a i) z) / 100 - 1 / 10 =
      (Complex.normSq (rowSum (a i) z) - 10) / 100 := by ring
  rw [eqn, abs_div] at hg
  norm_num at hg
  unfold radius at hδ
  linarith

/-- Unconditional robustness of the reference configuration in raw phase coordinates. -/
theorem reference_neighbourhood (x : Fin 20 → V) {δ : ℝ} (hδ : δ < radius)
    (hx : ∀ i, unitRow (x i)) (hc : ∀ i, near (x i) (phaseRow i.val) δ)
    (z : V) (hz : unitRow z) : ¬ ∀ i, Complex.normSq (rowSum (x i) z) = 10 := by
  apply transfer_gap x (fun i => phaseRow i.val) z hx _ hz hδ hc
  · apply MUB10.Certificate.probability_gap
    intro j
    simp [normalized, Complex.normSq_div, ← Complex.sq_norm (z j), hz j]
  · intro i j
    simp [phaseRow, Complex.norm_pow]

#print axioms rounding_preserves_gram
#print axioms reference_neighbourhood
end
end MUB10Robust
