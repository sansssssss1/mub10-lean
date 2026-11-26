import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complex overlaps for the order-ten Best–Kharaghani triple

`phaseTable` encodes the rows of Table 1, page 3 of arXiv:1209.4315.
Rows 0–9 are H and rows 10–19 are K. Entries 0, 1, 2, 3 mean 1, i, −1, −i.
The same `PhaseExp` defines both the physical measurement and its Laurent equations.
-/

open scoped BigOperators ComplexConjugate

namespace MUB10

def phaseTable : List (List Nat) := [
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 2, 2, 2, 1, 3, 0, 2, 0],
  [0, 2, 0, 2, 2, 3, 2, 1, 0, 0],
  [0, 2, 2, 0, 2, 3, 0, 0, 1, 2],
  [0, 2, 2, 2, 0, 1, 0, 2, 0, 3],
  [0, 3, 1, 1, 3, 2, 1, 3, 3, 1],
  [0, 1, 2, 0, 0, 3, 2, 2, 2, 0],
  [0, 0, 3, 0, 2, 1, 2, 2, 0, 2],
  [0, 2, 0, 3, 0, 1, 2, 0, 2, 2],
  [0, 0, 0, 2, 1, 3, 0, 2, 2, 2],
  [3, 2, 2, 0, 0, 0, 0, 3, 1, 0],
  [3, 0, 0, 0, 1, 2, 3, 0, 1, 3],
  [0, 3, 1, 3, 0, 2, 0, 1, 0, 1],
  [0, 1, 3, 0, 3, 3, 2, 0, 0, 1],
  [1, 0, 2, 1, 3, 1, 0, 0, 0, 3],
  [1, 0, 1, 3, 0, 0, 2, 0, 2, 0],
  [0, 1, 0, 0, 0, 1, 1, 2, 3, 3],
  [2, 3, 0, 0, 2, 0, 1, 1, 0, 0],
  [0, 0, 3, 2, 1, 0, 3, 2, 0, 0],
  [2, 0, 0, 1, 0, 3, 0, 3, 3, 1]]

def PhaseExp (r : Nat) (j : Fin 10) : Nat := ((phaseTable.getD r []).getD j.val 0) % 4
abbrev phase := PhaseExp

theorem phase_lt_four (r : Nat) (j : Fin 10) : phase r j < 4 := Nat.mod_lt _ (by decide)

def gaussianPhase (e : Nat) : Int × Int :=
  match e % 4 with
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | _ => (0, -1)

/-- Gaussian-integer coordinates of the unnormalized Gram entry of rows `r` and `s`. -/
def integerGram (r s : Nat) : Int × Int :=
  (List.finRange 10).foldl (fun u j =>
    let t := gaussianPhase (phase s j + 4 - phase r j)
    (u.1 + t.1, u.2 + t.2)) (0, 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- A direct kernel computation over the 400 Gram entries, including all cross-group norms. -/
theorem integer_gram_check : ∀ r s : Fin 20,
    let g := integerGram r.val s.val
    if r = s then g = (10, 0)
    else if r.val / 10 = s.val / 10 then g = (0, 0)
    else g.1 * g.1 + g.2 * g.2 = 10 := by decide

noncomputable section

def phaseRow (r : Nat) (j : Fin 10) : ℂ := Complex.I ^ phase r j

def rowSum (r z : Fin 10 → ℂ) : ℂ := ∑ j, conj (r j) * z j

def rowEq (r : Nat) (z : Fin 10 → ℂ) : ℂ :=
  ∑ j, ∑ k, if j = k then 0 else Complex.I ^ ((phase r k + 4 - phase r j) % 4) * z j / z k

lemma phase_difference (a b : Nat) (ha : a < 4) (hb : b < 4) :
    conj (Complex.I ^ a) * Complex.I ^ b = Complex.I ^ ((b + 4 - a) % 4) := by
  interval_cases a <;> interval_cases b <;>
    norm_num [pow_succ, Complex.I_mul_I, Complex.conj_I, map_mul]

lemma conj_eq_inverse {w : ℂ} (h : Complex.normSq w = 1) : conj w = w⁻¹ := by
  simp [Complex.inv_def, h]

lemma unit_ne_zero {w : ℂ} (h : Complex.normSq w = 1) : w ≠ 0 := by
  rintro rfl
  simp at h

private def term (r z : Fin 10 → ℂ) (j k : Fin 10) : ℂ :=
  conj (r j) * r k * z j * conj (z k)

private lemma square_expansion (r z : Fin 10 → ℂ) :
    rowSum r z * conj (rowSum r z) = ∑ j, ∑ k, term r z j k := by
  unfold rowSum
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [term, mul_assoc, mul_comm, mul_left_comm]

private lemma term_diagonal (r : Nat) (z : Fin 10 → ℂ)
    (hz : ∀ j, Complex.normSq (z j) = 1) (j : Fin 10) : term (phaseRow r) z j j = 1 := by
  unfold term
  rw [← Complex.normSq_eq_conj_mul_self]
  simp [phaseRow, Complex.mul_conj, hz]

private lemma sum_decomposition (r : Nat) (z : Fin 10 → ℂ)
    (hz : ∀ j, Complex.normSq (z j) = 1) :
    (∑ j, ∑ k, term (phaseRow r) z j k) = rowEq r z + 10 := by
  calc
    (∑ j, ∑ k, term (phaseRow r) z j k) =
        ∑ j : Fin 10, ∑ k : Fin 10,
          ((if j = k then 0 else Complex.I ^ ((phase r k + 4 - phase r j) % 4) * z j / z k) +
            (if k = j then (1 : ℂ) else 0)) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      by_cases h : j = k
      · subst k; simp [term_diagonal r z hz]
      · simp only [h, Ne.symm h, if_false, add_zero]
        unfold term phaseRow
        rw [phase_difference _ _ (phase_lt_four r j) (phase_lt_four r k),
          conj_eq_inverse (hz k), div_eq_mul_inv]
    _ = rowEq r z + 10 := by
      have hone (j : Fin 10) : (∑ k : Fin 10, if k = j then (1 : ℂ) else 0) = 1 :=
        (Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℂ))).trans (if_pos (Finset.mem_univ j))
      simp only [Finset.sum_add_distrib, hone, rowEq]
      simp

theorem rowEq_zero_of_unbiased (r : Nat) (z : Fin 10 → ℂ)
    (hz : ∀ j, Complex.normSq (z j) = 1) (hu : Complex.normSq (rowSum (phaseRow r) z) = 10) :
    rowEq r z = 0 := by
  have h := square_expansion (phaseRow r) z
  rw [Complex.mul_conj, hu, sum_decomposition r z hz] at h
  apply add_right_cancel (b := (10 : ℂ))
  simpa using h.symm

def rootTen : ℂ := (Real.sqrt 10 : ℝ)

@[simp] lemma rootTen_norm : Complex.normSq rootTen = 10 := by
  unfold rootTen
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]

@[simp] lemma conj_rootTen : conj rootTen = rootTen := Complex.conj_ofReal _

def phaseCoordinates (v : Fin 10 → ℂ) : Fin 10 → ℂ := fun j => rootTen * v j

def normalizedRow (r : Nat) : Fin 10 → ℂ := fun j => phaseRow r j / rootTen

lemma normalized_row_sum (r : Nat) (v : Fin 10 → ℂ) :
    rowSum (normalizedRow r) v = rowSum (phaseRow r) v / rootTen := by
  unfold rowSum normalizedRow
  simp only [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_assoc, mul_left_comm, mul_comm]

lemma phase_row_sum (r v : Fin 10 → ℂ) : rowSum r (phaseCoordinates v) = rootTen * rowSum r v := by
  unfold rowSum phaseCoordinates
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma flat_coordinates (v : Fin 10 → ℂ) (hv : ∀ j, Complex.normSq (v j) = 1 / 10) :
    ∀ j, Complex.normSq (phaseCoordinates v j) = 1 := by
  intro j
  unfold phaseCoordinates
  rw [Complex.normSq_mul, rootTen_norm, hv j]
  norm_num

lemma flat_overlap (r : Nat) (v : Fin 10 → ℂ)
    (hu : Complex.normSq (rowSum (normalizedRow r) v) = 1 / 10) :
    Complex.normSq (rowSum (phaseRow r) (phaseCoordinates v)) = 10 := by
  rw [normalized_row_sum, Complex.normSq_div, rootTen_norm] at hu
  have hs : Complex.normSq (rowSum (phaseRow r) v) = 1 :=
    (div_left_inj' (show (10 : ℝ) ≠ 0 by norm_num)).mp hu
  rw [phase_row_sum, Complex.normSq_mul, rootTen_norm, hs, mul_one]

/-- The complex polynomial residual is a real scalar, exactly 100 times the probability error. -/
theorem rowEq_prob (r : Nat) (v : Fin 10 → ℂ) (hv : ∀ j, Complex.normSq (v j) = 1 / 10) :
    rowEq r (phaseCoordinates v) =
      ((100 * (Complex.normSq (rowSum (normalizedRow r) v) - 1 / 10) : ℝ) : ℂ) := by
  have h := square_expansion (phaseRow r) (phaseCoordinates v)
  rw [Complex.mul_conj, sum_decomposition r _ (flat_coordinates v hv), phase_row_sum,
    Complex.normSq_mul, rootTen_norm] at h
  rw [normalized_row_sum, Complex.normSq_div, rootTen_norm]
  calc
    rowEq r (phaseCoordinates v) = ((10 * Complex.normSq (rowSum (phaseRow r) v) : ℝ) : ℂ) - 10 :=
      eq_sub_of_add_eq h.symm
    _ = _ := by push_cast; ring

/-- The hypotheses use squared overlaps with the standard basis and the twenty normalized
rows. The conclusion uses exactly the unsigned row indices and exponents in the certificate. -/
theorem sharp_from_normalized (v : Fin 10 → ℂ) (hv : ∀ j, Complex.normSq (v j) = 1 / 10)
    (hu : ∀ r : Fin 20, Complex.normSq (rowSum (normalizedRow r.val) v) = 1 / 10) :
    (∀ j, Complex.normSq (phaseCoordinates v j) = 1) ∧
    (∀ j, phaseCoordinates v j ≠ 0) ∧ (∀ r : Fin 20, rowEq r.val (phaseCoordinates v) = 0) := by
  have hz := flat_coordinates v hv
  exact ⟨hz, fun j => unit_ne_zero (hz j),
    fun r => rowEq_zero_of_unbiased r.val _ hz (flat_overlap r.val v (hu r))⟩

end
end MUB10
