import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Evaluation of the base-eight Laurent-exponent keys in the certificate. -/
namespace MUB10
open scoped BigOperators

def digit (key : Nat) (q : Fin 10) : Int :=
  (((key / 8 ^ q.val) % 8 : Nat) : Int) - 3

def stepKey (m : Nat) (j k : Fin 10) : Nat :=
  m + 8 ^ j.val - 8 ^ k.val

def center : Nat := 3 * ∑ q : Fin 10, 8 ^ q.val

noncomputable def mon (z : Fin 10 → ℂ) (key : Nat) : ℂ :=
  ∏ q, z q ^ digit key q

theorem digit_center : ∀ q : Fin 10, digit center q = 0 := by decide

@[simp] theorem mon_center (z : Fin 10 → ℂ) : mon z center = 1 := by
  simp [mon, digit_center]

private theorem prod_indicator (z : Fin 10 → ℂ) (j : Fin 10) :
    (∏ q : Fin 10, z q ^ (if q = j then (1 : ℤ) else 0)) = z j := by
  classical
  calc
    _ = ∏ q : Fin 10, (if q = j then z j else 1) := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases h : q = j <;> simp [h]
    _ = z j := by simp

theorem mon_step (z : Fin 10 → ℂ) (hz : ∀ q, z q ≠ 0)
    (m : Nat) (j k : Fin 10)
    (h : ∀ q, digit (stepKey m j k) q =
      digit m q + (if q = j then 1 else 0) - (if q = k then 1 else 0)) :
    mon z (stepKey m j k) = mon z m * z j / z k := by
  classical
  unfold mon
  calc
    _ = ∏ q : Fin 10,
        (z q ^ digit m q * z q ^ (if q = j then (1 : ℤ) else 0)) /
          z q ^ (if q = k then (1 : ℤ) else 0) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [h q, zpow_sub₀ (hz q), zpow_add₀ (hz q)]
    _ = _ := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, prod_indicator, prod_indicator]

/-! A multiplier has all exponents in [-2,2]. Its base-eight digits
have room for adding one and subtracting one, with no carries or borrows. -/
private def column (m j : Nat) : Nat := (m / 8^j) % 8

private theorem column_succ (m j : Nat) : column m (j+1) = column (m/8) j := by
  simp [column, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

private theorem column_add (j : Nat) : ∀ m q : Nat, column m j < 7 →
    column (m + 8^j) q = column m q + (if q = j then 1 else 0) := by
  induction j with
  | zero =>
    intro m q hm
    have h : m % 8 < 7 := by simpa [column] using hm
    cases q with
    | zero => simp [column]; omega
    | succ q =>
      have divEq : (m + 1) / 8 = m / 8 := by omega
      simp [column_succ, divEq]
  | succ j ih =>
    intro m q hm
    have h : column (m/8) j < 7 := by simpa only [column_succ] using hm
    cases q with
    | zero =>
      simp [column, Nat.pow_succ, Nat.add_mul_mod_self_right]
    | succ q =>
      have step : (m + 8 ^ (j+1)) / 8 = m / 8 + 8 ^ j := by
        rw [Nat.pow_succ]
        omega
      simpa only [column_succ, step, Nat.succ.injEq] using ih (m/8) q h

private theorem column_sub (j : Nat) : ∀ m q : Nat, 0 < column m j →
    column (m - 8^j) q = column m q - (if q = j then 1 else 0) := by
  induction j with
  | zero =>
    intro m q hm
    have h : 0 < m % 8 := by simpa [column] using hm
    cases q with
    | zero => simp [column]; omega
    | succ q =>
      have divEq : (m - 1) / 8 = m / 8 := by omega
      simp [column_succ, divEq]
  | succ j ih =>
    intro m q hm
    have h : 0 < column (m/8) j := by simpa only [column_succ] using hm
    have ha : 8^j ≤ m/8 := by
      apply Nat.le_of_not_gt
      intro hlt
      simp [column, Nat.div_eq_of_lt hlt] at h
    cases q with
    | zero =>
      simp [column, Nat.pow_succ]
      omega
    | succ q =>
      have step : (m - 8 ^ (j+1)) / 8 = m / 8 - 8 ^ j := by
        rw [Nat.pow_succ]
        omega
      simpa only [column_succ, step, Nat.succ.injEq] using ih (m/8) q h

theorem digit_step (m : Nat) (j k : Fin 10)
    (bounds : ∀ q, -2 ≤ digit m q ∧ digit m q ≤ 2) (q : Fin 10) :
    digit (stepKey m j k) q = digit m q +
      (if q = j then 1 else 0) - (if q = k then 1 else 0) := by
  have limits (t : Fin 10) : 1 ≤ column m t.val ∧ column m t.val < 7 := by
    have h := bounds t
    change -2 ≤ (column m t.val : Int) - 3 ∧ (column m t.val : Int) - 3 ≤ 2 at h
    omega
  have canAdd := (limits j).2
  have canSub : 0 < column (m + 8^j.val) k.val := by
    rw [column_add j.val m k.val canAdd]
    have := (limits k).1
    omega
  change ((column (m + 8^j.val - 8^k.val) q.val : Nat) : Int) - 3 =
    (column m q.val : Int) - 3 + _ - _
  rw [column_sub k.val _ q.val canSub, column_add j.val m q.val canAdd]
  have := (limits q).1
  simp only [Fin.val_inj]
  by_cases hj : q = j
  · by_cases hk : q = k
    · simp only [if_pos hj, if_pos hk]; omega
    · simp only [if_pos hj, if_neg hk]; omega
  · by_cases hk : q = k
    · simp only [if_neg hj, if_pos hk]; omega
    · simp only [if_neg hj, if_neg hk]; omega

theorem mon_step_of_bounded (z : Fin 10 → ℂ) (hz : ∀ q, z q ≠ 0)
    (m : Nat) (j k : Fin 10) (bounds : ∀ q, -2 ≤ digit m q ∧ digit m q ≤ 2) :
    mon z (stepKey m j k) = mon z m * z j / z k :=
  mon_step z hz m j k (digit_step m j k bounds)

end MUB10
