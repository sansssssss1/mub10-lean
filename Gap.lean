import StrongTriple
import Mathlib.Data.Complex.Norm
import Mathlib.Tactic.Linarith

/-! A uniform quantitative obstruction for every state flat in the coordinate basis. -/
namespace MUB10.Certificate
open PolyCheck
open scoped BigOperators

private def height (w : Multiplier) : Nat := w.coeff.1.natAbs + w.coeff.2.natAbs
private def blockHeight (b : List Multiplier) : Nat := (b.map height).sum
private def pageHeight (p : List (List Multiplier)) : Nat := (p.map blockHeight).sum
def certificateHeight : Nat := (pages.map pageHeight).sum

set_option maxRecDepth 100000 in
theorem certificate_height_lt : certificateHeight < 44278 * constantValue := by
  native_decide

private theorem sum_majorant {α : Type*} (xs : List α) (u : α → ℂ)
    (w : α → Nat) (δ : ℝ) (h : ∀ t, ‖u t‖ ≤ (w t : ℝ) * δ) :
    ‖(xs.map u).sum‖ ≤ ((xs.map w).sum : Nat) * δ := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h a) ih)

private theorem norm_gauss_height (w : Multiplier) :
    ‖gauss w.coeff‖ ≤ (height w : ℝ) := by
  change ‖(w.coeff.1 : ℂ) + (w.coeff.2 : ℂ) * Complex.I‖ ≤ _
  have habs (a : Int) : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [Int.cast_natAbs, Int.cast_abs]
  simpa only [height, Nat.cast_add, habs, Complex.norm_mul, Complex.norm_I,
    mul_one, Complex.norm_intCast] using
    norm_add_le (w.coeff.1 : ℂ) ((w.coeff.2 : ℂ) * Complex.I)

private theorem norm_mon_of_flat (z : Fin 10 → ℂ) (unit : ∀ j, Complex.normSq (z j) = 1)
    (k : Nat) : ‖mon z k‖ = 1 := by
  have hu (q : Fin 10) : ‖z q‖ = 1 := by
    have hh := (Complex.sq_norm (z q)).trans (unit q)
    nlinarith [norm_nonneg (z q)]
  simp [mon, Complex.norm_prod, Complex.norm_zpow, hu]

private noncomputable def summand (z : Fin 10 → ℂ) (w : Multiplier) : ℂ :=
  if SafeKey w.key then gauss w.coeff * mon z w.key * rowEq w.row.val z else 0

/-- One of the twenty unnormalized squared-overlap residuals has at least this modulus. -/
theorem row_gap (z : Fin 10 → ℂ) (unit : ∀ j, Complex.normSq (z j) = 1) :
    ∃ r : Fin 20, (1/44278 : ℝ) ≤ ‖rowEq r.val z‖ := by
  by_contra! h
  have hterm (w : Multiplier) : ‖summand z w‖ ≤ (height w : ℝ) * (1/44278) := by
    by_cases hk : SafeKey w.key
    · rw [summand, if_pos hk, Complex.norm_mul, Complex.norm_mul, norm_mon_of_flat z unit, mul_one]
      exact mul_le_mul (norm_gauss_height w) (h w.row).le (norm_nonneg _) (Nat.cast_nonneg _)
    · rw [summand, if_neg hk, norm_zero]
      positivity
  let bval := fun b : List Multiplier => (b.map (summand z)).sum
  let pval := fun p : List (List Multiplier) => (p.map bval).sum
  have hb (b : List Multiplier) : ‖bval b‖ ≤ (blockHeight b : ℝ) * (1/44278) :=
    sum_majorant b _ _ _ hterm
  have hp (p : List (List Multiplier)) : ‖pval p‖ ≤ (pageHeight p : ℝ) * (1/44278) :=
    sum_majorant p _ _ _ hb
  have hall := sum_majorant pages pval pageHeight (1/44278) hp
  change ‖(pages.map pval).sum‖ ≤ (certificateHeight : ℝ) * (1/44278) at hall
  have hid : (pages.map pval).sum = (constantValue : ℂ) :=
    direct_identity z (fun j => unit_ne_zero (unit j))
  rw [hid, Complex.norm_natCast] at hall
  have hw : (certificateHeight : ℝ) < 44278 * (constantValue : ℝ) := by
    exact_mod_cast certificate_height_lt
  linarith

/-- For every coordinate-flat state, some normalized row measurement has a nonzero
probability error of at least one part in 4,427,800. -/
theorem probability_gap (v : Fin 10 → ℂ) (flat : ∀ j, Complex.normSq (v j) = 1/10) :
    ∃ r : Fin 20, (1/4427800 : ℝ) ≤
      |Complex.normSq (rowSum (normalizedRow r.val) v) - 1/10| := by
  obtain ⟨r, hr⟩ := row_gap (phaseCoordinates v) (flat_coordinates v flat)
  refine ⟨r, ?_⟩
  rw [rowEq_prob r.val v flat, Complex.norm_real, Real.norm_eq_abs, abs_mul] at hr
  norm_num at hr
  linarith

#print axioms probability_gap
end MUB10.Certificate
