import Certificate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace MUB10.Certificate
open PolyCheck
open scoped BigOperators

noncomputable def gauss : Coeff →+ ℂ where
  toFun c := (c.1 : ℂ) + (c.2 : ℂ) * Complex.I
  map_zero' := by simp
  map_add' a b := by simp; ring

private theorem gauss_rot (n : Nat) (h : n < 4) (c : Coeff) :
    gauss (rot n c) = Complex.I ^ n * gauss c := by
  interval_cases n <;> simp [gauss, rot, pow_succ, mul_add, Complex.I_mul_I] <;>
    ring_nf <;> simp [Complex.I_sq]

private theorem eval_lists {n : Nat} (φ : Nat → Coeff →+ ℂ) (f : Fin n → List Term) :
    eval φ (List.ofFn f).flatten = ∑ j, eval φ (f j) := by
  rw [← List.flatMap_id, eval_flatMap, List.map_ofFn, List.sum_ofFn]
  rfl

theorem eval_expand (z : Fin 10 → ℂ) (hz : ∀ j, z j ≠ 0) (w : Multiplier) :
    eval (weighted gauss (mon z)) (expand w) =
      if SafeKey w.key then gauss w.coeff * mon z w.key * rowEq w.row.val z else 0 := by
  by_cases h : SafeKey w.key
  · simp only [expand, if_pos h, eval_lists, eval_ofFn, weighted_apply, rowEq,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    by_cases he : j = k
    · simp [elementary, he]
    · simp only [elementary, if_neg he, gauss_rot _ (Nat.mod_lt _ (by decide)) _,
        mon_step_of_bounded z hz _ _ _ h]
      ring
  · simp [expand,h]

/-- The untrusted coefficient-generation stage is eliminated by this identity,
    proved on the ten-dimensional complex torus for the original 20 equations. -/
theorem direct_identity (z : Fin 10 → ℂ) (hz : ∀ j, z j ≠ 0) :
    (pages.map (fun p => (p.map (fun b => (b.map (fun w =>
      if SafeKey w.key then gauss w.coeff * mon z w.key * rowEq w.row.val z
      else 0)).sum)).sum)).sum = (constantValue : ℂ) := by
  have h := congrArg (eval (weighted gauss (mon z))) exact_certificate
  simp only [polynomial, page, block, eval_compress, eval_flatMap] at h
  simp only [eval_expand z hz] at h
  simpa only [eval_cons, eval_nil, add_zero, weighted_apply, gauss, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Int.cast_natCast, Int.cast_zero, zero_mul, mon_center,
    mul_one] using h

theorem no_torus_solution (z : Fin 10 → ℂ) (hz : ∀ j, z j ≠ 0)
    (hrows : ∀ r : Fin 20, rowEq r.val z = 0) : False := by
  have he := direct_identity z hz
  have hconstant : (constantValue : ℂ) ≠ 0 := by
    exact_mod_cast (show constantValue ≠ 0 by decide)
  apply hconstant
  simpa [hrows] using he.symm

/-- No complex vector has probability 1/10 on all thirty rays of the
    coordinate basis and the two normalized ten-row matrices. -/
theorem best_kharaghani_strongly_unextendible :
    ¬ ∃ v : Fin 10 → ℂ,
      (∀ j, Complex.normSq (v j) = 1 / 10) ∧
      (∀ r : Fin 20, Complex.normSq (rowSum (normalizedRow r.val) v) = 1 / 10) := by
  rintro ⟨v, hv, hu⟩
  obtain ⟨_, hn, he⟩ := sharp_from_normalized v hv hu
  exact no_torus_solution _ hn he

#print axioms best_kharaghani_strongly_unextendible
end MUB10.Certificate
