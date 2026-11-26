import Gram
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp

/-! The three transition matrices for the physical triple have no nontrivial fifth root of
unity among their cross ratios. No finite-phase condition is imposed on a hypothetical
measurement or on the choice of representatives of the three bases. -/

namespace MUB10
open scoped ComplexConjugate

noncomputable section

private def RationalParts (z : ℂ) : Prop := (∃ a : ℚ, z.re = a) ∧ (∃ b : ℚ, z.im = b)

private lemma rational_mul {z w : ℂ} (hz : RationalParts z) (hw : RationalParts w) :
    RationalParts (z * w) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := hw
  exact ⟨⟨a*c-b*d, by simp [Complex.mul_re, ha, hb, hc, hd]⟩,
    ⟨a*d+b*c, by simp [Complex.mul_im, ha, hb, hc, hd]⟩⟩

private lemma rational_inv {z : ℂ} (hz : RationalParts z) : RationalParts z⁻¹ := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  exact ⟨⟨a / (a*a+b*b), by simp [Complex.inv_re, Complex.normSq_apply, ha, hb]⟩,
    ⟨-b / (a*a+b*b), by simp [Complex.inv_im, Complex.normSq_apply, ha, hb]⟩⟩

private lemma rational_I_pow (n : Nat) : RationalParts (Complex.I ^ n) := by
  induction n with
  | zero => exact ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩
  | succ n ih =>
    rw [pow_succ]
    exact rational_mul ih ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩

private lemma rational_gaussian (a b : ℤ) : RationalParts ((a : ℂ) + b * Complex.I) :=
  ⟨⟨(a : ℚ), by simp⟩, ⟨(b : ℚ), by simp⟩⟩

/-- A fifth root of unity with rational real part must be 1. -/
theorem fifth_root_with_rational_real_part {z : ℂ} (hr : ∃ a : ℚ, z.re = a)
    (hz : z ^ 5 = 1) : z = 1 := by
  by_contra hn
  have hn0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hn1 : Complex.normSq z = 1 := by
    have h := congrArg Complex.normSq hz
    simp only [map_pow, map_one] at h
    exact (pow_left_inj₀ (Complex.normSq_nonneg _) zero_le_one (by decide : 5 ≠ 0)).mp
      (by simpa using h)
  have hp : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := by
    have hprod : (z-1) * (z^4 + z^3 + z^2 + z + 1) = 0 :=
      calc _ = z^5-1 := by ring
           _ = 0 := by rw [hz]; ring
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hn)
  have hs : (2 * (z + conj z) + 1) ^ 2 = 5 := by
    apply sub_eq_zero.mp
    calc _ = 4 * (z^4 + z^3 + z^2 + z + 1) / z^2 := by
           rw [conj_eq_inverse hn1]; field_simp [hn0]; ring
         _ = 0 := by simp [hp]
  obtain ⟨a, ha⟩ := hr
  rw [Complex.add_conj, ha] at hs
  have hq : (2 * (2*a) + 1) ^ 2 = (5 : ℚ) := by exact_mod_cast hs
  have hsq : IsSquare (5 : ℚ) := ⟨_, by rw [← sq]; exact hq.symm⟩
  obtain ⟨n, hn⟩ := (Rat.isSquare_natCast_iff (n := 5)).mp hsq
  by_cases h3 : 3 ≤ n
  · have h9 : 9 ≤ n*n := Nat.mul_le_mul h3 h3
    omega
  · have hsmall : n < 3 := by omega
    interval_cases n <;> norm_num at hn

private def hIndex (i : Fin 10) : Fin 20 := ⟨i.val, by omega⟩
private def kIndex (j : Fin 10) : Fin 20 := ⟨10+j.val, by omega⟩

/-- The entries are `⟨eᵢ,Hⱼ⟩`, `⟨eᵢ,Kⱼ⟩`, and `⟨Hᵢ,Kⱼ⟩`, respectively. -/
def transitionEntry (p : Fin 3) (i j : Fin 10) : ℂ :=
  if p.val = 0 then normalizedRow (hIndex j).val i
  else if p.val = 1 then normalizedRow (kIndex j).val i
  else rowSum (normalizedRow (hIndex i).val) (normalizedRow (kIndex j).val)

private def rawEntry (p : Fin 3) (i j : Fin 10) : ℂ :=
  if p.val = 0 then phaseRow (hIndex j).val i
  else if p.val = 1 then phaseRow (kIndex j).val i
  else let q := integerGram (hIndex i).val (kIndex j).val
       (q.1 : ℂ) + q.2 * Complex.I

private def transitionScale (p : Fin 3) : ℂ :=
  if p.val = 0 then rootTen else if p.val = 1 then rootTen else 10

private lemma raw_rational (p : Fin 3) (i j : Fin 10) : RationalParts (rawEntry p i j) := by
  unfold rawEntry
  split_ifs <;> first | exact rational_I_pow _ | exact rational_gaussian _ _

private lemma scale_ne_zero (p : Fin 3) : transitionScale p ≠ 0 := by
  have h : rootTen ≠ 0 := by
    intro h
    have h' := rootTen_norm
    rw [h] at h'
    norm_num at h'
  unfold transitionScale
  split_ifs <;> first | exact h | norm_num

private lemma entry_as_scaled (p : Fin 3) (i j : Fin 10) :
    transitionEntry p i j = rawEntry p i j / transitionScale p := by
  unfold transitionEntry rawEntry transitionScale
  split_ifs <;> first | rfl | exact normalized_gram_entry _ _

/-- This is the row- and column-phase-invariant cross ratio `Tᵢⱼ Tₖₗ / (Tᵢₗ Tₖⱼ)`. -/
def crossRatio (p : Fin 3) (i k j l : Fin 10) : ℂ :=
  transitionEntry p i j * transitionEntry p k l / (transitionEntry p i l * transitionEntry p k j)

private lemma rational_crossRatio (p : Fin 3) (i k j l : Fin 10) :
    RationalParts (crossRatio p i k j l) := by
  unfold crossRatio
  simp only [entry_as_scaled, div_mul_div_comm]
  rw [div_div_div_cancel_right₀ (mul_ne_zero (scale_ne_zero p) (scale_ne_zero p)), div_eq_mul_inv]
  exact rational_mul (rational_mul (raw_rational _ _ _) (raw_rational _ _ _))
    (rational_inv (rational_mul (raw_rational _ _ _) (raw_rational _ _ _)))

theorem no_nontrivial_fifth_cross_ratio (p : Fin 3) (i k j l : Fin 10)
    (h : (crossRatio p i k j l) ^ 5 = 1) : crossRatio p i k j l = 1 :=
  fifth_root_with_rational_real_part (rational_crossRatio p i k j l).1 h

/-- Even after arbitrary nonzero row and column scalings, no 2×2 block can be
`[[1,1],[1,w]]` for a nontrivial fifth root `w`. Arbitrary row and column permutations
are covered by the four free indices. -/
theorem no_rephased_fifth_minor (p : Fin 3) (i k j l : Fin 10)
    (u v : Fin 10 → ℂ) (hu : ∀ t, u t ≠ 0) (hv : ∀ t, v t ≠ 0)
    (w : ℂ) (hw : w^5 = 1) (hw' : w ≠ 1)
    (ha : u i * transitionEntry p i j * v j = 1)
    (hb : u i * transitionEntry p i l * v l = 1)
    (hc : u k * transitionEntry p k j * v j = 1)
    (hd : u k * transitionEntry p k l * v l = w) : False := by
  let t := u i * u k * v j * v l
  have ht : t ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hu i) (hu k)) (hv j)) (hv l)
  have hratio : crossRatio p i k j l = w := by
    calc crossRatio p i k j l =
        (t * (transitionEntry p i j * transitionEntry p k l)) /
        (t * (transitionEntry p i l * transitionEntry p k j)) := (mul_div_mul_left _ _ ht).symm
      _ = ((u i * transitionEntry p i j * v j) * (u k * transitionEntry p k l * v l)) /
          ((u i * transitionEntry p i l * v l) * (u k * transitionEntry p k j * v j)) := by
            unfold t; congr 1 <;> ring
      _ = w := by rw [ha, hb, hc, hd]; simp
  exact hw' (hratio ▸ no_nontrivial_fifth_cross_ratio p i k j l (hratio.symm ▸ hw))

end
end MUB10
