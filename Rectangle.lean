import MainResult

/-! A phase-independent quantitative obstruction to a fourth unbiased ray.
The entries are the unit-modulus phases of the normalized transition amplitudes. -/
open scoped BigOperators ComplexConjugate
namespace MUB10Radius
open MUB10 MUB10Robust
noncomputable section

/-- Common column phases and an arbitrary scalar phase on each row cancel in this product. -/
def rectangle (X : Ix → V) (r₀ : Ix) (j₀ : Fin 10) (r : Ix) (j : Fin 10) : ℂ :=
  X r j * conj (X r j₀) * conj (X r₀ j) * X r₀ j₀

private def twist (c : V) (a : ℂ) (x : V) : V := fun j => a * c j * x j

private lemma twist_unit (c x : V) (a : ℂ) (hc : unitRow c) (hx : unitRow x) (ha : ‖a‖ = 1) :
    unitRow (twist c a x) := by
  intro j
  simp [twist, Complex.norm_mul, hc j, hx j, ha]

private lemma twist_gram (c x y : V) (a b : ℂ)
    (hc : unitRow c) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    Complex.normSq (rowSum (twist c a x) (twist c b y)) = Complex.normSq (rowSum x y) := by
  have eq : rowSum (twist c a x) (twist c b y) = conj a * b * rowSum x y := by
    unfold rowSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [twist, map_mul]
    calc
      _ = (conj (c j) * c j) * (conj a * b * (conj (x j) * y j)) := by ring
      _ = _ := by rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hc j]; simp
  rw [eq, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj,
    ← Complex.sq_norm a, ← Complex.sq_norm b, ha, hb]
  simp

/-- Whenever a fourth unbiased ray exists, every reference row and reference
coordinate exhibit a rectangle at chordal distance at least 1/8,855,600 from every fourth root.
Rows may be anchored in either of the two non-coordinate bases. -/
theorem rectangle_far (X : Ix → V) (hm : MUBPair X)
    (z : V) (hz : unitRow z) (hu : ∀ a, Complex.normSq (rowSum (X a) z) = 10)
    (r₀ : Ix) (j₀ : Fin 10) :
    ∃ r j, ∀ k : Fin 4, radius ≤ ‖rectangle X r₀ j₀ r j - Complex.I ^ k.val‖ := by
  classical
  let c : V := fun j => conj (X r₀ j) * X r₀ j₀
  let a : Ix → ℂ := fun r => conj (X r j₀)
  have hc : unitRow c := fun j => by
    simp [c, Complex.norm_mul, Complex.norm_conj, hm.1 r₀ j, hm.1 r₀ j₀]
  have ha (r) : ‖a r‖ = 1 := by simp [a, Complex.norm_conj, hm.1 r j₀]
  let Y : Ix → V := fun r => twist c (a r) (X r)
  have hY : MUBPair Y := ⟨fun r => twist_unit c _ _ hc (hm.1 r) (ha r),
    fun r s => (twist_gram c _ _ _ _ hc (ha r) (ha s)).trans (hm.2 r s)⟩
  have rect (r j) : Y r j = rectangle X r₀ j₀ r j := by unfold Y twist a c rectangle; ring
  by_contra! bad
  choose P hP using bad
  let d (p : Ix × Fin 10) : ℝ := ‖Y p.1 p.2 - Complex.I ^ (P p.1 p.2).val‖
  obtain ⟨m,_,hmax⟩ := Finset.exists_max_image Finset.univ d Finset.univ_nonempty
  have hd : d m < radius := by simpa [d,rect] using hP m.1 m.2
  have close (r) : near (Y r) (phaseOf (P r)) (d m) := fun j => hmax (r,j) (Finset.mem_univ _)
  have one_norm : ‖(1:ℂ)‖ = 1 := by
    have h := Complex.sq_norm (1:ℂ)
    rw [map_one] at h
    nlinarith [norm_nonneg (1:ℂ)]
  apply near_quaternary_no_ray Y P hY hd close (twist c 1 z) (twist_unit c z 1 hc hz one_norm)
  intro r
  exact (twist_gram c _ _ _ 1 hc (ha r) one_norm).trans (hu r)

#print axioms rectangle_far
end
end MUB10Radius
