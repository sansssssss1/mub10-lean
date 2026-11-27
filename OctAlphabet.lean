import OctSixtyGlobalCore

namespace MUB10Oct.Sixty
open MUB10Robust

private theorem fourth_power : zeta8^4 = -1 := by
  rw [show 4=2*2 by decide,pow_mul,zeta8_sq,Complex.I_sq]

private theorem square_choices (x y : ℂ) (h : x^2=y^2) : x=y ∨ x= -y := by
  have eqn : (x-y)*(x+y)=0 := by linear_combination h
  rcases mul_eq_zero.mp eqn with hl|hr
  · exact Or.inl (sub_eq_zero.mp hl)
  · exact Or.inr (eq_neg_of_add_eq_zero_left hr)

/-- The eight encoded phases are exactly the complex solutions of z^8=1. -/
theorem eighth_roots_exact (z : ℂ) : z^8=1 ↔ ∃ k : O, z=val8 k := by
  have v0 : val8 0 = 1 := rfl
  have v1 : val8 1 = zeta8 := by change zeta8^1=zeta8; simp
  have v2 : val8 2 = Complex.I := zeta8_sq
  have v3 : val8 3 = Complex.I*zeta8 := by change zeta8^3=Complex.I*zeta8; rw [pow_succ,zeta8_sq]
  have shift (a : O) : val8 (a+4) = -val8 a := by
    rw [val8_add, show val8 4 = -1 from fourth_power]; ring
  have pick (a : O) (h : z=val8 a ∨ z= -val8 a) : ∃ k : O, z=val8 k := by
    rcases h with h|h
    · exact ⟨a,h⟩
    · exact ⟨a+4,(shift a).symm ▸ h⟩
  constructor
  · intro h
    rcases square_choices (z^4) 1 (by simpa [← pow_mul] using h) with hp|hm
    · rcases square_choices (z^2) 1 (by simpa [← pow_mul] using hp) with he|ho
      · apply pick 0; rw [v0]; exact square_choices _ _ (by simpa using he)
      · apply pick 2; rw [v2]; exact square_choices _ _ (by simpa using ho)
    · rcases square_choices (z^2) Complex.I (by simpa [← pow_mul] using hm) with he|ho
      · apply pick 1; rw [v1]; exact square_choices _ _ (by rwa [zeta8_sq])
      · apply pick 3; rw [v3]; exact square_choices _ _ (by simpa [mul_pow,zeta8_sq] using ho)
  · rintro ⟨k,rfl⟩
    unfold val8
    rw [← pow_mul,Nat.mul_comm,pow_mul]
    have h8 : zeta8^8=1 := by rw [show 8=4*2 by decide,pow_mul,fourth_power]; norm_num
    simp [h8]

theorem relative_eighth_power (r : V) (hr : unitRow r) :
    RelativeOct r ↔ ∀ j, (r j / r 0)^8=1 := by
  have hn : r 0 ≠ 0 := by intro h; have := hr 0; simp [h] at this
  constructor
  · intro h j
    obtain ⟨k,hk⟩ := h j
    apply (eighth_roots_exact _).2
    exact ⟨k, by rw [hk]; field_simp⟩
  · intro h j
    obtain ⟨k,hk⟩ := (eighth_roots_exact _).1 (h j)
    exact ⟨k, by rw [div_eq_iff hn] at hk; simpa [mul_comm] using hk⟩

#print axioms eighth_roots_exact
end MUB10Oct.Sixty
