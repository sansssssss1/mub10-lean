import OctBasics
import Mathlib.Data.Real.Irrational

/-! Eighth-root phases and their complex multiplication and conjugation laws. -/
open scoped BigOperators ComplexConjugate
namespace MUB10Oct
open MUB10 MUB10Robust MUB10Radius MUB10Catalogue MUB10.Certificate
noncomputable section

def zeta8 : ℂ := ⟨Real.sqrt 2 / 2, Real.sqrt 2 / 2⟩
def val8 (e : O) : ℂ := zeta8 ^ e.val
def phase8 (r : OQ) : V := fun j => val8 (r j)

theorem zeta8_sq : zeta8 ^ 2 = Complex.I := by
  apply Complex.ext <;> simp [zeta8, pow_two, Complex.mul_re, Complex.mul_im]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem zeta8_normSq : Complex.normSq zeta8 = 1 := by
  simp [zeta8, Complex.normSq_apply]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

private theorem zeta8_pow_eight : zeta8 ^ 8 = 1 := by
  rw [show 8 = 2*4 by decide, pow_mul, zeta8_sq]
  norm_num [pow_succ, Complex.I_mul_I]

theorem val8_add (e f : O) : val8 (e+f) = val8 e * val8 f := by
  change zeta8 ^ ((e.val+f.val)%8) = zeta8^e.val * zeta8^f.val
  rw [← pow_add]
  set n := e.val + f.val
  calc
    _ = zeta8 ^ (n%8) * (zeta8 ^ 8) ^ (n/8) := by simp [zeta8_pow_eight]
    _ = _ := by rw [← pow_mul, ← pow_add, Nat.mod_add_div]

theorem val8_normSq (e : O) : Complex.normSq (val8 e) = 1 := by simp [val8,map_pow,zeta8_normSq]

theorem val8_sub (e f : O) : val8 (e-f) = val8 e * conj (val8 f) := by
  have add := val8_add (e-f) f
  rw [sub_add_cancel] at add
  calc
    _ = val8 (e-f) * (val8 f * conj (val8 f)) := by simp [Complex.mul_conj,val8_normSq]
    _ = _ := by rw [← mul_assoc, ← add]

theorem val8_split (e : O) :
    val8 e = Complex.I ^ (digit e).val * (if bit e then zeta8 else 1) := by
  have he : ∀ k : O, k.val = 2 * (digit k).val + (if bit k then 1 else 0) := by decide
  unfold val8
  conv_lhs => rw [he e, pow_add, pow_mul, zeta8_sq]
  cases hb : bit e <;> simp

theorem phase8_even (r : OQ) (h : ∀ j, bit (r j) = false) :
    phase8 r = phaseOf (fun j => digit (r j)) := by
  funext j
  simp [phase8, val8_split,h,phaseOf]

theorem val8_oct_false (a : Phase) : val8 (oct false a) = Complex.I ^ a.val := by
  rw [val8_split]
  have aux : ∀ p : Phase, digit (oct false p) = p ∧ bit (oct false p) = false := by decide
  simp [(aux a).1,(aux a).2]


end
end MUB10Oct
