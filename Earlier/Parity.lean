import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Push

/-! The dimension-ten overlap equations after clearing a common odd denominator.
A pair (a,b) represents the phase (a+bi)/d. The phase overlap of two rows
has denominator d², so its squared modulus has denominator d⁴. -/

namespace MUB10.Earlier.Parity
open scoped BigOperators

abbrev Residue := ZMod 4
private def binary : Residue →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) _

private theorem product_color : ∀ a b c d : Residue,
    a*a + b*b = 1 → c*c + d*d = 1 →
    binary (a*d - b*c) = binary b + binary d := by decide

private theorem norm_two_color : ∀ a b : Residue,
    a*a + b*b = 2 → binary b = 1 := by decide

structure Phase (d : ℤ) where
  re : ℤ
  im : ℤ
  onCircle : re*re + im*im = d*d

abbrev Row (d : ℤ) := Fin 10 → Phase d

def realNumerator {d : ℤ} (u v : Row d) : ℤ := ∑ j, ((u j).re*(v j).re + (u j).im*(v j).im)
def imagNumerator {d : ℤ} (u v : Row d) : ℤ := ∑ j, ((u j).re*(v j).im - (u j).im*(v j).re)

def Unbiased {d : ℤ} (u v : Row d) : Prop :=
  realNumerator u v * realNumerator u v + imagNumerator u v * imagNumerator u v =
    10 * (d*d) * (d*d)

private def color {d : ℤ} (u : Row d) : ZMod 2 := ∑ j, binary ((u j).im : Residue)

private theorem odd_square (k : ℤ) : ((2*k+1 : ℤ) : Residue) * ((2*k+1 : ℤ) : Residue) = 1 := by
  push_cast
  exact (by decide : ∀ t : Residue, (2*t+1)*(2*t+1) = 1) _

private theorem pair_color {k : ℤ} (u v : Row (2*k+1)) (h : Unbiased u v) :
    color u + color v = 1 := by
  have hc (x : Phase (2*k+1)) : (x.re : Residue)*x.re + x.im*x.im = 1 := by
    have hx := congrArg (fun a : ℤ => (a : Residue)) x.onCircle
    push_cast at hx
    exact hx.trans (by simpa using odd_square k)
  have hn := congrArg (fun a : ℤ => (a : Residue)) h
  push_cast at hn
  have hs : (2*(k : Residue)+1)*(2*(k : Residue)+1) = 1 := by simpa using odd_square k
  rw [hs] at hn
  have him := norm_two_color _ _ (hn.trans (by decide))
  rw [imagNumerator, Int.cast_sum] at him
  simp only [Int.cast_sub, Int.cast_mul, map_sum, product_color _ _ _ _ (hc _) (hc _),
    Finset.sum_add_distrib] at him
  exact him

/-- Three flat raw rows with Gaussian-integer numerators on a common odd
denominator cannot satisfy all three dimension-ten unbiasedness equations. -/
theorem no_three_integer_phase_vectors (k : ℤ) (u v w : Row (2*k+1)) :
    ¬ (Unbiased u v ∧ Unbiased v w ∧ Unbiased w u) := by
  rintro ⟨huv,hvw,hwu⟩
  have no_cycle : ∀ a b c : ZMod 2, a+b = 1 → b+c = 1 → c+a = 1 → False := by decide
  exact no_cycle _ _ _ (pair_color _ _ huv) (pair_color _ _ hvw) (pair_color _ _ hwu)

#print axioms no_three_integer_phase_vectors
end MUB10.Earlier.Parity
