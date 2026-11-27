import OctOverlap

/-! Invariance of physical octonary measurements under an independent scalar phase on each ray.
Only the orthogonality and unbiasedness of the actual physical rows are used. -/
open scoped BigOperators ComplexConjugate
namespace MUB10Oct
open MUB10 MUB10Robust MUB10Radius MUB10Catalogue
noncomputable section

def multiplyRow (s : ℂ) (x : V) : V := fun j => s*x j

private theorem scaled_gram (s t : ℂ) (x y : V) :
    rowSum (multiplyRow s x) (multiplyRow t y) = conj s * t * rowSum x y := by
  unfold rowSum multiplyRow
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [map_mul]; ring

theorem scaled_probability (s t : ℂ) (hs : Complex.normSq s=1)
    (ht : Complex.normSq t=1) (x y : V) :
    Complex.normSq (rowSum (multiplyRow s x) (multiplyRow t y)) =
      Complex.normSq (rowSum x y) := by
  rw [scaled_gram]; simp [Complex.normSq_mul,hs,ht]

theorem remove_phases_pair (X Y : Ix → V) (κ : Ix → ℂ)
    (hκ : ∀ a, Complex.normSq (κ a)=1) (hrep : ∀ a, X a = multiplyRow (κ a) (Y a))
    (hm : MUBPair X) : MUBPair Y := by
  constructor
  · intro a j
    have ht := hm.1 a j
    have hs : ‖κ a‖=1 := by nlinarith [Complex.sq_norm (κ a),hκ a,norm_nonneg (κ a)]
    simpa [hrep a,multiplyRow,Complex.norm_mul,hs] using ht
  · intro a b
    have h := hm.2 a b
    rw [hrep a,hrep b,scaled_probability _ _ (hκ a) (hκ b)] at h
    exact h


end
end MUB10Oct
