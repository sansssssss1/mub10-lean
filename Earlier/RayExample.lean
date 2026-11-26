import Robust
import Mathlib.Data.Matrix.Notation

/-! Three distinct flat rays with pairwise unbiased measurements. Their phases
have real and imaginary parts in ℚ(√3). The calculation uses the same complex
inner product and normalization as the main theorem. -/

namespace MUB10.Earlier.RayExample
open scoped ComplexConjugate
open MUB10 MUB10Robust
noncomputable section

private def z : ℂ := ⟨-4/5, 3/5⟩
private def omega : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩

def v : V := fun _ => 1
def w : V := fun j => if j.val < 5 then 1 else z
def u : V := ![-omega, -conj omega, Complex.I, Complex.I, Complex.I, 1, -1, 1, omega, conj omega]

private lemma z_unit : Complex.normSq z = 1 := by norm_num [z, Complex.normSq_apply]

private lemma omega_unit : Complex.normSq omega = 1 := by
  simp only [omega, Complex.normSq_apply]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

theorem raw_moduli (j : Fin 10) : Complex.normSq (v j) = 1 ∧
    Complex.normSq (w j) = 1 ∧ Complex.normSq (u j) = 1 := by
  fin_cases j <;> norm_num [v,w,u,z_unit,omega_unit, Complex.normSq_conj]

private def target : ℂ := 1 + 3*Complex.I

private theorem overlaps : rowSum v w = target ∧ rowSum v u = target ∧ rowSum w u = target := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    norm_num [rowSum,Fin.sum_univ_succ,v,w,u,z,omega,target,Complex.mul_re,Complex.mul_im]
  all_goals ring

/-- Squared overlaps of the normalized rays, including all three cross-pairs. -/
theorem three_unbiased_rays :
    Complex.normSq (rowSum (normalized v) (normalized w)) = 1/10 ∧
    Complex.normSq (rowSum (normalized v) (normalized u)) = 1/10 ∧
    Complex.normSq (rowSum (normalized w) (normalized u)) = 1/10 := by
  simp only [normalized_probability, overlaps.1, overlaps.2.1, overlaps.2.2]
  norm_num [target,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]

#print axioms three_unbiased_rays

end
end MUB10.Earlier.RayExample
