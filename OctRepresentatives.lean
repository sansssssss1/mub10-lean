import OctSixtyPhysical

namespace MUB10Oct.Sixty
open MUB10
open scoped BigOperators ComplexConjugate

def representative (m : Fin 60) (r j : Fin 10) : O :=
  ((catalogue8 m).getD r.val []).getD j.val 0

theorem representatives_exact : ∀ m : Fin 60,
    (List.ofFn fun r => List.ofFn (representative m r)) = catalogue8 m := by native_decide

private theorem offDiagonal : ∀ (m : Fin 60) (r s : Fin 10), r ≠ s →
    score (List.ofFn (representative m r)) (List.ofFn (representative m s)) = 0 := by native_decide

theorem representatives_hadamard (m : Fin 60) (r s : Fin 10) :
    rowSum (phase8 (representative m r)) (phase8 (representative m s)) =
      if r=s then 10 else 0 := by
  by_cases h : r=s
  · subst s
    simp [rowSum, ← Complex.normSq_eq_conj_mul_self, phase8, val8_normSq]
  · rw [if_neg h]
    exact (score_zero_iff _ _).mp (offDiagonal m r s h)

#print axioms representatives_hadamard
end MUB10Oct.Sixty
