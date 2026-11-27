import OctLexNormal
import OctSixtyPhysical

open scoped BigOperators ComplexConjugate
namespace MUB10Oct.Sixty
open MUB10 MUB10Robust MUB10Radius MUB10Catalogue
noncomputable section

def move8 (π : Equiv.Perm (Fin 10)) (col : OQ) (s : ℂ) (x : V) : V :=
  fun j => s * val8 (col j) * x (π j)

theorem changeGram (π : Equiv.Perm (Fin 10)) (col : OQ) (s t : ℂ) (x y : V) :
    rowSum (move8 π col s x) (move8 π col t y) = conj s * t * rowSum x y := by
  unfold rowSum
  rw [Finset.mul_sum]
  conv_rhs => rw [← Equiv.sum_comp π]
  apply Finset.sum_congr rfl
  intro j _
  simp only [move8,map_mul]
  calc
    _ = (conj (val8 (col j))*val8 (col j)) * (conj s*t*(conj (x (π j))*y (π j))) := by ring
    _ = _ := by rw [← Complex.normSq_eq_conj_mul_self,val8_normSq]; simp

theorem changeProb (π : Equiv.Perm (Fin 10)) (col : OQ) (s t : ℂ)
    (hs : Complex.normSq s=1) (ht : Complex.normSq t=1) (x y : V) :
    Complex.normSq (rowSum (move8 π col s x) (move8 π col t y)) = Complex.normSq (rowSum x y) := by
  rw [changeGram]; simp [Complex.normSq_mul,hs,ht]

theorem phase_gauge (π : Equiv.Perm (Fin 10)) (col : OQ) (s : O) (r : OQ) :
    phase8 (gauge8 π col s r) = move8 π col (val8 s) (phase8 r) := by
  funext j
  simp [phase8,gauge8,move8,val8_add]

theorem score_gauge_zero (π : Equiv.Perm (Fin 10)) (col : OQ) (s t : O) (r q : OQ)
    (hz : score (pack8 r) (pack8 q)=0) :
    score (pack8 (gauge8 π col s r)) (pack8 (gauge8 π col t q))=0 := by
  apply (score_zero_iff _ _).mpr
  rw [phase_gauge,phase_gauge,changeGram,(score_zero_iff _ _).mp hz,mul_zero]

end
end MUB10Oct.Sixty
