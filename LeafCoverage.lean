import DoubleLex
import LeafCertificates

namespace MUB10Radius
open MUB10 MUB10Catalogue MUB10Robust
open scoped BigOperators ComplexConjugate

set_option maxRecDepth 100000 in
theorem leaves_match_certificates : leaves = certifiedLeaves := by native_decide

private lemma self_gram (p : Q) : gramSq (pack p) (pack p) = 100 := by
  have h : rowSum (phaseOf p) (phaseOf p) = 10 := by
    simp only [rowSum, ← Complex.normSq_eq_conj_mul_self]
    simp [phaseOf, map_pow]
  have hh := physical_gram p p
  rw [h] at hh
  norm_num [Complex.normSq_apply] at hh
  exact_mod_cast hh.symm

private lemma get_pack (p : Q) (i : Fin 10) : (pack p).getD i.val 0 = p i := by
  fin_cases i <;> rfl

theorem normalized_leaf (T : Fin 10 → Q) (hz : T 0 = fun _ => 0)
    (hc : ∀ i, T i 0 = 0) (weak : (List.ofFn (fun r => pack (T r))).Pairwise (· ≤ ·))
    (cols : ∀ j : Fin 9, (List.ofFn fun r => T r j.castSucc) ≤ List.ofFn (fun r => T r j.succ))
    (orth : ∀ r s, r ≠ s → gramSq (pack (T r)) (pack (T s)) = 0) :
    (List.ofFn fun i => pack (T i)) ∈ certifiedLeaves := by
  let rest : Basis := List.ofFn fun i : Fin 9 => pack (T i.succ)
  have head : (List.ofFn fun r => pack (T r)) = zeroRow :: rest := by
    rw [List.ofFn_succ, hz]; rfl
  have strict : (List.ofFn fun r => pack (T r)).Pairwise (· < ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    apply lt_of_le_of_ne (List.pairwise_ofFn.mp weak hij)
    intro eqn
    have ho := orth i j (ne_of_lt hij)
    rw [eqn, self_gram] at ho
    norm_num at ho
  have op : (List.ofFn fun r => pack (T r)).Pairwise (fun r s => gramSq r s = 0) :=
    List.pairwise_ofFn.mpr fun _ _ h => orth _ _ (ne_of_lt h)
  have cp : ColumnsOrdered (List.ofFn fun r => pack (T r)) := by
    intro j
    unfold column
    rw [List.map_ofFn, List.map_ofFn]
    change (List.ofFn fun r => (pack (T r)).getD j.castSucc.val 0) ≤
      List.ofFn (fun r => (pack (T r)).getD j.succ.val 0)
    simpa only [get_pack] using (show (List.ofFn fun r => T r j.castSucc) ≤
      List.ofFn (fun r => T r j.succ) from cols j)
  rw [← leaves_match_certificates, head]
  rw [head] at strict op cp
  apply doubleLex_complete rest List.length_ofFn _ strict op cp
  intro r hr
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
  exact ⟨_, by rw [pack, List.ofFn_succ, hc], List.length_ofFn⟩

end MUB10Radius
