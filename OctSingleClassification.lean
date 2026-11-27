import OctIndexedCover
import OctLeafMatch
import OctSixtyGlobalCore

/-! Every octonary Hadamard matrix of order ten is equivalent to a listed
matrix. Row/column permutations and independent eighth-root phases suffice. -/
namespace MUB10Oct.Sixty

theorem searched_matrix8 (T : Fin 10 → OQ) (hz : T 0 = fun _ => 0) (hc : ∀ i, T i 0 = 0)
    (weak : (List.ofFn (fun i => pack8 (T i))).Pairwise (· ≤ ·))
    (cols : ∀ j : Fin 9, (List.ofFn fun r => T r j.castSucc) ≤ List.ofFn fun r => T r j.succ)
    (orth : ∀ i j, i ≠ j → score (pack8 (T i)) (pack8 (T j)) = 0) :
    (List.ofFn fun i => pack8 (T i)) ∈ fullLeaves8 :=
  indexed8_complete packR FastRow.data fastOrth fastLT anchors8 secondPool8 (fun _ => rfl)
    fastLT_ok fastOrth_ok anchor_full secondPool8_full T hz hc weak cols orth

private lemma compose_gauge8 (π α : Equiv.Perm (Fin 10)) (c d : OQ) (s t : O) (v : OQ) :
    gauge8 α d t (gauge8 π c s v) =
      gauge8 (α.trans π) (fun j => d j + c (α j)) (t+s) v := by
  funext j
  dsimp [gauge8]
  abel

theorem single_oct_classification : SingleOctClassification := by
  intro A hA
  obtain ⟨σ,π,c,r,hz,hcol,hweak,hlex⟩ := lex_normal A
  let T := fun k => gauge8 π c (r (σ k)) (A (σ k))
  have ho (i j : Fin 10) (hn : i ≠ j) : score (pack8 (T i)) (pack8 (T j)) = 0 :=
    score_gauge_zero _ _ _ _ _ _ (hA _ _ (σ.injective.ne hn))
  have leaf := searched_matrix8 T hz hcol hweak hlex ho
  rw [all_leaves_certified8] at leaf
  obtain ⟨m,α,d,t,hm⟩ := certified_leaf_gauge8 T leaf
  let v := fun j => d j + c (α j)
  let w := fun j => t (σ.symm j) + r j
  refine ⟨m,α.trans π,v,w,?_⟩
  let f := fun i => pack8 (gauge8 (α.trans π) v (w i) (A i))
  apply (Equiv.Perm.ofFn_comp_perm σ f).symm.trans
  change (List.ofFn fun i => pack8 (gauge8 α d (t i) (T i))).Perm (catalogue8 m) at hm
  unfold f
  simpa only [Function.comp_def,T,compose_gauge8,w,v,Equiv.symm_apply_apply] using hm

#print axioms single_oct_classification
end MUB10Oct.Sixty
