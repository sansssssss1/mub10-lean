import OctCoverSearch
import OctLexNormal
import OctSixtyData

namespace MUB10Oct.Sixty

private lemma score_same (s : OQ) : score (pack8 s) (pack8 s) = 10 := by
  simp [score,pack8,List.ofFn_succ,valCode]

private lemma get_row (v : OQ) (j : Fin 10) : (pack8 v).getD j.val 0 = v j := by
  fin_cases j <;> rfl

/-- Transport a sorted, indexed matrix into the packed-row search. Only the semantic
completeness properties of the encodings and candidate pools are needed here. -/
theorem indexed8_complete {α : Type} (encode : ORow → α) (row : α → ORow)
    (ok lt : α → α → Bool) (anchors : OBasis) (pool : ORow → List α)
    (readback : ∀ r, row (encode r) = r)
    (fastLt : ∀ {r s : ORow}, r.length = s.length → r < s → lt (encode r) (encode s) = true)
    (fastOk : ∀ (a b : OQ), score (pack8 a) (pack8 b) = 0 → ok (encode (pack8 a)) (encode (pack8 b)) = true)
    (seed : ∀ r, (∃ t, r=0::t ∧ t.length=9) → score (List.replicate 10 0) r = 0 →
      fitsPrefix8 [List.replicate 10 0] r = true → r ∈ anchors)
    (poolFull : ∀ h r, (∃ t, r=0::t ∧ t.length=9) → score (List.replicate 10 0) r = 0 →
      score h r = 0 → h < r → h.length = r.length → encode r ∈ pool h)
    (T : Fin 10 → OQ) (hz : T 0 = fun _ => 0) (hc : ∀ i, T i 0 = 0)
    (weak : (List.ofFn (fun i => pack8 (T i))).Pairwise (· ≤ ·))
    (cols : ∀ j : Fin 9, (List.ofFn fun r => T r j.castSucc) ≤ List.ofFn fun r => T r j.succ)
    (orth : ∀ i j, i ≠ j → score (pack8 (T i)) (pack8 (T j)) = 0) :
    (List.ofFn fun i => pack8 (T i)) ∈ anchors.flatMap (fun h =>
      (search8 ok row lt (fun pre r => fitsPrefix8 (pre.map row) (row r)) 8
        [encode (List.replicate 10 0),encode h] (pool h)).map (List.map row)) := by
  let h := pack8 (T 1)
  let pre := [encode (List.replicate 10 0),encode h]
  let rows := List.ofFn fun i : Fin 8 => pack8 (T i.succ.succ)
  let rest := List.ofFn fun i : Fin 8 => encode (pack8 (T i.succ.succ))
  let A := List.ofFn fun i => pack8 (T i)
  have z0 : pack8 (T 0) = List.replicate 10 0 := by rw [hz]; rfl
  have head : A = List.replicate 10 0 :: h :: rows := by
    unfold A
    rw [List.ofFn_succ,z0,List.ofFn_succ]
    rfl
  have cp : ColumnsOrdered8 A := by
    intro j
    unfold column8 A
    rw [List.map_ofFn,List.map_ofFn]
    change (List.ofFn fun r => (pack8 (T r)).getD j.castSucc.val 0) ≤
      List.ofFn fun r => (pack8 (T r)).getD j.succ.val 0
    simpa only [get_row] using cols j
  have inj : Function.Injective fun i => pack8 (T i) := by
    intro i j e
    by_contra hn
    have ho := orth i j hn
    change pack8 (T i) = pack8 (T j) at e
    rw [e,score_same] at ho
    norm_num at ho
  have strict (i j : Fin 10) (hij : i < j) : pack8 (T i) < pack8 (T j) :=
    lt_of_le_of_ne (List.pairwise_ofFn.mp weak hij) (inj.ne hij.ne)
  have shape (i : Fin 10) : ∃ t, pack8 (T i) = 0::t ∧ t.length=9 :=
    ⟨_,by rw [pack8,List.ofFn_succ,hc],List.length_ofFn⟩
  have seedMem : h ∈ anchors := by
    apply seed h (shape 1)
    · rw [← z0]
      exact orth 0 1 (by decide)
    · apply fitsPrefix8_of_columns _ _ rows
      simpa only [head] using cp
  have mapped : (pre ++ rest).map row = A := by
    rw [head]
    simp only [pre,rest,rows,List.map_append,List.map_cons,List.map_nil,List.map_ofFn, readback,
      List.cons_append,List.nil_append,Function.comp_def]
  have sub : rest ⊆ pool h := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    apply poolFull h _ (shape i.succ.succ)
    · rw [← z0]
      exact orth _ _ (by fin_cases i <;> decide)
    · exact orth _ _ (by fin_cases i <;> decide)
    · exact strict _ _ (by fin_cases i <;> decide)
    · simp [h,pack8]
  have nd : rest.Nodup := by
    apply List.nodup_ofFn_ofInjective
    intro i j eqn
    have er := congrArg row eqn
    change row (encode (pack8 (T i.succ.succ))) = row (encode (pack8 (T j.succ.succ))) at er
    rw [readback,readback] at er
    exact Fin.succ_injective _ (Fin.succ_injective _ (inj er))
  have os : rest.Pairwise (fun r s => lt r s = true) := by
    apply List.pairwise_ofFn.mpr
    intro i j ij
    exact fastLt (by simp [pack8]) (strict _ _ (by simpa using ij))
  have or : rest.Pairwise (fun r s => ok r s = true) := by
    apply List.pairwise_ofFn.mpr
    intro i j ij
    exact fastOk _ _ (orth _ _ (by simpa using ij.ne))
  have incl := search8_of_columns ok row lt (fun p r => fitsPrefix8 (p.map row) (row r))
    (fun _ _ hf => hf) pre rest (pool h) sub nd os or (by rw [mapped]; exact cp)
  apply List.mem_flatMap.mpr
  refine ⟨h,seedMem,List.mem_map.mpr ⟨pre++rest,?_,mapped⟩⟩
  simpa only [rest,List.length_ofFn] using incl

end MUB10Oct.Sixty
