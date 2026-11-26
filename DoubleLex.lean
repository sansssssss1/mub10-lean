import Catalogue
import Mathlib.Data.List.Lex

namespace MUB10Radius
open MUB10Catalogue

def zeroRow : Row := List.replicate 10 0
def column (A : Basis) (j : Nat) := A.map (fun r => r.getD j 0)
def ColumnsOrdered (A : Basis) : Prop := ∀ j : Fin 9, column A j.val ≤ column A (j.val+1)

def fitsPrefix (pre : Basis) (r : Row) : Bool :=
  (List.finRange 9).all fun j =>
    if pre.all (fun a => a.getD j.val 0 == a.getD (j.val+1) 0) then
      decide (r.getD j.val 0 ≤ r.getD (j.val+1) 0) else true

private lemma cancel_prefix (pre x y : List Phase) (h : pre ++ x ≤ pre ++ y) : x ≤ y := by
  apply le_of_not_gt
  exact fun hlt => (not_lt_of_ge h) (List.Lex.append_left _ hlt pre)

private lemma fits_of_columns (pre : Basis) (r : Row) (xs : Basis)
    (h : ColumnsOrdered (pre ++ r :: xs)) : fitsPrefix pre r = true := by
  apply List.all_eq_true.mpr
  intro j _
  split
  next he =>
    have heq : column pre j.val = column pre (j.val+1) := List.map_congr_left fun a ha =>
      beq_iff_eq.mp (List.all_eq_true.mp he a ha)
    have hj := h j
    simp only [column, List.map_append, List.map_cons] at hj
    unfold column at heq
    rw [heq] at hj
    apply decide_eq_true
    apply le_of_not_gt
    exact fun hh => (not_lt_of_ge (cancel_prefix _ _ _ hj)) (List.Lex.rel hh)
  next => rfl

def allWords : Nat → List Row
  | 0 => [[]]
  | n+1 => (List.finRange 4).flatMap (fun d => (allWords n).map (d :: ·))

private theorem all_words_complete (r : Row) : r ∈ allWords r.length := by
  induction r with
  | nil => simp [allWords]
  | cons a tl ih =>
    simp only [List.length_cons, allWords, List.mem_flatMap, List.mem_map]
    exact ⟨a, List.mem_finRange _, tl, ih, rfl⟩

def firstPool : Basis :=
  ((allWords 9).map (fun tl => 0 :: tl)).filter fun r => gramSq zeroRow r == 0

/-- Keep all orthogonal lex-later rows in the pool. The column comparison only
constrains pairs of adjacent columns still tied on the prefix already chosen. -/
def search : Nat → Basis → Basis → List Basis
  | 0, pre, _ => [pre]
  | n+1, pre, pool => pool.flatMap fun r =>
    if fitsPrefix pre r then
      search n (pre ++ [r]) (pool.filter fun s => decide (r < s) && (gramSq r s == 0))
    else []

def leaves := search 9 [zeroRow] firstPool

private theorem covers (pre rest pool : Basis) (hs : rest ⊆ pool)
    (hl : rest.Pairwise (· < ·)) (ho : rest.Pairwise (fun r s => gramSq r s = 0))
    (hc : ColumnsOrdered (pre ++ rest)) :
    pre ++ rest ∈ search rest.length pre pool := by
  induction rest generalizing pre pool with
  | nil => simp [search]
  | cons r rs ih =>
    obtain ⟨lt,sl⟩ := List.pairwise_cons.mp hl
    obtain ⟨ort,so⟩ := List.pairwise_cons.mp ho
    have sub : rs ⊆ pool.filter (fun s => decide (r < s) && (gramSq r s == 0)) := by
      intro s h
      apply List.mem_filter.mpr
      exact ⟨hs (List.mem_cons_of_mem _ h), by simp [lt s h,ort s h]⟩
    have follow := ih (pre ++ [r]) _ sub sl so (by simpa using hc)
    simp only [List.length_cons, search, List.mem_flatMap]
    refine ⟨r, hs List.mem_cons_self, ?_⟩
    rw [if_pos (fits_of_columns pre r rs hc)]
    simpa using follow

theorem doubleLex_complete (rest : Basis) (len : rest.length = 9)
    (shape : ∀ r ∈ rest, ∃ tail : Row, r = 0 :: tail ∧ tail.length = 9)
    (ordered : (zeroRow :: rest).Pairwise (· < ·))
    (orth : (zeroRow :: rest).Pairwise (fun r s => gramSq r s = 0))
    (cols : ColumnsOrdered (zeroRow :: rest)) : zeroRow :: rest ∈ leaves := by
  have sub : rest ⊆ firstPool := by
    intro r hr
    obtain ⟨tl,rfl,ht⟩ := shape r hr
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨tl,ht ▸ all_words_complete tl,rfl⟩,
      beq_iff_eq.mpr ((List.pairwise_cons.mp orth).1 _ hr)⟩
  simpa [len, leaves] using covers [zeroRow] rest firstPool sub
    (List.pairwise_cons.mp ordered).2 (List.pairwise_cons.mp orth).2 cols

set_option maxRecDepth 100000 in
theorem leaf_count : leaves.length = 1284 := by native_decide

end MUB10Radius
