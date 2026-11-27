import OctBasics
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Card

/-! Complete enumeration after fixing a prefix of a doubly sorted octonary matrix.
The executable predicate for prefix compatibility and the row representation can be
specialized to packed integers. The proof imposes no ordering on a candidate pool. -/
namespace MUB10Oct.Sixty

def column8 (A : OBasis) (j : Nat) := A.map fun r => r.getD j 0
def ColumnsOrdered8 (A : OBasis) : Prop := ∀ j : Fin 9, column8 A j.val ≤ column8 A (j.val+1)

def fitsPrefix8 (pre : OBasis) (r : ORow) : Bool :=
  (List.finRange 9).all fun j =>
    if pre.all (fun a => a.getD j.val 0 == a.getD (j.val+1) 0) then
      decide (r.getD j.val 0 ≤ r.getD (j.val+1) 0) else true

theorem fitsPrefix8_of_columns (pre : OBasis) (r : ORow) (xs : OBasis)
    (cols : ColumnsOrdered8 (pre ++ r :: xs)) : fitsPrefix8 pre r = true := by
  apply List.all_eq_true.mpr
  intro j _
  split
  next h =>
    have heq : column8 pre j.val = column8 pre (j.val+1) := List.map_congr_left fun a ha =>
      beq_iff_eq.mp (List.all_eq_true.mp h a ha)
    have hj := cols j
    simp only [column8, List.map_append, List.map_cons] at hj
    unfold column8 at heq
    rw [heq] at hj
    apply decide_eq_true
    apply le_of_not_gt
    intro hlt
    exact (not_lt_of_ge hj) (List.Lex.append_left (fun a b : O => a < b) (List.Lex.rel hlt) _)
  next => rfl

/-- For compatibility with cursor-based and packed representations, `row` is an
explicit interpretative parameter. The search only executes the supplied Boolean functions. -/
def search8 {α : Type} (ok : α → α → Bool) (row : α → ORow) (lt : α → α → Bool)
    (fits : List α → α → Bool) : Nat → List α → List α → List (List α)
  | 0, pre, _ => [pre]
  | n+1, pre, pool =>
    if pool.length ≤ n then []
    else pool.flatMap fun r =>
      if fits pre r then
        search8 ok row lt fits n (pre ++ [r]) (pool.filter fun s => lt r s && ok r s)
      else []

def FollowsFit8 {α : Type} (fits : List α → α → Bool) : List α → List α → Prop
  | _, [] => True
  | pre, r::rest => fits pre r = true ∧ FollowsFit8 fits (pre ++ [r]) rest

theorem followsFit8_of_columns {α : Type} (row : α → ORow) (fits : List α → α → Bool)
    (valid : ∀ pre r, fitsPrefix8 (pre.map row) (row r) = true → fits pre r = true)
    (pre rest : List α) (col : ColumnsOrdered8 ((pre ++ rest).map row)) :
    FollowsFit8 fits pre rest := by
  induction rest generalizing pre with
  | nil => trivial
  | cons r rs ih =>
    constructor
    · exact valid pre r (fitsPrefix8_of_columns (pre.map row) (row r) (rs.map row)
        (by simpa only [List.map_append,List.map_cons] using col))
    · apply ih
      simpa using col

private theorem length_of_sub {α : Type} {l s : List α} (hd : l.Nodup) (hs : l ⊆ s) :
    l.length ≤ s.length := by
  classical
  rw [← List.toFinset_card_of_nodup hd]
  apply le_trans _ s.toFinset_card_le
  exact Finset.card_le_card fun a ha => List.mem_toFinset.mpr (hs (List.mem_toFinset.mp ha))

theorem search8_complete {α : Type} (ok : α → α → Bool) (row : α → ORow) (lt : α → α → Bool)
    (fits : List α → α → Bool) (pre rest pool : List α) (hs : rest ⊆ pool) (hd : rest.Nodup)
    (ord : rest.Pairwise (fun r s => lt r s = true))
    (orth : rest.Pairwise (fun r s => ok r s = true))
    (fit : FollowsFit8 fits pre rest) :
    pre ++ rest ∈ search8 ok row lt fits rest.length pre pool := by
  induction rest generalizing pre pool with
  | nil => simp [search8]
  | cons r rs ih =>
    obtain ⟨lo,lor⟩ := List.pairwise_cons.mp ord
    obtain ⟨ho,hor⟩ := List.pairwise_cons.mp orth
    have sub : rs ⊆ pool.filter (fun s => lt r s && ok r s) := by
      intro s hrs
      exact List.mem_filter.mpr ⟨hs (List.mem_cons_of_mem _ hrs),by simp [lo s hrs,ho s hrs]⟩
    have enough := length_of_sub hd hs
    have bound : ¬ pool.length ≤ rs.length := by simp only [List.length_cons] at enough; omega
    have cont := ih (pre++[r]) _ sub (List.nodup_cons.mp hd).2 lor hor fit.2
    simp only [List.length_cons,search8,if_neg bound,List.mem_flatMap]
    refine ⟨r,hs List.mem_cons_self,?_⟩
    rw [if_pos fit.1]
    simpa using cont

theorem search8_of_columns {α : Type} (ok : α → α → Bool) (row : α → ORow) (lt : α → α → Bool)
    (fits : List α → α → Bool)
    (valid : ∀ pre r, fitsPrefix8 (pre.map row) (row r) = true → fits pre r = true)
    (pre rest pool : List α) (hs : rest ⊆ pool) (hd : rest.Nodup)
    (ord : rest.Pairwise (fun r s => lt r s = true))
    (orth : rest.Pairwise (fun r s => ok r s = true))
    (col : ColumnsOrdered8 ((pre ++ rest).map row)) :
    pre ++ rest ∈ search8 ok row lt fits rest.length pre pool :=
  search8_complete ok row lt fits pre rest pool hs hd ord orth
    (followsFit8_of_columns row fits valid pre rest col)

#print axioms search8_of_columns
end MUB10Oct.Sixty
