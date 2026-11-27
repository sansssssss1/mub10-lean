import OctSixtyData

/-! Monomial equivalences from the 15,564 dephased, doubly lexicographically
ordered leaves to the order-ten octonary catalogue. -/
namespace MUB10Oct.Sixty

private structure Certificate where
  L : OBasis
  c : Fin 60
  perm : List (Fin 10)
  col : ORow
  row : ORow

private def certText := include_str "oct-leaf-certificates.txt"

private def parseOct (s : String) : ORow :=
  s.toList.map fun x => ((x.toNat-'0'.toNat : Nat) : O)

private def parseCertificate (s : String) : Certificate :=
  let xs := s.splitOn " "
  let p := (xs.getD 11 "").toList.map (fun x => ((x.toNat-'0'.toNat : Nat) : Fin 10))
  ⟨(xs.take 10).map parseOct, ((xs.getD 10 "").toNat! : Fin 60), p,
    parseOct (xs.getD 12 ""), parseOct (xs.getD 13 "")⟩

private def certificates : List Certificate :=
  ((certText.replace "\r" "").trim.splitOn "\n").map parseCertificate

def certifiedLeaves8 : List OBasis := certificates.map (·.L)

private def datum (r : ORow) (j : Fin 10) : O := r.getD j.val 0
private def unpack (A : OBasis) (i : Fin 10) : OQ := datum (A.getD i.val [])
private def pfun (w : Certificate) (j : Fin 10) := w.perm.getD j.val 0
private def pinv (w : Certificate) (j : Fin 10) : Fin 10 := (w.perm.idxOf j : Fin 10)

private def transformed (w : Certificate) : OBasis := List.ofFn fun r : Fin 10 =>
  List.ofFn fun j : Fin 10 => datum w.row r + datum w.col j + unpack w.L r (pfun w j)

private def Correct (w : Certificate) : Prop :=
  (∀ i, pinv w (pfun w i)=i ∧ pfun w (pinv w i)=i) ∧ (transformed w).Perm (catalogue8 w.c)

private instance (w : Certificate) : Decidable (Correct w) := by unfold Correct; infer_instance

set_option maxRecDepth 100000 in
private theorem verified : certificates.length = 15564 ∧
    (certificates.all fun w => decide (Correct w)) = true := by native_decide

private lemma getD_ofFn {α : Type} (f : Fin 10 → α) (i : Fin 10) (a : α) :
    (List.ofFn f).getD i.val a = f i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt,Option.getD_some]

theorem certified_leaf_gauge8 (A : Fin 10 → OQ)
    (mem : (List.ofFn fun i => List.ofFn (A i)) ∈ certifiedLeaves8) :
    ∃ (c : Fin 60) (π : Fin 10 ≃ Fin 10) (col row : OQ),
      (List.ofFn (fun r => List.ofFn fun j => row r + col j + A r (π j))).Perm (catalogue8 c) := by
  obtain ⟨w,hw,hL⟩ := List.mem_map.mp mem
  have h : Correct w := of_decide_eq_true (List.all_eq_true.mp verified.2 w hw)
  let π : Fin 10 ≃ Fin 10 := ⟨pfun w,pinv w,fun j => (h.1 j).1,fun j => (h.1 j).2⟩
  refine ⟨w.c,π,datum w.col,datum w.row,?_⟩
  have same : ∀ i j, unpack w.L i j = A i j := by
    intro i j
    simp only [unpack,datum,hL,getD_ofFn]
  have h' := h.2
  simpa only [transformed,same] using h'

#print axioms certified_leaf_gauge8
end MUB10Oct.Sixty
