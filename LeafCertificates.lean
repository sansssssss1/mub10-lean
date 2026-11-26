import Gauge

/-! Explicit monomial equivalences for the 1,284 doubly sorted dephased leaves.
The data is checked entry by entry against the ten catalogue matrices. -/
namespace MUB10Radius
open MUB10Catalogue

structure LeafCertificate where
  L : Basis
  c : Fin 10
  π : List (Fin 10)
  col : Row
  row : Row
deriving DecidableEq

private def leafText := include_str "single-leaf-certificates.txt"

private def parseLeaf (s : String) : LeafCertificate :=
  let xs := s.splitOn " "
  let perm := (xs.getD 11 "").toList.map (fun c => ((c.toNat - '0'.toNat : Nat) : Fin 10))
  ⟨(xs.take 10).map parseRow, ((xs.getD 10 "").toNat! : Fin 10), perm,
    parseRow (xs.getD 12 ""), parseRow (xs.getD 13 "")⟩

def leafCertificates : List LeafCertificate :=
  ((leafText.replace "\r" "").trim.splitOn "\n").map parseLeaf

def certifiedLeaves : List Basis := leafCertificates.map (·.L)

private def datum (r : Row) (j : Fin 10) := r.getD j.val 0
private def unpack (L : Basis) (i : Fin 10) : Q := datum (L.getD i.val [])

private def permFun (w : LeafCertificate) (j : Fin 10) : Fin 10 := w.π.getD j.val 0
private def permInv (w : LeafCertificate) (j : Fin 10) : Fin 10 := (w.π.idxOf j : Fin 10)

private def changed (w : LeafCertificate) : Basis := List.ofFn fun r : Fin 10 =>
  pack fun j => datum w.row r + datum w.col j + unpack w.L r (permFun w j)

private def Valid (w : LeafCertificate) : Prop :=
  (∀ i, permInv w (permFun w i) = i ∧ permFun w (permInv w i) = i) ∧
    (changed w).Perm (catalogue w.c)

private instance (w : LeafCertificate) : Decidable (Valid w) := by unfold Valid; infer_instance

set_option maxRecDepth 100000 in
private theorem leaf_checks : leafCertificates.length = 1284 ∧
    (leafCertificates.all fun w => decide (Valid w)) = true := by native_decide

private lemma ofFn_getD {α : Type} (f : Fin 10 → α) (i : Fin 10) (a : α) :
    (List.ofFn f).getD i.val a = f i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some]

/-- A leaf accepted by the data file has an explicit ordinary monomial
equivalence to the actual catalogue, including an inverse permutation. -/
theorem certified_leaf_gauge (A : Fin 10 → Q)
    (mem : (List.ofFn fun i => pack (A i)) ∈ certifiedLeaves) :
    ∃ (c : Fin 10) (π : Fin 10 ≃ Fin 10) (col row : Q),
      (List.ofFn (fun r => pack (changeQ π col (row r) (A r)))).Perm (catalogue c) := by
  obtain ⟨w,hw,hL⟩ := List.mem_map.mp mem
  have valid : Valid w := of_decide_eq_true (List.all_eq_true.mp leaf_checks.2 w hw)
  let π : Fin 10 ≃ Fin 10 := ⟨permFun w, permInv w, fun j => (valid.1 j).1, fun j => (valid.1 j).2⟩
  refine ⟨w.c,π,datum w.col,datum w.row,?_⟩
  have same : ∀ i j, unpack w.L i j = A i j := by
    intro i j
    simp only [unpack, datum, hL, ofFn_getD, pack]
  have convert : changed w = List.ofFn (fun r => pack (changeQ π (datum w.col) (datum w.row r) (A r))) := by
    simp only [changed,changeQ,same]
    rfl
  rw [← convert]
  exact valid.2

#print axioms certified_leaf_gauge
end MUB10Radius
