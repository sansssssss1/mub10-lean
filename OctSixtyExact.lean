import OctSixtyScan
import OctSixtyLower

namespace MUB10Oct.Sixty
open MUB10Catalogue

theorem catalogue8_hadamard : ∀ i : Fin 60, (catalogue8 i).Nodup ∧
    (∀ r ∈ catalogue8 i, r.length=10 ∧ r.head?=some 0) ∧
    ∀ r ∈ catalogue8 i, ∀ s ∈ catalogue8 i, r≠s → score r s=0 := by native_decide

private def allCliques (i : Fin 60) := cliques (fun r s => score r s == 0) 10 (octPool i)

private theorem raw_sizes (i : Fin 60) : (octPool i).length = rayCount60.getD i.val 0 ∧
    (allCliques i).length = mateCount60 i :=
  ⟨congrArg Prod.fst (scan60_checked i), congrArg (fun x => x.2.1) (scan60_checked i)⟩

set_option maxRecDepth 100000 in
theorem exact_cardinalities : ∀ i : Fin 60,
    (explicitRays i).card = rayCount60.getD i.val 0 ∧
    (explicitMateSets i).card = mateCount60 i := by native_decide

private theorem in_pool (i : Fin 60) (r : ORow) (h : ValidRay i r) : r ∈ octPool i :=
  octPool_full i r (valid_shape i r h) h.2.2

private theorem rays_exhaust (i : Fin 60) : explicitRays i = (octPool i).toFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    exact List.mem_toFinset.mpr (in_pool i r ((witness_valid i).1 r hr))
  · rw [(exact_cardinalities i).1,← (raw_sizes i).1]
    exact List.toFinset_card_le _

theorem ray_iff (i : Fin 60) (r : ORow) : r ∈ explicitRays i ↔ ValidRay i r := by
  refine ⟨(witness_valid i).1 r,?_⟩
  intro h
  rw [rays_exhaust]
  exact List.mem_toFinset.mpr (in_pool i r h)

private theorem in_cliques (i : Fin 60) (B : OBasis) (h : ValidBasis i B) :
    B.toFinset ∈ ((allCliques i).map List.toFinset).toFinset := by
  obtain ⟨hl,hd,hv,ho⟩ := h
  have sub : B ⊆ octPool i := fun r hr => in_pool i r (hv r hr)
  obtain ⟨C,hm,hp⟩ := cliques_complete (fun r s => score r s == 0) 10 _ B sub hd hl
    (fun r hr s hs hn => by simpa using ho r hr s hs hn)
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨C,hm,List.toFinset_eq_of_perm _ _ hp.symm⟩)

private theorem mates_exhaust (i : Fin 60) :
    explicitMateSets i = ((allCliques i).map List.toFinset).toFinset := by
  apply Finset.eq_of_subset_of_card_le
  · intro C hc
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact in_cliques i B ((witness_valid i).2 B hB)
  · rw [(exact_cardinalities i).2,← (raw_sizes i).2]
    simpa using List.toFinset_card_le ((allCliques i).map List.toFinset)

/-- Sets of normalized rays identify all row permutations of the same basis. -/
theorem mate_set_iff (i : Fin 60) (S : Finset ORow) :
    S ∈ explicitMateSets i ↔ ∃ B : OBasis, ValidBasis i B ∧ B.toFinset = S := by
  constructor
  · intro h
    obtain ⟨B,hB,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact ⟨B,(witness_valid i).2 B hB,rfl⟩
  · rintro ⟨B,hB,rfl⟩
    rw [mates_exhaust]
    exact in_cliques i B hB

#print axioms exact_cardinalities
#print axioms mate_set_iff
end MUB10Oct.Sixty
