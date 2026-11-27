import OctSixtyPool

namespace MUB10Oct.Sixty
open MUB10Catalogue

def rayCount60 : List Nat :=
  [560,216,400,560,224,336,320,304,912,400,304,232,144,160,192,128,32,60,128,192,
   232,144,232,144,192,128,172,112,360,80,360,128,24,48,60,224,224,400,400,320,
   144,232,192,192,192,24,224,24,32,24,20,22,22,0,8,20,20,20,0,0]

def mateCount60 (i : Fin 60) : Nat := if i=8 then 36 else if i=27 then 1 else 0

def scan60 (i : Fin 60) : Nat × Nat × Bool :=
  let rs := octPool i
  let cs := cliques (fun r s => score r s == 0) 10 rs
  (rs.length, cs.length, cs.all fun B => B.all fun r => r.all fun x => !bit x)

set_option maxRecDepth 100000 in
theorem scan60_checked : ∀ i : Fin 60, scan60 i = (rayCount60.getD i.val 0, mateCount60 i, true) := by
  native_decide

private theorem even_anchors : ∀ i : Fin 60, i=8 ∨ i=27 →
    ∀ h ∈ catalogue8 i, ∀ x ∈ h, bit x=false := by native_decide

/-- Every order-ten clique in the full octonary ray graph has a quaternary
anchor and quaternary dephased rows. Indices use Aalto's zero-based order. -/
theorem catalogue8_mate (i : Fin 60) (B : OBasis) (hlen : B.length=10) (hd : B.Nodup)
    (hn : ∀ r ∈ B, ∃ t, r=0::t ∧ t.length=9)
    (hx : ∀ r ∈ B, ∀ h ∈ catalogue8 i, score h r ∈ targets)
    (ho : ∀ r ∈ B, ∀ s ∈ B, r≠s → score r s=0) :
    (i=8 ∨ i=27) ∧ (∀ h ∈ catalogue8 i, ∀ x ∈ h, bit x=false) ∧
      ∀ r ∈ B, ∀ x ∈ r, bit x=false := by
  have sub : B ⊆ octPool i := fun r hr => octPool_full i r (hn r hr) (hx r hr)
  let cs := cliques (fun r s => score r s == 0) 10 (octPool i)
  obtain ⟨C,hm,hp⟩ := cliques_complete (fun r s => score r s == 0) 10 _ B sub hd hlen
    (fun r hr s hs hn => by simpa using ho r hr s hs hn)
  have count : cs.length = mateCount60 i := congrArg (fun s => s.2.1) (scan60_checked i)
  have pos : 0 < mateCount60 i := count ▸ List.length_pos_of_mem hm
  have idx : i=8 ∨ i=27 := by
    by_contra! hh
    simp [mateCount60,hh.1,hh.2] at pos
  refine ⟨idx,even_anchors i idx,?_⟩
  have allC : cs.all (fun D => D.all fun r => r.all fun x => !bit x) = true :=
    congrArg (fun s => s.2.2) (scan60_checked i)
  intro r hr x hxr
  simpa using List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp allC C hm) r (hp.mem_iff.mp hr)) x hxr

#print axioms catalogue8_mate
end MUB10Oct.Sixty
