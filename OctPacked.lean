import OctZeroPool
import OctCoverSearch

namespace MUB10Oct.Sixty

def wordCode : ORow → Nat
  | [] => 0
  | d::ds => d.val * 8^ds.length + wordCode ds

private theorem code_bound (r : ORow) : wordCode r < 8^r.length := by
  induction r with
  | nil => decide
  | cons a s ih =>
    change a.val*8^s.length + wordCode s < 8^(s.length+1)
    rw [pow_succ,Nat.mul_comm _ 8]
    calc
      _ < a.val*8^s.length + 8^s.length := Nat.add_lt_add_left ih _
      _ = (a.val+1)*8^s.length := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ a.isLt

private theorem code_le (r s : ORow) (hl : r.length=s.length) (h : wordCode r ≤ wordCode s) :
    r ≤ s := by
  induction r generalizing s with
  | nil => cases s <;> simp_all
  | cons a r ih =>
    cases s with
    | nil => simp at hl
    | cons b s =>
      have len : r.length=s.length := by simpa using hl
      change a.val*8^r.length+wordCode r ≤ b.val*8^s.length+wordCode s at h
      rw [len] at h
      rcases lt_trichotomy a b with hab|rfl|hba
      · exact (show a::r < b::s from List.Lex.rel hab).le
      · exact List.cons_le_cons _ (ih s len (by omega))
      · have hm := Nat.mul_le_mul_right (8^s.length) (show b.val+1 ≤ a.val from hba)
        rw [Nat.add_mul,one_mul] at hm
        have hh := code_bound s
        omega

structure FastRow where
  data : ORow
  key : Nat
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat

private def two (a b : O) : Nat := 8*a.val+b.val
private def cut (r : ORow) (i : Nat) := two (r.getD i 0) (r.getD (i+1) 0)
def packR (r : ORow) : FastRow :=
  ⟨r,wordCode r,cut r 0,cut r 2,cut r 4,cut r 6,cut r 8⟩

private def pairTable : Array Int := (Array.range 4096).map fun i =>
  let a : O := (i/512 : Nat)
  let b : O := (i/64 : Nat)
  let c : O := (i/8 : Nat)
  let d : O := (i : Nat)
  valCode (c-a)+valCode (d-b)

@[inline] private def pairScore (a b : Nat) := pairTable.getD (64*a+b) 0

private theorem pairScore_ok : ∀ a b c d : O,
    pairScore (two a b) (two c d) = valCode (c-a)+valCode (d-b) := by native_decide

def fastOrth (a b : FastRow) : Bool :=
  pairScore a.c0 b.c0 + pairScore a.c1 b.c1 + pairScore a.c2 b.c2 +
    pairScore a.c3 b.c3 + pairScore a.c4 b.c4 == 0
def fastLT (a b : FastRow) : Bool := a.key < b.key

theorem fastLT_ok {a b : ORow} (len : a.length=b.length) (h : a<b) :
    fastLT (packR a) (packR b)=true := by
  apply decide_eq_true
  exact lt_of_not_ge (fun hc => (not_lt_of_ge (code_le b a len.symm hc)) h)

theorem fastOrth_ok (a b : OQ) (h : score (List.ofFn a) (List.ofFn b)=0) :
    fastOrth (packR (List.ofFn a)) (packR (List.ofFn b))=true := by
  simp only [fastOrth,packR,cut,pairScore_ok,beq_iff_eq]
  simp only [List.ofFn_succ, List.ofFn_zero,score,List.zipWith_cons_cons,List.zipWith_nil_left,
    List.sum_cons,List.sum_nil, add_zero] at h ⊢
  simpa [add_assoc] using h

def rawZero : ORow := List.replicate 10 0
def anchors8 : OBasis :=
  (Zero.fromPair rawZero rawZero).filter (fitsPrefix8 [rawZero])
theorem anchor_full (r : ORow) (hn : ∃ t, r=0::t ∧ t.length=9)
    (hz : score rawZero r=0) (fit : fitsPrefix8 [rawZero] r=true) : r ∈ anchors8 :=
  List.mem_filter.mpr ⟨Zero.fromPair_full _ _ _ hn hz hz,fit⟩

def secondPool8 (h : ORow) : List FastRow :=
  ((Zero.fromPair rawZero h).map packR).filter (fastLT (packR h))
theorem secondPool8_full (h r : ORow) (hn : ∃ t, r=0::t ∧ t.length=9)
    (hz : score rawZero r=0) (hh : score h r=0) (hlt : h<r) (len : h.length=r.length) :
    packR r ∈ secondPool8 h := by
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨r, Zero.fromPair_full _ _ _ hn hz hh,rfl⟩,
    fastLT_ok len hlt⟩

def leavesWith (h : ORow) : List OBasis :=
  (search8 fastOrth FastRow.data fastLT (fun p r => fitsPrefix8 (p.map FastRow.data) r.data)
    8 [packR rawZero,packR h] (secondPool8 h)).map (List.map FastRow.data)
def fullLeaves8 : List OBasis := anchors8.flatMap leavesWith

end MUB10Oct.Sixty
