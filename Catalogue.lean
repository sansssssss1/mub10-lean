import ComplexBridge
import Mathlib.Tactic.FinCases

/-! The ten input matrices, in Aalto's order, are the catalogue of Lampio,
Szöllősi and Östergård. MainResult proves coverage of arbitrary input matrices.
The enumeration of mates for each input matrix is checked here.
https://wiki.aalto.fi/pages/viewpage.action?pageId=63546913 -/
namespace MUB10Catalogue

abbrev Phase := Fin 4
abbrev Row := List Phase
abbrev Basis := List Row

def catalogueText := include_str "aalto-bh4-10.txt"

def parseRow (s : String) : Row :=
  s.toList.map (fun c => ((c.toNat - '0'.toNat : Nat) : Phase))

def catalogueRows : List Basis :=
  ((catalogueText.replace "\r" "").trim.splitOn "\n").map
    (fun line => (line.splitOn " ").map parseRow)

/-- Catalogue indices are zero based, so index 2 is Aalto matrix #3. -/
def catalogue (i : Fin 10) : Basis := catalogueRows.getD i.val []

def dephase (r : Row) : Row := r.map fun x => x - r.headD 0

def baseRows (useK : Bool) : Basis :=
  let rs := if useK then MUB10.phaseTable.drop 10 else MUB10.phaseTable.take 10
  rs.map fun r => r.map (fun n => (n : Phase))

structure Witness where
  swap : Bool
  anchor : Fin 10
  perm : List (Fin 10)
deriving Repr, DecidableEq

/-- All operations are common coordinate phases/permutation, followed by
an irrelevant separate phase on each row to make its first entry one. -/
def transformed (w : Witness) (r : Row) : Row :=
  let a := (baseRows w.swap).getD w.anchor.val []
  dephase (w.perm.map fun j => r.getD j.val 0 - a.getD j.val 0)

def sourceH (w : Witness) : Basis := (baseRows w.swap).map (transformed w)
def sourceK (w : Witness) : Basis := (baseRows (!w.swap)).map (transformed w)

def witnesses : List Witness :=
  [⟨false,0,[0,2,4,7,5,6,1,9,8,3]⟩,
  ⟨false,0,[0,2,7,4,5,9,8,6,1,3]⟩,
  ⟨false,0,[0,3,1,8,5,9,4,6,7,2]⟩,
  ⟨false,0,[0,3,8,1,5,6,7,9,4,2]⟩,
  ⟨false,0,[0,6,4,8,5,2,1,3,7,9]⟩,
  ⟨false,0,[0,6,8,4,5,3,7,2,1,9]⟩,
  ⟨false,0,[0,9,1,7,5,3,4,2,8,6]⟩,
  ⟨false,0,[0,9,7,1,5,2,8,3,4,6]⟩,
  ⟨false,0,[1,2,4,9,5,6,0,7,3,8]⟩,
  ⟨false,0,[1,2,9,4,5,7,3,6,0,8]⟩,
  ⟨false,0,[1,6,3,4,5,8,9,2,0,7]⟩,
  ⟨false,0,[1,6,4,3,5,2,0,8,9,7]⟩,
  ⟨false,0,[1,7,0,9,5,8,4,2,3,6]⟩,
  ⟨false,0,[1,7,9,0,5,2,3,8,4,6]⟩,
  ⟨false,0,[1,8,0,3,5,7,4,6,9,2]⟩,
  ⟨false,0,[1,8,3,0,5,6,9,7,4,2]⟩,
  ⟨false,0,[2,0,4,7,5,1,6,8,9,3]⟩,
  ⟨false,0,[2,0,7,4,5,8,9,1,6,3]⟩,
  ⟨false,0,[2,1,4,9,5,0,6,3,7,8]⟩,
  ⟨false,0,[2,1,9,4,5,3,7,0,6,8]⟩,
  ⟨false,0,[2,3,6,9,5,8,4,1,7,0]⟩,
  ⟨false,0,[2,3,9,6,5,1,7,8,4,0]⟩,
  ⟨false,0,[2,8,6,7,5,3,4,0,9,1]⟩,
  ⟨false,0,[2,8,7,6,5,0,9,3,4,1]⟩,
  ⟨false,0,[4,3,1,6,5,9,0,8,2,7]⟩,
  ⟨false,0,[4,3,6,1,5,8,2,9,0,7]⟩,
  ⟨false,0,[4,7,0,2,5,8,1,9,6,3]⟩,
  ⟨false,0,[4,7,2,0,5,9,6,8,1,3]⟩,
  ⟨false,0,[4,8,0,6,5,7,1,3,2,9]⟩,
  ⟨false,0,[4,8,6,0,5,3,2,7,1,9]⟩,
  ⟨false,0,[4,9,1,2,5,3,0,7,6,8]⟩,
  ⟨false,0,[4,9,2,1,5,7,6,3,0,8]⟩,
  ⟨false,0,[9,0,1,7,5,4,3,8,2,6]⟩,
  ⟨false,0,[9,0,7,1,5,8,2,4,3,6]⟩,
  ⟨false,0,[9,4,1,2,5,0,3,6,7,8]⟩,
  ⟨false,0,[9,4,2,1,5,6,7,0,3,8]⟩,
  ⟨true,2,[0,1,9,4,6,2,3,8,5,7]⟩]

/-- Squared modulus of the inner product before dividing the rows by √10. -/
def gramSq (r s : Row) : Int :=
  let q := (List.zipWith (fun a b : Phase => MUB10.gaussianPhase (b-a).val) r s).foldl
    (fun v t : Int × Int => (v.1+t.1,v.2+t.2)) (0,0)
  q.1*q.1 + q.2*q.2

def acceptable (A : Basis) (r : Row) : Bool := A.all fun a => gramSq a r == 10
def orth (r s : Row) : Bool := gramSq r s == 0

/-- Input sanity checks. In this encoding a dephased row starts at exponent 0. -/
theorem catalogue_sanity : catalogueRows.length = 10 ∧ ∀ i : Fin 10,
    let A := catalogue i
    A.length = 10 ∧ A.Nodup ∧ A.all (fun r =>
      r.length == 10 && r.head? == some 0 && A.all (fun s =>
        gramSq r s == (if r = s then (100 : Int) else 0))) = true := by native_decide

/-- Walk the full four-way tree, retaining only acceptable leaves. -/
def rays (A : Basis) : Nat → Row → Basis
  | 0, pref => if acceptable A pref then [pref] else []
  | n+1, pref => rays A n (pref ++ [0]) ++ rays A n (pref ++ [1]) ++
                 rays A n (pref ++ [2]) ++ rays A n (pref ++ [3])

theorem rays_complete (A : Basis) (tail pref : Row)
    (ha : acceptable A (pref ++ tail) = true) : pref ++ tail ∈ rays A tail.length pref := by
  induction tail generalizing pref with
  | nil => simp_all [rays]
  | cons a tl ih =>
    have hh := ih (pref ++ [a]) (by simpa using ha)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hh
    fin_cases a <;> simp only [List.length_cons, rays, List.mem_append]
    · exact Or.inl (Or.inl (Or.inl hh))
    · exact Or.inl (Or.inl (Or.inr hh))
    · exact Or.inl (Or.inr hh)
    · exact Or.inr hh

/-- Include the first vertex, retaining its neighbours, or exclude it. -/
def cliques {α : Type} (ok : α → α → Bool) : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _+1, [] => []
  | n+1, a :: as => (cliques ok n (as.filter (ok a))).map (a :: ·) ++ cliques ok (n+1) as
termination_by n pool => (n,pool.length)

theorem cliques_complete {α : Type} [DecidableEq α] (ok : α → α → Bool)
    (n : Nat) (pool want : List α) (hs : want ⊆ pool) (hd : want.Nodup)
    (hl : want.length = n)
    (hp : ∀ a ∈ want, ∀ b ∈ want, a ≠ b → ok a b = true) :
    ∃ C ∈ cliques ok n pool, want.Perm C := by
  induction n generalizing pool want with
  | zero =>
    have he : want = [] := List.length_eq_zero_iff.mp hl
    subst want
    exact ⟨[], by simp [cliques], List.Perm.refl _⟩
  | succ n ih =>
    induction pool generalizing want with
    | nil =>
      have he : want = [] := List.eq_nil_iff_forall_not_mem.mpr fun a ha => by
        simpa using hs ha
      simp [he] at hl
    | cons a as it =>
      by_cases ha : a ∈ want
      · have pe := List.perm_cons_erase ha
        have ln : (want.erase a).length = n := by
          have hh := pe.length_eq
          simp only [List.length_cons] at hh
          omega
        have ss : want.erase a ⊆ as.filter (ok a) := by
          intro b hb
          obtain ⟨hne,hm⟩ := hd.mem_erase_iff.mp hb
          apply List.mem_filter.mpr
          refine ⟨?_, hp a ha b hm hne.symm⟩
          exact (List.mem_cons.mp (hs hm)).resolve_left hne
        obtain ⟨C,hC,hperm⟩ := ih (as.filter (ok a)) (want.erase a) ss (hd.erase a) ln
          (fun b hb c hc he => hp b (List.mem_of_mem_erase hb) c (List.mem_of_mem_erase hc) he)
        refine ⟨a::C, ?_, pe.trans (hperm.cons a)⟩
        simp only [cliques, List.mem_append, List.mem_map]
        exact Or.inl ⟨C,hC,rfl⟩
      · have ss : want ⊆ as := by
          intro b hb
          rcases List.mem_cons.mp (hs hb) with h|h
          · subst b; contradiction
          · exact h
        obtain ⟨C,hC,hperm⟩ := it want ss hd hl hp
        exact ⟨C, by rw [cliques]; exact List.mem_append_right _ hC, hperm⟩

def Matches (A B : Basis) (w : Witness) : Prop :=
  w.perm.Perm (List.finRange 10) ∧ A.Perm (sourceH w) ∧ B.Perm (sourceK w)

instance (A B : Basis) (w : Witness) : Decidable (Matches A B w) := by
  unfold Matches; infer_instance

def scan (i : Fin 10) : Nat × Nat × Bool :=
  let A := catalogue i
  let pool := rays A 9 [0]
  let cs := cliques orth 10 pool
  (pool.length, cs.length, cs.all fun C => witnesses.any fun w => decide (Matches A C w))

def rayCounts : List Nat := [176,304,432,152,304,232,132,232,80,112]
def mateCounts : List Nat := [0,0,36,0,0,0,0,0,0,1]

set_option maxRecDepth 100000 in
theorem scan_checked : ∀ i : Fin 10,
    scan i = (rayCounts.getD i.val 0, mateCounts.getD i.val 0, true) := by native_decide

/-- For an arbitrary ten-row matrix, only normalized row length, mutual
unbiasedness against the chosen H, distinctness and pairwise orthogonality
are required. The listed mates are outputs, never hypotheses. -/
theorem catalogue_pair (i : Fin 10) (B : Basis)
    (hlen : B.length = 10) (hd : B.Nodup)
    (hshape : ∀ r ∈ B, ∃ tail : Row, r = 0 :: tail ∧ tail.length = 9)
    (hcross : ∀ r ∈ B, ∀ a ∈ catalogue i, gramSq a r = 10)
    (horth : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → gramSq a b = 0) :
    ∃ w ∈ witnesses, w.perm.Perm (List.finRange 10) ∧
      (catalogue i).Perm (sourceH w) ∧ B.Perm (sourceK w) := by
  let A := catalogue i
  have sub : B ⊆ rays A 9 [0] := by
    intro r hr
    obtain ⟨tail,rfl,ht⟩ := hshape r hr
    have hacc : acceptable A ([0] ++ tail) = true := List.all_eq_true.mpr fun a ha =>
      beq_iff_eq.mpr (hcross _ hr a ha)
    simpa [ht] using rays_complete A tail [0] hacc
  obtain ⟨C,hC,hperm⟩ := cliques_complete orth 10 (rays A 9 [0]) B sub hd hlen
    (fun a ha b hb hne => beq_iff_eq.mpr (horth a ha b hb hne))
  have hh : ((cliques orth 10 (rays A 9 [0])).all fun D =>
    witnesses.any fun w => decide (Matches A D w)) = true := congrArg (fun z => z.2.2) (scan_checked i)
  obtain ⟨w,hw,hw'⟩ := List.any_eq_true.mp (List.all_eq_true.mp hh C hC)
  obtain ⟨h₁,h₂,h₃⟩ := of_decide_eq_true hw'
  exact ⟨w,hw,h₁,h₂,hperm.trans h₃⟩

end MUB10Catalogue
