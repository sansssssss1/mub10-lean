import OctBasics
import Mathlib.Data.List.Lex

/-! Simultaneous row and column lexicographic normal form for a dephased
octonary matrix. A weighted sum decreases strictly when an inverted pair is swapped. -/
open scoped BigOperators
namespace MUB10Oct.Sixty
open MUB10Oct

def pack8 (v : OQ) : ORow := List.ofFn v

def gauge8 (π : Equiv.Perm (Fin 10)) (col : OQ) (s : O) (r : OQ) : OQ := fun j => s + col j + r (π j)

private def weight (j : Fin 10) : Nat := 8 ^ (9 - j.val)
private def score (v : OQ) : Nat := ∑ j, weight j * (v j).val
private def cost (M : Fin 10 → OQ) : Nat := ∑ i, weight i * score (M i)
private def radix : List (Fin 8) → Nat
  | [] => 0
  | a :: s => a.val * 8 ^ s.length + radix s

private theorem radix_bound (s : List (Fin 8)) : radix s < 8 ^ s.length := by
  induction s with
  | nil => decide
  | cons a s ih =>
    change a.val * 8 ^ s.length + radix s < 8 ^ (s.length + 1)
    rw [pow_succ, Nat.mul_comm _ 8]
    calc
      _ < a.val * 8 ^ s.length + 8 ^ s.length := Nat.add_lt_add_left ih _
      _ = (a.val + 1) * 8 ^ s.length := by ring
      _ ≤ 8 * 8 ^ s.length := Nat.mul_le_mul_right _ a.isLt

private theorem radix_mono (s t : List (Fin 8)) (hl : s.length = t.length)
    (h : radix s ≤ radix t) : s ≤ t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all
  | cons a s ih =>
    cases t with
    | nil => simp at hl
    | cons b t =>
      have len : s.length = t.length := by simpa using hl
      change a.val * 8 ^ s.length + radix s ≤ b.val * 8 ^ t.length + radix t at h
      rw [len] at h
      rcases lt_trichotomy a b with hab|rfl|hba
      · exact (show a :: s < b :: t from List.Lex.rel hab).le
      · exact List.cons_le_cons _ (ih t len (by omega))
      · have hm := Nat.mul_le_mul_right (8 ^ t.length) (show b.val+1 ≤ a.val from hba)
        rw [Nat.add_mul, one_mul] at hm
        have hh := radix_bound t
        omega

set_option maxRecDepth 10000 in
private theorem score_radix (v : OQ) : score v = radix (pack8 v) := by
  simp [score, pack8, weight, Fin.sum_univ_succ, List.ofFn_succ, radix]
  ring

private theorem score_le {u v : OQ} (h : score u ≤ score v) : pack8 u ≤ pack8 v :=
  radix_mono _ _ (by simp [pack8]) (by simpa only [score_radix] using h)

private theorem transpose_cost (M : Fin 10 → OQ) :
    cost (fun i j => M j i) = cost M := by
  simp only [cost, score, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem swap_decreases (v : Fin 10 → Nat) (i k : Fin 10)
    (hik : i < k) (hv : v k < v i) :
    (∑ r, weight r * v (Equiv.swap i k r)) < ∑ r, weight r * v r := by
  classical
  let rest := (Finset.univ.erase i).erase k
  have split (f : Fin 10 → Nat) : ∑ r, f r = (∑ r ∈ rest, f r) + f k + f i := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hik.ne',Finset.mem_univ k⟩)]
  rw [split, split (fun r => weight r * v r)]
  have hs : (∑ r ∈ rest, weight r * v (Equiv.swap i k r)) =
      ∑ r ∈ rest, weight r * v r := by
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨hrk,hri⟩ := Finset.mem_erase.mp hr
    rw [Equiv.swap_apply_of_ne_of_ne (Finset.mem_erase.mp hri).1 hrk]
  rw [hs, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have wh : weight k < weight i := by
    have allPairs : ∀ a b : Fin 10, a < b → weight b < weight a := by decide
    exact allPairs i k hik
  have hh := mul_add_mul_lt_mul_add_mul wh hv
  omega

private def permute (D : Fin 10 → OQ) (σ π : Equiv.Perm (Fin 10)) : Fin 10 → OQ :=
  fun i j => D (σ i) (π j)

/-- Positive-index coordinate permutations keep the dephased row and column fixed.
The row phases below are indexed by original row number, as in gauge8. -/
theorem lex_normal (A : Fin 10 → OQ) :
    ∃ (σ π : Equiv.Perm (Fin 10)) (col row : OQ),
      let T := fun r => gauge8 π col (row (σ r)) (A (σ r))
      T 0 = (fun _ => 0) ∧ (∀ r, T r 0 = 0) ∧
      (List.ofFn (fun r => pack8 (T r))).Pairwise (· ≤ ·) ∧
      ∀ j : Fin 9, (List.ofFn (fun r => T r j.castSucc)) ≤ List.ofFn (fun r => T r j.succ) := by
  classical
  let row : OQ := fun r => -(A r 0) + A 0 0
  let D : Fin 10 → OQ := fun i j => row i + -(A 0 j) + A i j
  have zr (j) : D 0 j = 0 := by simp [D,row]
  have zc (i) : D i 0 = 0 := by dsimp [D,row]; abel
  let P (n : Nat) := ∃ σ π : Equiv.Perm (Fin 10), σ 0 = 0 ∧ π 0 = 0 ∧ cost (permute D σ π) = n
  have ex : ∃ n, P n := ⟨_, Equiv.refl _, Equiv.refl _, rfl,rfl,rfl⟩
  obtain ⟨σ,π,hσ,hπ,hmin⟩ := Nat.find_spec ex
  let T := permute D σ π
  have minimum (a b : Equiv.Perm (Fin 10)) (ha : a 0 = 0) (hb : b 0 = 0) :
      cost T ≤ cost (permute D a b) := by
    rw [show cost T = Nat.find ex from hmin]
    exact Nat.find_min' ex ⟨a,b,ha,hb,rfl⟩
  have tr (j) : T 0 j = 0 := by change D (σ 0) (π j) = 0; rw [hσ,zr]
  have tc (i) : T i 0 = 0 := by change D (σ i) (π 0) = 0; rw [hπ,zc]
  have rm (i k : Fin 10) (hik : i < k) : score (T i) ≤ score (T k) := by
    by_cases iz : i = 0
    · subst i; simp [score,tr]
    have kz : k ≠ 0 := by omega
    let g := Equiv.swap i k
    have gz : g 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm iz) (Ne.symm kz)
    have h := minimum (g.trans σ) π (by simp [gz,hσ]) hπ
    apply le_of_not_gt
    intro hn
    exact (not_lt_of_ge h) (swap_decreases (fun r => score (T r)) i k hik hn)
  have cm (i k : Fin 10) (hik : i < k) :
      score (fun r => T r i) ≤ score (fun r => T r k) := by
    by_cases iz : i = 0
    · subst i; simp [score,tc]
    have kz : k ≠ 0 := by omega
    let g := Equiv.swap i k
    have gz : g 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm iz) (Ne.symm kz)
    have h := minimum σ (g.trans π) hσ (by simp [gz,hπ])
    rw [← transpose_cost T, ← transpose_cost (permute D σ (g.trans π))] at h
    apply le_of_not_gt
    intro hn
    exact (not_lt_of_ge h) (swap_decreases (fun j => score (fun r => T r j)) i k hik hn)
  refine ⟨σ,π,(fun j => -(A 0 (π j))),row,funext tr,tc,?_,?_⟩
  · exact List.pairwise_ofFn.mpr fun _ _ hik => score_le (rm _ _ hik)
  · intro j
    exact score_le (cm j.castSucc j.succ (Fin.castSucc_lt_succ j))

#print axioms lex_normal

end MUB10Oct.Sixty
