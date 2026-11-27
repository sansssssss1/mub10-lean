import OctSixtyData

/-! A finite integer invariant distinguishing the sixty octonary monomial
equivalence classes, including independent row and column permutations. -/

namespace MUB10Oct.Sixty

open scoped BigOperators

abbrev M10 := Fin 10 → OQ

def quadDiff (A : M10) (a b k j : Fin 10) : O :=
  A b j - A a j - A b k + A a k

private def blockScore (A : M10) (a b c d k : Fin 10) : Nat :=
  (∑ j : Fin 10, ((quadDiff A a b k j).val + (quadDiff A a c k j).val +
      (quadDiff A a d k j).val)^2) % 19

def classScore (A : M10) : Nat :=
  ∑ a : Fin 10, ∑ b : Fin 10, ∑ c : Fin 10, ∑ d : Fin 10, ∑ k : Fin 10, blockScore A a b c d k

def remap (A : M10) (ρ π : Equiv.Perm (Fin 10)) (col row : OQ) : M10 :=
  fun r j => row r + col j + A (ρ r) (π j)

private theorem diff_remap (A : M10) (ρ π : Equiv.Perm (Fin 10)) (col row : OQ)
    (a b j k : Fin 10) : quadDiff (remap A ρ π col row) a b k j =
    quadDiff A (ρ a) (ρ b) (π k) (π j) := by
  unfold quadDiff remap
  abel

private theorem block_remap (A : M10) (ρ π : Equiv.Perm (Fin 10)) (col row : OQ)
    (a b c d k : Fin 10) : blockScore (remap A ρ π col row) a b c d k =
    blockScore A (ρ a) (ρ b) (ρ c) (ρ d) (π k) := by
  unfold blockScore
  simp only [diff_remap]
  exact congrArg (· % 19) (Equiv.sum_comp π (fun j =>
    ((quadDiff A (ρ a) (ρ b) (π k) j).val + (quadDiff A (ρ a) (ρ c) (π k) j).val +
      (quadDiff A (ρ a) (ρ d) (π k) j).val)^2))

theorem classScore_remap (A : M10) (ρ π : Equiv.Perm (Fin 10)) (col row : OQ) :
    classScore (remap A ρ π col row) = classScore A := by
  unfold classScore
  simp only [block_remap]
  rw [← Equiv.sum_comp ρ (fun a => ∑ b, ∑ c, ∑ d, ∑ k, blockScore A a b c d k)]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp ρ (fun b => ∑ c, ∑ d, ∑ k, blockScore A (ρ a) b c d k)]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Equiv.sum_comp ρ (fun c => ∑ d, ∑ k, blockScore A (ρ a) (ρ b) c d k)]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Equiv.sum_comp ρ (fun d => ∑ k, blockScore A (ρ a) (ρ b) (ρ c) d k)]
  apply Finset.sum_congr rfl
  intro d _
  exact Equiv.sum_comp π (fun k => blockScore A (ρ a) (ρ b) (ρ c) (ρ d) k)

def catalogueMatrix (i : Fin 60) : M10 := fun r j => ((catalogue8 i).getD r.val []).getD j.val 0

def scoreList := [856068,869508,864388,867012,885220,860844,870044,865172,823500,875332,894356,887088,885264,887684,880788,896412,898898,893571,902288,892536,894384,896892,888912,894612,909060,883644,831990,822300,822756,817740,825492,901240,902136,901764,886104,907876,895252,858916,888100,889196,880704,887544,892644,889116,899484,917070,952564,905436,921196,906604,927195,899550,894420,949332,907746,916310,924290,909470,933660,926250]

set_option maxRecDepth 100000 in
theorem catalogue_scores : (List.ofFn fun i => classScore (catalogueMatrix i)) = scoreList := by
  native_decide

/-- Distinct representatives cannot be connected by octonary row or column
phases and permutations. -/
theorem catalogue_inequivalent (i j : Fin 60) (ρ π : Equiv.Perm (Fin 10)) (col row : OQ)
    (eqn : remap (catalogueMatrix i) ρ π col row = catalogueMatrix j) : i = j := by
  have hj : classScore (catalogueMatrix i) = classScore (catalogueMatrix j) := by
    rw [← eqn, classScore_remap]
  apply (List.nodup_ofFn.mp (show (List.ofFn fun k => classScore (catalogueMatrix k)).Nodup by
    rw [catalogue_scores]; decide))
  exact hj

#print axioms catalogue_inequivalent
end MUB10Oct.Sixty
