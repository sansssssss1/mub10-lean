import Gauge

/-! A finite integer invariant distinguishing the ten quaternary monomial
equivalence classes, including independent row and column permutations. -/

namespace MUB10Radius
open MUB10Catalogue
open scoped BigOperators

abbrev M10 := Fin 10 → Q

def quadDiff (A : M10) (a b k j : Fin 10) : Fin 4 :=
  A b j - A a j - A b k + A a k

private def blockScore (A : M10) (a b c d k : Fin 10) : Nat :=
  (∑ j : Fin 10, ((quadDiff A a b k j).val + (quadDiff A a c k j).val +
      (quadDiff A a d k j).val)^2) % 7

def classScore (A : M10) : Nat :=
  ∑ a : Fin 10, ∑ b : Fin 10, ∑ c : Fin 10, ∑ d : Fin 10, ∑ k : Fin 10, blockScore A a b c d k

def remap (A : M10) (ρ π : Equiv.Perm (Fin 10)) (col row : Q) : M10 :=
  fun r => changeQ π col (row r) (A (ρ r))

private theorem diff_remap (A : M10) (ρ π : Equiv.Perm (Fin 10)) (col row : Q)
    (a b j k : Fin 10) : quadDiff (remap A ρ π col row) a b k j =
    quadDiff A (ρ a) (ρ b) (π k) (π j) := by
  unfold quadDiff remap changeQ
  abel

private theorem block_remap (A : M10) (ρ π : Equiv.Perm (Fin 10)) (col row : Q)
    (a b c d k : Fin 10) : blockScore (remap A ρ π col row) a b c d k =
    blockScore A (ρ a) (ρ b) (ρ c) (ρ d) (π k) := by
  unfold blockScore
  simp only [diff_remap]
  exact congrArg (· % 7) (Equiv.sum_comp π (fun j =>
    ((quadDiff A (ρ a) (ρ b) (π k) j).val + (quadDiff A (ρ a) (ρ c) (π k) j).val +
      (quadDiff A (ρ a) (ρ d) (π k) j).val)^2))

theorem classScore_remap (A : M10) (ρ π : Equiv.Perm (Fin 10)) (col row : Q) :
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

def catalogueMatrix (i : Fin 10) : M10 := fun r j => ((catalogue i).getD r.val []).getD j.val 0

def scoreList := [268516,277284,317700,268180,279300,306788,303050,301412,299060,300740]

set_option maxRecDepth 100000 in
theorem catalogue_scores : (List.ofFn fun i => classScore (catalogueMatrix i)) = scoreList := by
  native_decide

/-- Distinct representatives cannot be connected by quaternary row or column
phases and permutations. -/
theorem catalogue_inequivalent (i j : Fin 10) (ρ π : Equiv.Perm (Fin 10)) (col row : Q)
    (eqn : remap (catalogueMatrix i) ρ π col row = catalogueMatrix j) : i = j := by
  have hj : classScore (catalogueMatrix i) = classScore (catalogueMatrix j) := by
    rw [← eqn, classScore_remap]
  apply (List.nodup_ofFn.mp (show (List.ofFn fun k => classScore (catalogueMatrix k)).Nodup by
    rw [catalogue_scores]; decide))
  exact hj

#print axioms catalogue_inequivalent
end MUB10Radius
