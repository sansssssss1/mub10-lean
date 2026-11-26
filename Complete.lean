import ClassRadius
import Mathlib.Data.Finset.Card

namespace MUB10Radius
open MUB10 MUB10Robust
noncomputable section

/-- A complete family expressed in one of its bases: the other ten matrices have
unit-modulus raw entries; the raw squared Gram targets are 0, 10 and 100. -/
def CompleteFamily (F : Fin 10 → Fin 10 → V) : Prop :=
  (∀ p i, unitRow (F p i)) ∧
  ∀ p i q j, Complex.normSq (rowSum (F p i) (F q j)) =
    ((if p ≠ q then 10 else if i = j then 100 else 0 : ℤ) : ℝ)

def CloseToFourth (A : Fin 10 → V) : Prop :=
  ∃ (p : Fin 10 → Q) (δ : ℝ), δ < radius ∧ ∀ i, near (A i) (phaseOf (p i)) δ

def selectBases {α : Type*} (A B : Fin 10 → α) (i : Ix) : α :=
  if i.1 = 0 then A i.2 else B i.2

lemma selected_mub {F : Fin 10 → Fin 10 → V} (hf : CompleteFamily F) {p q : Fin 10} (hne : p ≠ q) :
    MUBPair (selectBases (F p) (F q)) := by
  constructor
  · intro ⟨a,i⟩
    fin_cases a <;> simp [selectBases, hf.1]
  · intro ⟨a,i⟩ ⟨b,j⟩
    fin_cases a <;> fin_cases b <;> simp [selectBases, target, hf.2, hne, hne.symm]

lemma common_bound {A B : Fin 10 → V} (ha : CloseToFourth A) (hb : CloseToFourth B) :
    ∃ (P : Ix → Q) (δ : ℝ), δ < radius ∧
      ∀ i, near (selectBases A B i) (phaseOf (P i)) δ := by
  obtain ⟨p,d,hd,hp⟩ := ha
  obtain ⟨q,e,he,hq⟩ := hb
  refine ⟨selectBases p q, max d e, max_lt hd he, ?_⟩
  intro ⟨a,i⟩ j
  fin_cases a
  · exact (hp i j).trans (le_max_left _ _)
  · exact (hq i j).trans (le_max_right _ _)

/-- The counting step applies to any phase-neighbourhood theorem for a pair.
The Fourier or quaternary classification is not asserted as an axiom here. -/
theorem at_most_one_of_exclusion
    (exclude : ∀ (X : Ix → V) (P : Ix → Q) (δ : ℝ),
      MUBPair X → δ < radius → (∀ i, near (X i) (phaseOf (P i)) δ) →
        ∀ z : V, unitRow z → ¬ ∀ i, Complex.normSq (rowSum (X i) z) = 10)
    (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) :
    Set.Subsingleton {p | CloseToFourth (F p)} := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨P,δ,hd,hP⟩ := common_bound hp hq
  have third : ∀ a b : Fin 10, ∃ k : Fin 10, a ≠ k ∧ b ≠ k := by decide
  obtain ⟨k,hpk,hqk⟩ := third p q
  apply exclude _ P δ (selected_mub hf hpq) hd hP (F k 0) (hf.1 k 0)
  intro ⟨a,i⟩
  fin_cases a <;> simp [selectBases, hf.2, hpk, hqk]

open Classical in
theorem nine_far_of_subsingleton (F : Fin 10 → Fin 10 → V)
    (h : Set.Subsingleton {p | CloseToFourth (F p)}) :
    9 ≤ (Finset.univ.filter (fun p => ¬ CloseToFourth (F p))).card := by
  classical
  have hcard : (Finset.univ.filter (fun p => CloseToFourth (F p))).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    exact h (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  rw [Finset.filter_not, Finset.card_sdiff (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega
end
end MUB10Radius
