import Catalogue
import Robust

namespace MUB10Radius
open MUB10 MUB10Robust MUB10Catalogue
open scoped BigOperators ComplexConjugate
noncomputable section
abbrev Q := Fin 10 → Fin 4
abbrev pack (s : Q) : Row := List.ofFn s

private lemma gaussian_fold (xs : List (ℤ × ℤ)) (u : ℤ × ℤ) :
    xs.foldl (fun v t : ℤ × ℤ => (v.1+t.1,v.2+t.2)) u =
      (u.1 + (xs.map Prod.fst).sum, u.2 + (xs.map Prod.snd).sum) := by
  induction xs generalizing u with
  | nil => simp
  | cons a xs ih => simp [ih, add_assoc]

private lemma zip_fn {n : Nat} (s t : Fin n → Fin 4) :
    List.zipWith (fun a b : Fin 4 => gaussianPhase (b-a).val) (List.ofFn s) (List.ofFn t) =
      List.ofFn (fun j => gaussianPhase (t j-s j).val) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.zipWith_cons_cons]; rw [ih]

theorem physical_gram (s t : Q) : Complex.normSq (rowSum (phaseOf s) (phaseOf t)) =
    (gramSq (pack s) (pack t) : ℝ) := by
  let v := fun j => gaussianPhase (t j - s j).val
  have eqn : rowSum (phaseOf s) (phaseOf t) =
      ((∑ j, (v j).1 : ℤ) : ℂ) + ((∑ j, (v j).2 : ℤ) : ℂ) * Complex.I := by
    simp only [rowSum, phaseOf, gaussian_term, Finset.sum_add_distrib]
    simp [v, Finset.sum_mul]
  have eqi : gramSq (pack s) (pack t) =
      (∑ j, (v j).1)*(∑ j, (v j).1) + (∑ j, (v j).2)*(∑ j, (v j).2) := by
    simp only [gramSq, pack, zip_fn, gaussian_fold, zero_add, List.map_ofFn, List.sum_ofFn]; rfl
  rw [eqn, eqi]
  generalize (∑ j, (v j).1) = a
  generalize (∑ j, (v j).2) = b
  simp [Complex.normSq_apply]

def target (a b : Fin 2 × Fin 10) : ℤ := if a.1 ≠ b.1 then 10 else if a.2 = b.2 then 100 else 0
abbrev Ix := Fin 2 × Fin 10

def MUBPair (X : Ix → V) : Prop :=
  (∀ a, unitRow (X a)) ∧ ∀ a b, Complex.normSq (rowSum (X a) (X b)) = (target a b : ℝ)

theorem rounded_pair (X : Ix → V) (P : Ix → Q) (hm : MUBPair X)
    {δ : ℝ} (hδ : δ < radius) (hc : ∀ a, near (X a) (phaseOf (P a)) δ) :
    ∀ a b, gramSq (pack (P a)) (pack (P b)) = target a b := by
  intro a b
  have small : δ < 1/400 := hδ.trans (by norm_num [radius])
  have hg := rounding_preserves_gram _ _ _ _ (hm.1 a) (hm.1 b) small (hc a) (hc b) _ (hm.2 a b)
  rw [physical_gram] at hg
  exact_mod_cast hg
end
end MUB10Radius
