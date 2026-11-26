import RoundedGram
import ClassObstruction
import Mathlib.Data.List.FinRange

namespace MUB10Radius
open MUB10 MUB10Robust MUB10Catalogue
noncomputable section

private lemma from_pack (p : Q) :
    MUB10Catalogue.normalized (pack p) = MUB10Robust.normalized (phaseOf p) := by
  funext j
  fin_cases j <;> rfl

/-- Entrywise chordal neighbourhood of the fourth roots. Only the first rounded
matrix is put in catalogue coordinates. The second matrix is arbitrary and its
orthogonality after rounding is derived. Rows in the second group are dephased. -/
theorem canonical_radius (X : Ix → V) (P : Ix → Q) (c : Fin 10) (hm : MUBPair X)
    (first : (List.ofFn (fun j => pack (P (0,j)))).Perm (catalogue c))
    (second : ∀ j, P (1,j) 0 = 0) {δ : ℝ} (hδ : δ < radius)
    (hc : ∀ a, near (X a) (phaseOf (P a)) δ) (z : V) (hz : unitRow z) :
    ¬ ∀ a, Complex.normSq (rowSum (X a) z) = 10 := by
  let B := List.ofFn fun j : Fin 10 => pack (P (1,j))
  have hg := rounded_pair X P hm hδ hc
  have hd : B.Nodup := by
    apply List.nodup_ofFn_ofInjective
    intro j k he
    change pack (P (1,j)) = pack (P (1,k)) at he
    by_contra hne
    have h1 := hg (1,j) (1,k)
    have h2 := hg (1,k) (1,k)
    rw [he] at h1
    simp [target, hne] at h1 h2
    omega
  have sh : ∀ r ∈ B, ∃ tail : Row, r = 0 :: tail ∧ tail.length = 9 := by
    intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨_, by rw [pack, List.ofFn_succ, second], List.length_ofFn⟩
  have cross : ∀ r ∈ B, ∀ a ∈ catalogue c, gramSq a r = 10 := by
    intro r hr a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (first.mem_iff.mpr ha)
    simpa [target] using hg (0,k) (1,j)
  have orthB : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → gramSq a b = 0 := by
    intro a ha b hb hn
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
    have hj : j ≠ k := fun h => hn (congrArg (fun m => pack (P (1,m))) h)
    simpa [target, hj] using hg (1,j) (1,k)
  have flat : ∀ j, Complex.normSq (MUB10Robust.normalized z j) = 1/10 := by
    intro j
    simp [MUB10Robust.normalized, Complex.normSq_div, ← Complex.sq_norm (z j), hz j]
  obtain ⟨r,hr,hdiff⟩ := catalogue_probability_gap c B List.length_ofFn hd sh cross orthB _ flat
  apply transfer_gap X (fun a => phaseOf (P a)) z hm.1 (fun a => phase_unit _) hz hδ hc
  obtain left | right := List.mem_append.mp hr
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (first.mem_iff.mpr left)
    exact ⟨(0,j), by rwa [from_pack] at hdiff⟩
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp right
    exact ⟨(1,j), by rwa [from_pack] at hdiff⟩

#print axioms canonical_radius
end
end MUB10Radius
