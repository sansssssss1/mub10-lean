import ClassRadius

/-! Transport a nearby pair and an arbitrary test ray under the same
quaternary monomial coordinate change. -/

namespace MUB10Radius
open MUB10 MUB10Robust MUB10Catalogue
open scoped BigOperators ComplexConjugate
noncomputable section

def changeQ (π : Fin 10 ≃ Fin 10) (col : Q) (t : Fin 4) (p : Q) : Q :=
  fun j => t + col j + p (π j)

/-- The usual monomial equivalence classification of one quaternary matrix.
Reordering rows is expressed by a list permutation. -/
def SingleBHClassification : Prop :=
  ∀ A : Fin 10 → Q, (∀ r s, r ≠ s → gramSq (pack (A r)) (pack (A s)) = 0) →
    ∃ (c : Fin 10) (π : Fin 10 ≃ Fin 10) (col row : Q),
      (List.ofFn (fun r => pack (changeQ π col (row r) (A r)))).Perm (catalogue c)

private def u (t : Fin 4) : ℂ := Complex.I ^ t.val

private lemma u_add (s t : Fin 4) : u (s+t) = u s * u t := by
  fin_cases s <;> fin_cases t <;> norm_num [u, Fin.add_def, pow_succ, Complex.I_mul_I]

private lemma u_norm (t : Fin 4) : ‖u t‖ = 1 := by simp [u, Complex.norm_pow]

private lemma u_sq (t : Fin 4) : Complex.normSq (u t) = 1 := by
  simp [u, map_pow]

private def move (π : Fin 10 ≃ Fin 10) (col : Q) (t : Fin 4) (x : V) : V :=
  fun j => u t * u (col j) * x (π j)

private theorem phase_move (π : Fin 10 ≃ Fin 10) (col : Q) (t : Fin 4) (p : Q) :
    phaseOf (changeQ π col t p) = move π col t (phaseOf p) := by
  funext j
  change u (_ + _ + _) = _ * _ * u _
  rw [u_add, u_add]

private theorem move_unit (π : Fin 10 ≃ Fin 10) (col : Q) (t : Fin 4) (x : V)
    (hx : unitRow x) : unitRow (move π col t x) := by
  intro j
  simpa only [move, Complex.norm_mul, u_norm, one_mul] using hx (π j)

private theorem move_near (π : Fin 10 ≃ Fin 10) (col : Q) (t : Fin 4) (x y : V)
    {δ : ℝ} (h : near x y δ) : near (move π col t x) (move π col t y) δ := by
  intro j
  simpa only [move, ← mul_sub, Complex.norm_mul, u_norm, one_mul] using h (π j)

private theorem move_gram (π : Fin 10 ≃ Fin 10) (col : Q) (s t : Fin 4) (x y : V) :
    Complex.normSq (rowSum (move π col s x) (move π col t y)) =
    Complex.normSq (rowSum x y) := by
  have amp : rowSum (move π col s x) (move π col t y) = conj (u s) * u t * rowSum x y := by
    unfold rowSum
    rw [Finset.mul_sum]
    conv_rhs => rw [← Equiv.sum_comp π]
    apply Finset.sum_congr rfl
    intro j _
    simp only [move, map_mul]
    calc
      _ = (conj (u (col j)) * u (col j)) * (conj (u s) * u t * (conj (x (π j)) * y (π j))) := by ring
      _ = _ := by rw [← Complex.normSq_eq_conj_mul_self, u_sq]; simp
  rw [amp, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_conj, u_sq, u_sq]
  simp

theorem gramSq_changeQ (π : Equiv.Perm (Fin 10)) (col : Q) (s t : Fin 4) (x y : Q) :
    gramSq (pack (changeQ π col s x)) (pack (changeQ π col t y)) = gramSq (pack x) (pack y) := by
  have h := move_gram π col s t (phaseOf x) (phaseOf y)
  rw [← phase_move, ← phase_move, physical_gram, physical_gram] at h
  exact_mod_cast h

theorem changeQ_comp (π σ : Equiv.Perm (Fin 10)) (c d : Q) (s t : Fin 4) (p : Q) :
    changeQ σ d t (changeQ π c s p) =
    changeQ (σ.trans π) (fun j => d j + c (σ j)) (t+s) p := by
  funext j
  simp only [changeQ, Equiv.trans_apply]
  abel

/-- The radius obstruction for arbitrary input coordinates. Its sole
classification input concerns one exact quaternary Hadamard matrix. -/
theorem global_radius (classification : SingleBHClassification)
    (X : Ix → V) (P : Ix → Q) (hm : MUBPair X) {δ : ℝ} (hδ : δ < radius)
    (hc : ∀ a, near (X a) (phaseOf (P a)) δ) (z : V) (hz : unitRow z) :
    ¬ ∀ a, Complex.normSq (rowSum (X a) z) = 10 := by
  have rounded := rounded_pair X P hm hδ hc
  obtain ⟨c,π,col,ρ,hcata⟩ := classification (fun r => P (0,r))
    (fun r s h => by simpa [target,h] using rounded (0,r) (0,s))
  let b : Ix → Fin 4 := fun a =>
    if a.1 = 0 then ρ a.2 else -(col 0 + P a (π 0))
  let Y : Ix → V := fun a => move π col (b a) (X a)
  let T : Ix → Q := fun a => changeQ π col (b a) (P a)
  have hY : MUBPair Y := ⟨fun a => move_unit π col (b a) _ (hm.1 a),
    fun a d => (move_gram π col (b a) (b d) _ _).trans (hm.2 a d)⟩
  have first : (List.ofFn (fun r => pack (T (0,r)))).Perm (catalogue c) := by
    simpa only [T,b,if_pos rfl] using hcata
  have second : ∀ r, T (1,r) 0 = 0 := by
    intro r
    change (if (1 : Fin 2) = 0 then ρ r else -(_ + _)) + _ + _ = 0
    simp [add_assoc]
  have close : ∀ a, near (Y a) (phaseOf (T a)) δ := by
    intro a
    rw [show T a = changeQ π col (b a) (P a) by rfl, phase_move]
    exact move_near π col (b a) _ _ (hc a)
  apply fun hall => canonical_radius Y T c hY first second hδ close (move π col 0 z)
    (move_unit π col 0 z hz) (fun a => (move_gram π col (b a) 0 _ _).trans (hall a))

#print axioms global_radius
end
end MUB10Radius
