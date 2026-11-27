import OctSixtyGauge

/-! Physical consequences of classifying a single octonary Hadamard and scanning its mates.
The single-matrix coverage hypothesis is explicit. -/
open scoped ComplexConjugate
namespace MUB10Oct.Sixty
open MUB10 MUB10Robust MUB10Radius MUB10Catalogue
noncomputable section

def SingleOctClassification : Prop := ∀ A : Fin 10 → OQ,
  (∀ r s, r≠s → score (pack8 (A r)) (pack8 (A s))=0) →
  ∃ (c : Fin 60) (π : Equiv.Perm (Fin 10)) (col ρ : OQ),
    (List.ofFn fun r => pack8 (gauge8 π col (ρ r) (A r))).Perm (catalogue8 c)

def SixtyMates : Prop := ∀ (i : Fin 60) (B : OBasis), B.length=10 → B.Nodup →
  (∀ r∈B, ∃ t, r=0::t ∧ t.length=9) →
  (∀ r∈B, ∀ h∈catalogue8 i, score h r ∈ targets) →
  (∀ r∈B, ∀ s∈B, r≠s → score r s=0) →
  (i=8 ∨ i=27) ∧ (∀ h∈catalogue8 i, ∀ x∈h, bit x=false) ∧ ∀ r∈B, ∀ x∈r, bit x=false

/-- A common rephasing of the coordinates and a separate rephasing of each ray
simultaneously turn both eighth-root bases into fourth-root bases. -/
theorem pair_gauge_even (hc : SingleOctClassification) (hmates : SixtyMates)
    (P : Ix → OQ) (hm : MUBPair (fun a => phase8 (P a))) :
    ∃ (π : Equiv.Perm (Fin 10)) (col : OQ) (s : Ix → O), ∀ a j, bit (gauge8 π col (s a) (P a) j)=false := by
  let A (r : Fin 10) := P (0,r)
  let B (r : Fin 10) := P (1,r)
  have hA (r s : Fin 10) (hne : r≠s) : score (pack8 (A r)) (pack8 (A s))=0 := by
    apply (score_zero_iff _ _).mpr
    apply Complex.normSq_eq_zero.mp
    simpa [A,target,hne] using hm.2 (0,r) (0,s)
  obtain ⟨i,π,col,ρ,first⟩ := hc A hA
  let H (r : Fin 10) := gauge8 π col (ρ r) (A r)
  let κ (r : Fin 10) := -(col 0 + B r (π 0))
  let T (r : Fin 10) := gauge8 π col (κ r) (B r)
  have cross (r s : Fin 10) : Complex.normSq (rowSum (phase8 (H r)) (phase8 (T s)))=10 := by
    unfold H T
    rw [phase_gauge,phase_gauge,changeProb _ _ _ _ (val8_normSq _) (val8_normSq _)]
    simpa [A,B,target] using hm.2 (0,r) (1,s)
  have gram (r s : Fin 10) : Complex.normSq (rowSum (phase8 (T r)) (phase8 (T s))) = if r=s then 100 else 0 := by
    unfold T
    rw [phase_gauge,phase_gauge,changeProb _ _ _ _ (val8_normSq _) (val8_normSq _)]
    simpa [B,target] using hm.2 (1,r) (1,s)
  let L := List.ofFn fun r : Fin 10 => List.ofFn (T r)
  have hn : L.Nodup := by
    apply List.nodup_ofFn_ofInjective
    intro r s hrs
    have ht : T r=T s := List.ofFn_inj.mp hrs
    by_cases he : r=s
    · exact he
    · have h0 : Complex.normSq (rowSum (phase8 (T s)) (phase8 (T s)))=0 := by
        simpa only [ht,if_neg he] using gram r s
      have h100 : Complex.normSq (rowSum (phase8 (T s)) (phase8 (T s)))=100 := by simpa using gram s s
      linarith
  have shape : ∀ r∈L, ∃ tail, r=0::tail ∧ tail.length=9 := by
    intro r hr
    obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hr
    refine ⟨List.ofFn (fun j : Fin 9 => T s j.succ),?_,List.length_ofFn⟩
    rw [List.ofFn_succ]
    simp only [T,gauge8,κ,neg_add_rev,add_assoc,neg_add_cancel_left,neg_add_cancel,zero_add]
  have checks : ∀ r∈L, ∀ h∈catalogue8 i, score h r ∈ targets := by
    intro r hr h hh
    obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (first.mem_iff.mpr hh)
    exact score_of_unbiased (H k) (T s) (cross k s)
  have orths : ∀ r∈L, ∀ s∈L, r≠s → score r s=0 := by
    intro r hr s hs hne
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hs
    have hkl : k≠l := fun h => hne (congrArg (fun q => List.ofFn (T q)) h)
    apply (score_zero_iff _ _).mpr
    apply Complex.normSq_eq_zero.mp
    simpa [hkl] using gram k l
  have ev := (hmates i L List.length_ofFn hn shape checks orths).2
  refine ⟨π,col,selectBases ρ κ,?_⟩
  rintro ⟨g,r⟩ j
  fin_cases g
  · apply ev.1 _ (first.mem_iff.mp (List.mem_ofFn.mpr ⟨r,rfl⟩))
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · apply ev.2 _ (List.mem_ofFn.mpr ⟨r,rfl⟩)
    exact List.mem_ofFn.mpr ⟨j,rfl⟩

def RelativeOct (x : V) : Prop := ∀ j, ∃ k : O, x j=x 0*val8 k

theorem relative_oct_exclusion (hc : SingleOctClassification) (hmates : SixtyMates)
    (X : Ix → V) (hm : MUBPair X) (hx : ∀ a, RelativeOct (X a)) (v : V)
    (flat : ∀ j, Complex.normSq (v j)=1/10) :
    ¬ ∀ a, Complex.normSq (rowSum (MUB10Robust.normalized (X a)) v)=1/10 := by
  choose P hP using (show ∀ a j, ∃ k:O, X a j=X a 0*val8 k from hx)
  let rowFactor (a : Ix) := X a 0
  have hu (a : Ix) : Complex.normSq (rowFactor a)=1 := by
    rw [← Complex.sq_norm]
    change ‖X a 0‖^2=1
    rw [hm.1]; norm_num
  have rep (a : Ix) : X a=multiplyRow (rowFactor a) (phase8 (P a)) := funext (hP a)
  have hp := remove_phases_pair _ _ _ hu rep hm
  obtain ⟨π,col,s,ev⟩ := pair_gauge_even hc hmates P hp
  let C (a : Ix) : Q := fun j => digit (gauge8 π col (s a) (P a) j)
  let α (a : Ix) : ℂ := val8 (s a)*conj (rowFactor a)
  have hα (a : Ix) : Complex.normSq (α a)=1 := by simp [α,Complex.normSq_mul,val8_normSq,hu]
  have eqC (a : Ix) : phaseOf (C a)=move8 π col (α a) (X a) := by
    rw [show phaseOf (C a)=phase8 (gauge8 π col (s a) (P a)) from (phase8_even _ (ev a)).symm,phase_gauge,rep]
    funext j
    unfold move8 multiplyRow α
    calc
      _ = (conj (rowFactor a) * rowFactor a) * (val8 (s a)*val8 (col j)*phase8 (P a) (π j)) := by
        rw [← Complex.normSq_eq_conj_mul_self,hu]; simp
      _ = _ := by ring
  have hC : MUBPair (fun a => phaseOf (C a)) := by
    constructor
    · intro a j
      change ‖Complex.I ^ (C a j).val‖=1
      rw [Complex.norm_pow,Complex.norm_I,one_pow]
    · intro a b
      simpa only [eqC,changeProb _ _ _ _ (hα a) (hα b)] using hm.2 a b
  let v' := move8 π col 1 v
  have hf (j : Fin 10) : Complex.normSq (v' j)=1/10 := by
    simp [v',move8,Complex.normSq_mul,val8_normSq,flat]
  intro hv
  apply quaternary_strongly_unextendible C hC v' hf
  intro a
  have hN : MUB10Robust.normalized (phaseOf (C a))=move8 π col (α a) (MUB10Robust.normalized (X a)) := by
    rw [eqC]
    funext j
    simp [MUB10Robust.normalized,move8,mul_div_assoc]
  rw [hN,show v'=move8 π col 1 v by rfl,changeProb _ _ _ _ (hα a) (by simp)]
  exact hv a

/-- Among the ten bases besides the fixed coordinate basis of a complete family,
at most one can have eighth-root ratios within each of its rays. -/
theorem complete_other_nine (hc : SingleOctClassification) (hscan : SixtyMates)
    (F : Fin 10 → Fin 10 → V) (hf : CompleteFamily F) (p : Fin 10)
    (hp : ∀ r, RelativeOct (F p r)) (q : Fin 10) (hq : q≠p) :
    ∃ r j, ∀ k : O, F q r j≠F q r 0*val8 k := by
  classical
  by_contra! hh
  have third : ∀ a b : Fin 10, ∃ k : Fin 10, a≠k ∧ b≠k := by decide
  obtain ⟨k,hpk,hqk⟩ := third p q
  have hu (j : Fin 10) : Complex.normSq (MUB10Robust.normalized (F k 0) j) = 1/10 := by
    simp [MUB10Robust.normalized,Complex.normSq_div,← Complex.sq_norm (F k 0 j),hf.1 k 0 j]
  refine relative_oct_exclusion hc hscan _ (selected_mub hf (Ne.symm hq)) ?_ (MUB10Robust.normalized (F k 0)) hu ?_
  · rintro ⟨g,r⟩
    fin_cases g
    · exact hp r
    · exact hh r
  · rintro ⟨g,r⟩
    rw [normalized_probability]
    fin_cases g <;> norm_num [selectBases,hf.2,hpk,hqk]

end
end MUB10Oct.Sixty
