import OctSixtyData
import OctGlobalCore

/-! Exact evaluation of octonary overlaps in the basis (1,i,ζ₈,iζ₈). -/
open scoped BigOperators ComplexConjugate
namespace MUB10Oct.Sixty
open MUB10 MUB10Robust MUB10Radius MUB10Catalogue
noncomputable section

private def w (e t : O) : Int :=
  (if e=t then 1 else 0) - (if e=t+4 then 1 else 0)

private def c (h r : OQ) (t : O) : Int := ∑ j, w (r j-h j) t

private theorem zipped {n : Nat} {α β γ : Type} (f : α → β → γ) (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun j => f (a j) (b j)) := by
  induction n with
  | zero => simp
  | succ n ih => simpa [List.ofFn_succ] using congrArg (List.cons (f (a 0) (b 0))) (ih (fun j => a j.succ) (fun j => b j.succ))

private def encode (a b u v : Int) : Int := a + b*32 + u*1024 + v*32768
private def eval (a b u v : Int) : ℂ :=
  (a:ℂ) + (b:ℂ)*Complex.I + zeta8*((u:ℂ)+(v:ℂ)*Complex.I)

private theorem score_expansion (h r : OQ) :
    score (List.ofFn h) (List.ofFn r) = encode (c h r 0) (c h r 2) (c h r 1) (c h r 3) := by
  have hw : ∀ e : O, valCode e=encode (w e 0) (w e 2) (w e 1) (w e 3) := by decide
  simp only [score,zipped,List.sum_ofFn,hw,encode,c,Finset.sum_add_distrib,Finset.sum_mul]

private theorem gram_expansion (h r : OQ) :
    rowSum (phase8 h) (phase8 r) = eval (c h r 0) (c h r 2) (c h r 1) (c h r 3) := by
  have hv (e : O) : val8 e=eval (w e 0) (w e 2) (w e 1) (w e 3) := by
    rw [val8_split]
    fin_cases e
    · change Complex.I ^ 0 * 1 = eval (1:Int) (0:Int) (0:Int) (0:Int)
      norm_num [eval,pow_succ,Complex.I_mul_I]
    · change Complex.I ^ 0 * zeta8 = eval (0:Int) (0:Int) (1:Int) (0:Int)
      norm_num [eval,pow_succ,Complex.I_mul_I]
    · change Complex.I ^ 1 * 1 = eval (0:Int) (1:Int) (0:Int) (0:Int)
      norm_num [eval,pow_succ,Complex.I_mul_I]
    · change Complex.I ^ 1 * zeta8 = eval (0:Int) (0:Int) (0:Int) (1:Int)
      norm_num [eval,pow_succ,Complex.I_mul_I]; ring
    · change Complex.I ^ 2 * 1 = eval (-1:Int) (0:Int) (0:Int) (0:Int)
      norm_num [eval,pow_succ,Complex.I_mul_I]
    · change Complex.I ^ 2 * zeta8 = eval (0:Int) (0:Int) (-1:Int) (0:Int)
      norm_num [eval,pow_succ,Complex.I_mul_I]
    · change Complex.I ^ 3 * 1 = eval (0:Int) (-1:Int) (0:Int) (0:Int)
      norm_num [eval,pow_succ,Complex.I_mul_I]
    · change Complex.I ^ 3 * zeta8 = eval (0:Int) (0:Int) (0:Int) (-1:Int)
      norm_num [eval,pow_succ,Complex.I_mul_I]; ring
  calc
    _ = ∑ j, val8 (r j-h j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [phase8,val8_sub,mul_comm]
    _ = _ := by simp only [hv,eval,c,Int.cast_sum,mul_add,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]

private theorem bounds (h r : OQ) (t : O) : -10 ≤ c h r t ∧ c h r t ≤ 10 := by
  have hw : ∀ (e t : O), -1 ≤ w e t ∧ w e t ≤ 1 := by decide
  constructor
  · calc
      (-10:Int) = ∑ _j : Fin 10, (-1:Int) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => (hw (r j-h j) t).1
  · calc
      _ ≤ ∑ _j : Fin 10, (1:Int) := Finset.sum_le_sum fun j _ => (hw (r j-h j) t).2
      _ = _ := by simp

private theorem separate (a b n : ℤ)
    (h : (a:ℝ) + (b:ℝ)*Real.sqrt 2 = n) : a = n ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    exact ⟨by exact_mod_cast (by simpa using h : (a:ℝ) = n),rfl⟩
  exfalso
  apply ((irrational_iff_ne_rational (Real.sqrt 2)).mp irrational_sqrt_two) (n-a) b
  apply (eq_div_iff (by exact_mod_cast hb : (b:ℝ) ≠ 0)).mpr
  push_cast
  linarith

private theorem eval_norm (a b u v : Int) :
    (((a*a+b*b+u*u+v*v:Int):ℝ) + ((a*(u-v)+b*(u+v):Int):ℝ)*Real.sqrt 2) =
      Complex.normSq (eval a b u v) := by
  simp [eval,zeta8,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring_nf
  simp [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

private theorem separate_norm (a b u v n : Int) (h : Complex.normSq (eval a b u v) = n) :
    a*a+b*b+u*u+v*v=n ∧ a*(u-v)+b*(u+v)=0 :=
  separate _ _ _ ((eval_norm a b u v).trans h)

private def signed (t : Fin 21) : Int := (t.val:Int)-10

private theorem box (a : Int) (h : -10 ≤ a ∧ a ≤ 10) :
    ∃ i : Fin 21, signed i = a := by
  refine ⟨⟨(a+10).toNat,by omega⟩,?_⟩
  unfold signed
  simp only
  omega

private theorem small_norm_certificate : ∀ i j k l : Fin 21,
    let a := signed i; let b := signed j; let u := signed k; let v := signed l
    a*a+b*b+u*u+v*v=10 → a*(u-v)+b*(u+v)=0 → encode a b u v ∈ targets := by native_decide

theorem score_of_unbiased (h r : OQ) (hx : Complex.normSq (rowSum (phase8 h) (phase8 r))=10) :
    score (List.ofFn h) (List.ofFn r) ∈ targets := by
  rw [gram_expansion] at hx
  have hp := separate_norm _ _ _ _ 10 (by simpa using hx)
  obtain ⟨i,hi⟩ := box _ (bounds h r 0)
  obtain ⟨j,hj⟩ := box _ (bounds h r 2)
  obtain ⟨k,hk⟩ := box _ (bounds h r 1)
  obtain ⟨l,hl⟩ := box _ (bounds h r 3)
  rw [score_expansion]
  have hlm := small_norm_certificate i j k l
  simp only [hi,hj,hk,hl] at hlm
  exact hlm hp.1 hp.2

private theorem converse_certificate : ∀ i j k l : Fin 21,
    let a := signed i; let b := signed j; let u := signed k; let v := signed l
    encode a b u v ∈ targets → a*a+b*b+u*u+v*v=10 ∧ a*(u-v)+b*(u+v)=0 := by native_decide

theorem score_unbiased_iff (h r : OQ) :
    score (List.ofFn h) (List.ofFn r) ∈ targets ↔ Complex.normSq (rowSum (phase8 h) (phase8 r))=10 := by
  refine ⟨?_,score_of_unbiased h r⟩
  rw [score_expansion,gram_expansion,← eval_norm]
  intro hmem
  obtain ⟨i,hi⟩ := box _ (bounds h r 0)
  obtain ⟨j,hj⟩ := box _ (bounds h r 2)
  obtain ⟨k,hk⟩ := box _ (bounds h r 1)
  obtain ⟨l,hl⟩ := box _ (bounds h r 3)
  have cert := converse_certificate i j k l
  simp only [hi,hj,hk,hl] at cert
  have hp := cert hmem
  simp [hp.1,hp.2]

theorem score_zero_iff (h r : OQ) : score (List.ofFn h) (List.ofFn r)=0 ↔ rowSum (phase8 h) (phase8 r)=0 := by
  rw [score_expansion,gram_expansion]
  let a := c h r 0
  let b := c h r 2
  let u := c h r 1
  let v := c h r 3
  change encode a b u v=0 ↔ eval a b u v=0
  have ha : -10 ≤ a ∧ a ≤ 10 := bounds _ _ _
  have hb : -10 ≤ b ∧ b ≤ 10 := bounds _ _ _
  have hu : -10 ≤ u ∧ u ≤ 10 := bounds _ _ _
  have hv : -10 ≤ v ∧ v ≤ 10 := bounds _ _ _
  constructor
  · intro raw
    unfold encode at raw
    have az : a=0 := by omega
    have bz : b=0 := by omega
    have uz : u=0 := by omega
    have vz : v=0 := by omega
    simp [eval,az,bz,uz,vz]
  · intro hx
    have hs := (separate_norm a b u v 0 (by simp [hx])).1
    have az : a=0 := by nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg u,sq_nonneg v]
    have bz : b=0 := by nlinarith [sq_nonneg b,sq_nonneg u,sq_nonneg v]
    have uz : u=0 := by nlinarith [sq_nonneg u,sq_nonneg v]
    have vz : v=0 := by nlinarith [sq_nonneg v]
    simp [encode,az,bz,uz,vz]

end
end MUB10Oct.Sixty
