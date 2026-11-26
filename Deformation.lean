import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-! The clock and skew-conjugation construction of Sun, specialized to dimension ten.
The four independent phases of the deformed Fourier basis are arbitrary.  All
probabilities below use normalized complex vectors in five two-dimensional blocks. -/

open scoped BigOperators ComplexConjugate
open Finset

namespace MUB10.Deformation
noncomputable section

abbrev Index := Fin 5
abbrev Block := ℂ × ℂ
abbrev Vec := Index → Block
abbrev UnitPhase := {x : ℂ // Complex.normSq x = 1}
abbrev Phases := Index → UnitPhase

def dot (u v : Block) : ℂ := conj u.1 * v.1 + conj u.2 * v.2
def overlap (u v : Vec) : ℂ := ∑ j, dot (u j) (v j)
def Flat (v : Vec) : Prop :=
  ∀ j, Complex.normSq (v j).1 = 1/10 ∧ Complex.normSq (v j).2 = 1/10

def scale (c : ℂ) (v : Block) : Block := (c * v.1, c * v.2)
def skew (η : UnitPhase) (v : Block) : Block :=
  (conj (η : ℂ) * conj v.2, -(conj (η : ℂ) * conj v.1))
/-- cos(2π/5) and the primitive fifth root in the upper half plane. -/
def reRoot : ℝ := (Real.sqrt 5 - 1)/4
def omega : ℂ := ⟨reRoot, Real.sqrt (1 - reRoot^2)⟩
def char (k j : Index) : ℂ := omega ^ ((k*j).val)
def clock (k : Index) (v : Vec) : Vec := fun j => scale (char k j) (v j)
def J (η : Phases) (v : Vec) : Vec := fun j => skew (η j) (v j)
def amplitude : ℂ := ((1 / Real.sqrt 10 : ℝ) : ℂ)
def first (η : Phases) (b : Bool) : Vec :=
  fun j => if b then (amplitude * conj (η j : ℂ), -(amplitude * conj (η j : ℂ)))
      else (amplitude, amplitude)
def anchor (η : Phases) (r : Index) (b : Bool) : Vec := clock r (first η b)
def companion (η : Phases) (g : Vec) (r : Index) (b : Bool) : Vec :=
  clock r (if b then J η g else g)

private lemma root_re_poly : 4*reRoot^2+2*reRoot-1 = 0 := by
  unfold reRoot
  have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  nlinarith

private lemma root_im_sq : (Real.sqrt (1-reRoot^2))^2 = 1-reRoot^2 := by
  apply Real.sq_sqrt
  have h := root_re_poly
  have hs : 0 ≤ reRoot := by
    unfold reRoot
    have hr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    have hp := Real.sqrt_nonneg (5:ℝ)
    nlinarith
  nlinarith

private lemma omega_unit : Complex.normSq omega = 1 := by
  simp only [omega, Complex.normSq_apply]
  nlinarith [root_im_sq]

private lemma root_quadratic : omega^2 - (2*↑reRoot)*omega + 1 = 0 := by
  apply Complex.ext <;> simp [omega, pow_two, Complex.mul_re, Complex.mul_im]
  · have h := root_im_sq
    simp only [pow_two] at h
    nlinarith
  · ring

private lemma omega_sum : omega^4+omega^3+omega^2+omega+1=0 := by
  have h : 4*(reRoot:ℂ)^2+2*(reRoot:ℂ)-1=0 := by exact_mod_cast root_re_poly
  calc
    _ = (omega^2+(1+2*(reRoot:ℂ))*omega+1) *
      (omega^2-2*(reRoot:ℂ)*omega+1) +
      omega^2 * (4*(reRoot:ℂ)^2+2*(reRoot:ℂ)-1) := by ring
    _ = 0 := by rw [root_quadratic,h]; ring

private lemma omega_five : omega^5=1 := by
  calc
    _ = 1+(omega-1)*(omega^4+omega^3+omega^2+omega+1) := by ring
    _ = 1 := by rw [omega_sum]; ring

private lemma base_add (u v : Index) : omega^(u+v).val = omega^u.val * omega^v.val := by
  rw [Fin.val_add, ← pow_eq_pow_mod _ omega_five, pow_add]

private lemma char_add (r s j : Index) : char (r+s) j = char r j * char s j := by
  simp only [char, add_mul, base_add]

private lemma unit_char (k j : Index) : Complex.normSq (char k j) = 1 := by
  simp [char, map_pow, omega_unit]

private lemma char_conj (k j : Index) : conj (char k j) = char (-k) j := by
  have h : char k j * char (-k) j = 1 := by rw [← char_add]; simp [char]
  have u := Complex.mul_conj (char k j)
  rw [unit_char, Complex.ofReal_one] at u
  exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h) (u.trans h.symm)

private lemma sum_char (k : Index) : ∑ j, char k j = if k = 0 then 5 else 0 := by
  fin_cases k <;> norm_num [Fin.sum_univ_succ, char, Fin.val_mul, Fin.val_add] <;>
    (convert omega_sum using 1; ring)

private lemma char_mod (r s j : Index) :
    conj (char r j) * char s j = char (s-r) j := by
  rw [char_conj, ← char_add, sub_eq_add_neg, add_comm]

private lemma scale_dot (a b : ℂ) (u v : Block) :
    dot (scale a u) (scale b v) = (conj a * b) * dot u v := by
  simp [dot, scale]; ring

private lemma clock_overlap (r s : Index) (u v : Vec) :
    overlap (clock r u) (clock s v) = ∑ j, char (s-r) j * dot (u j) (v j) := by
  simp [overlap, clock, scale_dot, char_mod]

private lemma clock_first (r s : Index) (u v : Vec) :
    overlap (clock r u) (clock s v) = overlap (clock (r-s) u) v := by
  rw [clock_overlap]
  unfold overlap clock
  apply Finset.sum_congr rfl
  intro j _
  have h := char_conj (r-s) j
  simp only [neg_sub] at h
  simp [scale, dot, h]; ring

private lemma norm_dot (u : Block) :
    dot u u = ↑(Complex.normSq u.1 + Complex.normSq u.2) := by
  simp only [dot, Complex.ofReal_add, mul_comm (conj u.1), mul_comm (conj u.2),
    Complex.mul_conj]

private lemma skew_cross (η : UnitPhase) (u : Block) : dot u (skew η u) = 0 := by
  simp [dot, skew]; ring

private lemma skew_cross_rev (η : UnitPhase) (u : Block) : dot (skew η u) u = 0 := by
  simp [dot, skew]; ring

private lemma skew_flat (η : Phases) (g : Vec) (hf : Flat g) : Flat (J η g) := by
  intro j
  simp [J, skew, Complex.normSq_mul, (η j).property, (hf j).1, (hf j).2]

private lemma clock_flat (k : Index) (v : Vec) (hf : Flat v) : Flat (clock k v) := by
  intro j
  simp [clock, scale, Complex.normSq_mul, unit_char, (hf j).1, (hf j).2]

private lemma branch_gram (r s : Index) (u : Vec) (hu : Flat u) :
    overlap (clock r u) (clock s u) = if r = s then 1 else 0 := by
  rw [clock_overlap]
  simp_rw [norm_dot, (hu _).1, (hu _).2]
  rw [← Finset.sum_mul, sum_char]
  by_cases h : r = s
  · subst s; norm_num
  · simp [sub_ne_zero.mpr (Ne.symm h), h]

theorem companion_flat (η : Phases) (g : Vec) (hf : Flat g) (r : Index) (b : Bool) :
    Flat (companion η g r b) := by
  cases b
  · exact clock_flat r g hf
  · exact clock_flat r (J η g) (skew_flat η g hf)

theorem companion_gram (η : Phases) (g : Vec) (hf : Flat g)
    (r : Index) (b : Bool) (s : Index) (c : Bool) :
    overlap (companion η g r b) (companion η g s c) =
      if r = s ∧ b = c then 1 else 0 := by
  cases b <;> cases c
  · simpa [companion] using branch_gram r s g hf
  · simp [companion, clock_overlap, J, skew_cross]
  · simp [companion, clock_overlap, J, skew_cross_rev]
  · simpa [companion] using branch_gram r s (J η g) (skew_flat η g hf)

private lemma amplitude_conj : conj amplitude = amplitude := Complex.conj_ofReal _

private lemma amplitude_norm : Complex.normSq amplitude = 1/10 := by
  simp [amplitude, Complex.normSq_ofReal, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 10)]

private lemma first_flat (η : Phases) (b : Bool) : Flat (first η b) := by
  intro j
  cases b <;> simp [first, amplitude_norm, Complex.normSq_mul, (η j).property]

theorem anchor_flat (η : Phases) (r : Index) (b : Bool) : Flat (anchor η r b) :=
  clock_flat r _ (first_flat η b)

theorem anchor_gram (η : Phases) (r : Index) (b : Bool) (s : Index) (c : Bool) :
    overlap (anchor η r b) (anchor η s c) = if r = s ∧ b = c then 1 else 0 := by
  cases b <;> cases c
  · simpa [anchor] using branch_gram r s _ (first_flat η false)
  · simp [anchor, clock_overlap, first, dot]
  · simp [anchor, clock_overlap, first, dot]
  · simpa [anchor] using branch_gram r s _ (first_flat η true)

private lemma phase_mul_conj (e : UnitPhase) : (e:ℂ) * conj (e:ℂ) = 1 := by
  rw [Complex.mul_conj, e.property, Complex.ofReal_one]

private lemma first_skew (η : Phases) (g : Vec) (j : Index) (b : Bool) :
    dot (first η b j) (J η g j) =
      (if b then 1 else -1 : ℂ) * conj (dot (first η (!b) j) (g j)) := by
  cases b
  · simp [dot, first, J, skew, amplitude_conj]; ring
  · simp [dot, first, J, skew, amplitude_conj]
    calc
      _ = ((η j:ℂ)*conj (η j:ℂ)) *
        (amplitude*conj (g j).2 + amplitude*conj (g j).1) := by ring
      _ = _ := by rw [phase_mul_conj]; ring

private lemma one_clock (r : Index) (u v : Vec) :
    overlap (clock r u) v = ∑ j, conj (char r j) * dot (u j) (v j) := by
  unfold overlap clock
  apply Finset.sum_congr rfl
  intro j _
  simp [dot, scale]; ring

private lemma anchor_skew (η : Phases) (g : Vec) (r : Index) (b : Bool) :
    overlap (anchor η r b) (J η g) =
      (if b then 1 else -1 : ℂ) * conj (overlap (anchor η (-r) (!b)) g) := by
  simp only [anchor, one_clock, first_skew, map_sum, map_mul, RingHomCompTriple.comp_apply,
    starRingEnd_self_apply, ← char_conj r, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Unbiasedness to the deformed Fourier measurement. -/
def AnchorUnbiased (η : Phases) (g : Vec) : Prop :=
  ∀ r b, Complex.normSq (overlap (anchor η r b) g) = 1/10

/-- All one hundred cross-measurement probabilities follow from the ten seed equations. -/
theorem companion_unbiased (η : Phases) (g : Vec) (hg : AnchorUnbiased η g)
    (r : Index) (b : Bool) (s : Index) (c : Bool) :
    Complex.normSq (overlap (anchor η r b) (companion η g s c)) = 1/10 := by
  unfold anchor companion
  rw [clock_first]
  cases c
  · exact hg (r-s) b
  · change Complex.normSq (overlap (anchor η (r-s) b) (J η g)) = _
    rw [anchor_skew]
    have h := hg (s-r) (!b)
    cases b <;> simpa using h

/-- The unnormalized five-point Fourier coefficient. -/
def spectrum (u : Index → ℂ) (r : Index) : ℂ := ∑ j, conj (char r j) * u j

/-- Two real amplitudes and a common block phase give the physical seed. -/
def profileSeed (p : Phases) (c s : Index → ℝ) : Vec := fun j =>
  (amplitude * (p j : ℂ) * (c j + Complex.I * s j),
   amplitude * (p j : ℂ) * (c j - Complex.I * s j))

theorem profile_flat (p : Phases) (c s : Index → ℝ)
    (h : ∀ j, c j ^ 2 + s j ^ 2 = 1) : Flat (profileSeed p c s) := by
  intro j
  simp only [profileSeed, Complex.normSq_mul, amplitude_norm, (p j).property, mul_one]
  simp [Complex.normSq_apply, ← sq, h j]

private lemma amplitude_sq : amplitude * amplitude = 1/10 := by
  have h := Complex.mul_conj amplitude
  rw [amplitude_conj, amplitude_norm] at h
  simpa using h

private lemma dot_profile (η p : Phases) (c s : Index → ℝ) (j : Index) (b : Bool) :
    dot (first η b j) (profileSeed p c s j) =
      if b then (Complex.I/5) * ((η j : ℂ) * (p j : ℂ) * s j)
      else (1/5 : ℂ) * ((p j : ℂ) * c j) := by
  cases b
  · simp only [Bool.false_eq_true, if_false, first, dot, profileSeed, amplitude_conj]
    calc
      _ = (amplitude * amplitude) * (2 * (p j : ℂ) * c j) := by ring
      _ = _ := by rw [amplitude_sq]; ring
  · simp [first, dot, profileSeed, amplitude_conj]
    calc
      _ = (amplitude * amplitude) * (2 * Complex.I * (η j : ℂ) * (p j : ℂ) * s j) := by ring
      _ = _ := by rw [amplitude_sq]; ring

theorem profile_overlaps (η p : Phases) (c s : Index → ℝ) (r : Index) (b : Bool) :
    overlap (anchor η r b) (profileSeed p c s) =
      if b then (Complex.I/5) * spectrum (fun j => (η j : ℂ) * (p j : ℂ) * s j) r
      else (1/5 : ℂ) * spectrum (fun j => (p j : ℂ) * c j) r := by
  simp only [anchor, one_clock, dot_profile, spectrum]
  cases b <;> simp only [if_true, if_false, Bool.false_eq_true, Finset.mul_sum] <;>
    exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- A pair of length-five spectra with the stated power and a pointwise circular
amplitude profile supplies an explicit common-unbiased seed. -/
theorem profile_unbiased (η p : Phases) (c s : Index → ℝ)
    (hc : ∀ r, Complex.normSq (spectrum (fun j => (p j : ℂ) * c j) r) = 5/2)
    (hs : ∀ r, Complex.normSq (spectrum (fun j => (η j : ℂ) * (p j : ℂ) * s j) r) = 5/2) :
    AnchorUnbiased η (profileSeed p c s) := by
  intro r b
  rw [profile_overlaps]
  cases b <;> simp only [if_true, if_false, Bool.false_eq_true, Complex.normSq_mul, hc, hs,
    Complex.normSq_div] <;> norm_num [Complex.normSq_apply]

/-- A monomial equivalence invariant of the varying anchor.  It is the quotient
of the products on opposite corners, for two block-zero coordinates and the two DC columns. -/
theorem anchor_cross_ratio (η : Phases) (u v : Index) :
    ((anchor η 0 false u).1 * (anchor η 0 true v).1) /
      ((anchor η 0 true u).1 * (anchor η 0 false v).1) =
      conj (η v : ℂ) / conj (η u : ℂ) := by
  have hq : amplitude ≠ 0 := by
    intro h
    have h' := amplitude_norm
    rw [h] at h'
    norm_num at h'
  have he : conj (η u : ℂ) ≠ 0 := by
    have hh := phase_mul_conj (η u)
    exact right_ne_zero_of_mul_eq_one hh
  simp [anchor, clock, scale, char, first]
  field_simp
  ring

/-- Unnormalized synthesis from the five spectral values. -/
def synth (f : Index → ℂ) (j : Index) : ℂ := ∑ k, char k j * f k

theorem spectrum_synth (f : Index → ℂ) (r : Index) :
    spectrum (synth f) r = 5 * f r := by
  simp only [spectrum, synth, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, char_mod, ← Finset.sum_mul, sum_char]
  simp [sub_eq_zero, ite_mul]

private lemma synth_duality (f v : Index → ℂ) :
    (∑ j, conj (synth f j) * v j) = ∑ k, conj (f k) * spectrum v k := by
  simp only [synth, spectrum, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem synth_energy (f : Phases) :
    ∑ j, Complex.normSq (synth (fun k => (f k : ℂ)) j) = 25 := by
  have h := synth_duality (fun k => (f k : ℂ)) (synth (fun k => (f k : ℂ)))
  simp_rw [spectrum_synth] at h
  have hv (k : Index) : conj (f k : ℂ) * (5 * (f k : ℂ)) = 5 := by
    calc
      _ = 5 * ((f k : ℂ) * conj (f k : ℂ)) := by ring
      _ = 5 := by rw [phase_mul_conj]; ring
  simp_rw [hv, mul_comm (conj _), Complex.mul_conj] at h
  norm_num at h
  have he := congrArg Complex.re h
  simpa [Fin.sum_univ_succ] using he

def onePhase : UnitPhase := ⟨1, by simp⟩
def evenFive (x y : UnitPhase) (k : Index) : UnitPhase :=
  if k=0 then onePhase else if k=1 ∨ k=4 then x else y
def raw (x y : UnitPhase) := synth (fun k => (evenFive x y k : ℂ))

private lemma char_swap (r j : Index) : char r j = char j r := by simp [char, mul_comm]

private lemma even_raw (x y : UnitPhase) (j : Index) : raw x y (-j) = raw x y j := by
  fin_cases j <;> simp only [raw, synth, Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_empty]
  · change omega^0 * (1:ℂ) + (omega^0 * (x:ℂ) + (omega^0 * (y:ℂ) + (omega^0 * (y:ℂ) + (omega^0 * (x:ℂ) + 0)))) = omega^0 * (1:ℂ) + (omega^0 * (x:ℂ) + (omega^0 * (y:ℂ) + (omega^0 * (y:ℂ) + (omega^0 * (x:ℂ) + 0))))
    ring
  · change omega^0 * (1:ℂ) + (omega^4 * (x:ℂ) + (omega^3 * (y:ℂ) + (omega^2 * (y:ℂ) + (omega^1 * (x:ℂ) + 0)))) = omega^0 * (1:ℂ) + (omega^1 * (x:ℂ) + (omega^2 * (y:ℂ) + (omega^3 * (y:ℂ) + (omega^4 * (x:ℂ) + 0))))
    ring
  · change omega^0 * (1:ℂ) + (omega^3 * (x:ℂ) + (omega^1 * (y:ℂ) + (omega^4 * (y:ℂ) + (omega^2 * (x:ℂ) + 0)))) = omega^0 * (1:ℂ) + (omega^2 * (x:ℂ) + (omega^4 * (y:ℂ) + (omega^1 * (y:ℂ) + (omega^3 * (x:ℂ) + 0))))
    ring
  · change omega^0 * (1:ℂ) + (omega^2 * (x:ℂ) + (omega^4 * (y:ℂ) + (omega^1 * (y:ℂ) + (omega^3 * (x:ℂ) + 0)))) = omega^0 * (1:ℂ) + (omega^3 * (x:ℂ) + (omega^1 * (y:ℂ) + (omega^4 * (y:ℂ) + (omega^2 * (x:ℂ) + 0))))
    ring
  · change omega^0 * (1:ℂ) + (omega^1 * (x:ℂ) + (omega^2 * (y:ℂ) + (omega^3 * (y:ℂ) + (omega^4 * (x:ℂ) + 0)))) = omega^0 * (1:ℂ) + (omega^4 * (x:ℂ) + (omega^3 * (y:ℂ) + (omega^2 * (y:ℂ) + (omega^1 * (x:ℂ) + 0))))
    ring

private lemma raw_zero (x y : UnitPhase) :
    raw x y 0 = 1+2*(x:ℂ)+2*(y:ℂ) := by
  simp [raw, synth, Fin.sum_univ_succ, evenFive, onePhase, char]
  ring

private lemma raw_complement (x y : UnitPhase)
    (h0 : Complex.normSq (1+2*(x:ℂ)+2*(y:ℂ)) = 5) (j : Index) :
    Complex.normSq (raw x y j) + Complex.normSq (raw x y (2*j)) = 10 := by
  have h := synth_energy (evenFive x y)
  change ∑ k, Complex.normSq (raw x y k) = 25 at h
  have hu : Complex.normSq (raw x y 0) = 5 := by rwa [raw_zero]
  have h4 : raw x y 4 = raw x y 1 := even_raw x y 1
  have h3 : raw x y 3 = raw x y 2 := even_raw x y 2
  have h12 : Complex.normSq (raw x y 1) + Complex.normSq (raw x y 2) = 10 := by
    norm_num [Fin.sum_univ_succ] at h
    change Complex.normSq (raw x y 0) + (Complex.normSq (raw x y 1) + (Complex.normSq (raw x y 2) + (Complex.normSq (raw x y 3) + Complex.normSq (raw x y 4)))) = 25 at h
    rw [h4,h3,hu] at h
    linarith
  fin_cases j
  · change Complex.normSq (raw x y 0) + Complex.normSq (raw x y 0) = 10
    linarith [hu]
  · change Complex.normSq (raw x y 1) + Complex.normSq (raw x y 2) = 10
    exact h12
  · change Complex.normSq (raw x y 2) + Complex.normSq (raw x y 4) = 10
    rw [h4]; linarith
  · change Complex.normSq (raw x y 3) + Complex.normSq (raw x y 1) = 10
    rw [h3]; linarith
  · change Complex.normSq (raw x y 4) + Complex.normSq (raw x y 3) = 10
    rw [h4,h3]; linarith

private lemma reflected_spectrum (u : Index → ℂ) (r : Index) :
    spectrum (fun j => conj (u (2*j))) r = conj (spectrum u (2*r)) := by
  simp only [spectrum, map_sum, map_mul, starRingEnd_self_apply]
  simp_rw [char_conj]
  fin_cases r <;> simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_empty]
  · change omega^0 * conj (u 0) + (omega^0 * conj (u 2) + (omega^0 * conj (u 4) + (omega^0 * conj (u 1) + (omega^0 * conj (u 3) + 0)))) = omega^0 * conj (u 0) + (omega^0 * conj (u 1) + (omega^0 * conj (u 2) + (omega^0 * conj (u 3) + (omega^0 * conj (u 4) + 0))))
    ring
  · change omega^0 * conj (u 0) + (omega^4 * conj (u 2) + (omega^3 * conj (u 4) + (omega^2 * conj (u 1) + (omega^1 * conj (u 3) + 0)))) = omega^0 * conj (u 0) + (omega^2 * conj (u 1) + (omega^4 * conj (u 2) + (omega^1 * conj (u 3) + (omega^3 * conj (u 4) + 0))))
    ring
  · change omega^0 * conj (u 0) + (omega^3 * conj (u 2) + (omega^1 * conj (u 4) + (omega^4 * conj (u 1) + (omega^2 * conj (u 3) + 0)))) = omega^0 * conj (u 0) + (omega^4 * conj (u 1) + (omega^3 * conj (u 2) + (omega^2 * conj (u 3) + (omega^1 * conj (u 4) + 0))))
    ring
  · change omega^0 * conj (u 0) + (omega^2 * conj (u 2) + (omega^4 * conj (u 4) + (omega^1 * conj (u 1) + (omega^3 * conj (u 3) + 0)))) = omega^0 * conj (u 0) + (omega^1 * conj (u 1) + (omega^2 * conj (u 2) + (omega^3 * conj (u 3) + (omega^4 * conj (u 4) + 0))))
    ring
  · change omega^0 * conj (u 0) + (omega^1 * conj (u 2) + (omega^2 * conj (u 4) + (omega^3 * conj (u 1) + (omega^4 * conj (u 3) + 0)))) = omega^0 * conj (u 0) + (omega^3 * conj (u 1) + (omega^1 * conj (u 2) + (omega^4 * conj (u 3) + (omega^2 * conj (u 4) + 0))))
    ring

private lemma spectrum_scale (q : ℂ) (u : Index → ℂ) (r : Index) :
    spectrum (fun j => q * u j) r = q * spectrum u r := by
  simp only [spectrum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

def alpha (x y : UnitPhase) (j : Index) : ℂ := amplitude * raw x y j
def beta (x y : UnitPhase) (j : Index) : ℂ := amplitude * conj (raw x y (2*j))

theorem even_five_complement (x y : UnitPhase)
    (h0 : Complex.normSq (1+2*(x:ℂ)+2*(y:ℂ)) = 5) (j : Index) :
    Complex.normSq (alpha x y j) + Complex.normSq (beta x y j) = 1 := by
  simp only [alpha, beta, Complex.normSq_mul, amplitude_norm, Complex.normSq_conj]
  linarith [raw_complement x y h0 j]

theorem even_five_spectra (x y : UnitPhase) (r : Index) :
    Complex.normSq (spectrum (alpha x y) r) = 5/2 ∧
    Complex.normSq (spectrum (beta x y) r) = 5/2 := by
  have hraw (k : Index) : spectrum (raw x y) k = 5 * (evenFive x y k : ℂ) :=
    spectrum_synth _ k
  change Complex.normSq (spectrum (fun j => amplitude * raw x y j) r) = _ ∧
    Complex.normSq (spectrum (fun j => amplitude * conj (raw x y (2*j))) r) = _
  rw [spectrum_scale, spectrum_scale, reflected_spectrum, hraw, hraw]
  simp only [Complex.normSq_mul, Complex.normSq_conj, amplitude_norm, (evenFive x y _).property]
  norm_num [Complex.normSq_apply]

/-- Polar phase; at zero any phase works and we fix one. -/
def phaseOf (z : ℂ) : UnitPhase := if h : z=0 then onePhase else
  ⟨z / (‖z‖ : ℂ), by
    rw [Complex.normSq_div, Complex.normSq_ofReal, ← sq, Complex.sq_norm]
    exact div_self (by simpa using h)⟩

private lemma polar_mul (z : ℂ) : (phaseOf z : ℂ) * (‖z‖ : ℂ) = z := by
  by_cases h : z=0
  · simp [h]
  · simp [phaseOf, h, norm_ne_zero_iff.mpr h]

def seedPhases (x y : UnitPhase) (j : Index) : UnitPhase := phaseOf (alpha x y j)
def deformedPhases (x y : UnitPhase) (j : Index) : UnitPhase :=
  ⟨(phaseOf (beta x y j) : ℂ) * conj (seedPhases x y j : ℂ), by
    simp [Complex.normSq_mul, (phaseOf (beta x y j)).property, (seedPhases x y j).property]⟩
def explicitSeed (x y : UnitPhase) : Vec :=
  profileSeed (seedPhases x y) (fun j => ‖alpha x y j‖) (fun j => ‖beta x y j‖)

private lemma beta_polar (x y : UnitPhase) (j : Index) :
    (deformedPhases x y j : ℂ) * (seedPhases x y j : ℂ) * ↑‖beta x y j‖ = beta x y j := by
  change ((phaseOf _ : ℂ) * conj (seedPhases x y j : ℂ)) * _ * _ = _
  calc
    _ = ((seedPhases x y j : ℂ)*conj (seedPhases x y j : ℂ)) *
      ((phaseOf (beta x y j):ℂ) * ↑‖beta x y j‖) := by ring
    _ = _ := by rw [phase_mul_conj, polar_mul, one_mul]

/-- Only the two unit numbers and one scalar power identity are inputs.  The phases,
seed, and hence all twenty non-coordinate measurement vectors are explicit. -/
theorem explicit_even_seed (x y : UnitPhase)
    (h : Complex.normSq (1+2*(x:ℂ)+2*(y:ℂ)) = 5) :
    Flat (explicitSeed x y) ∧ AnchorUnbiased (deformedPhases x y) (explicitSeed x y) := by
  constructor
  · apply profile_flat
    intro j
    simpa only [Complex.sq_norm] using even_five_complement x y h j
  · apply profile_unbiased
    · intro r
      simpa only [seedPhases, polar_mul] using (even_five_spectra x y r).1
    · intro r
      simpa only [beta_polar] using (even_five_spectra x y r).2

def angleCos (t : UnitPhase) : ℝ :=
  (-(t:ℂ).re + Real.sqrt ((t:ℂ).re^2+4))/4

private lemma cos_poly (t : UnitPhase) :
    4*angleCos t^2+2*(t:ℂ).re*angleCos t=1 := by
  have h := Real.sq_sqrt (show 0 ≤ (t:ℂ).re^2+4 by positivity)
  unfold angleCos
  nlinarith

private lemma cos_range (t : UnitPhase) : 0 ≤ 1-angleCos t^2 := by
  have h := t.property
  simp only [Complex.normSq_apply, ← sq] at h
  have hp := Real.sqrt_nonneg ((t:ℂ).re^2+4)
  have hs := Real.sq_sqrt (show 0 ≤ (t:ℂ).re^2+4 by positivity)
  have hup : Real.sqrt ((t:ℂ).re^2+4) ≤ 3 := by nlinarith [sq_nonneg (t:ℂ).im]
  have hr : -(1:ℝ) ≤ (t:ℂ).re := by nlinarith [sq_nonneg (t:ℂ).im]
  have hl : (t:ℂ).re ≤ 1 := by nlinarith [sq_nonneg (t:ℂ).im]
  have hle : angleCos t ≤ 1 := by unfold angleCos; linarith
  have hge : -1 ≤ angleCos t := by unfold angleCos; linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ 1+angleCos t by linarith)]

def curveFactor (t : UnitPhase) : UnitPhase :=
  ⟨⟨angleCos t, Real.sqrt (1-angleCos t^2)⟩, by
    simp only [Complex.normSq_apply, ← sq]
    rw [Real.sq_sqrt (cos_range t)]
    ring⟩

def curveX (t : UnitPhase) : UnitPhase :=
  ⟨(t:ℂ) * curveFactor t, by simp [Complex.normSq_mul, t.property, (curveFactor t).property]⟩
def curveY (t : UnitPhase) : UnitPhase :=
  ⟨(t:ℂ) * conj (curveFactor t : ℂ), by
    simp [Complex.normSq_mul, t.property, (curveFactor t).property]⟩

private lemma factor_sum (t : UnitPhase) :
    (curveFactor t : ℂ) + conj (curveFactor t : ℂ) = (2*angleCos t : ℝ) := by
  apply Complex.ext
  · simp [curveFactor]; ring
  · simp [curveFactor]

private lemma curve_power (t : UnitPhase) :
    Complex.normSq (1+2*(curveX t:ℂ)+2*(curveY t:ℂ))=5 := by
  have hs : 1+2*(curveX t:ℂ)+2*(curveY t:ℂ) = 1 + 4*(t:ℂ)*angleCos t := by
    calc
      _ = 1+2*(t:ℂ)*((curveFactor t:ℂ)+conj (curveFactor t:ℂ)) := by
        change 1+2*((t:ℂ)*_)+2*((t:ℂ)*_)=_
        ring
      _ = _ := by rw [factor_sum]; push_cast; ring
  rw [hs]
  have h := t.property
  simp only [Complex.normSq_apply, ← sq] at h
  have he : (t:ℂ).re^2*angleCos t^2+(t:ℂ).im^2*angleCos t^2=angleCos t^2 := by
    rw [← add_mul, h, one_mul]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith [cos_poly t]

/-- For every unit complex parameter the displayed root formulas construct an actual
common-unbiased seed.  In particular no seed-existence hypothesis is present. -/
theorem circle_seed (t : UnitPhase) :
    Flat (explicitSeed (curveX t) (curveY t)) ∧
    AnchorUnbiased (deformedPhases (curveX t) (curveY t)) (explicitSeed (curveX t) (curveY t)) :=
  explicit_even_seed _ _ (curve_power t)

private def b1 := omega+omega^4
private def b2 := omega^2+omega^3
private lemma bases_sum : b1+b2 = -1 := by
  calc
    _ = (omega^4+omega^3+omega^2+omega+1)-1 := by unfold b1 b2; ring
    _ = _ := by rw [omega_sum]; ring
private lemma bases_product : b1*b2 = -1 := by
  calc
    _ = (omega+omega^2)*omega^5+omega^3+omega^4 := by unfold b1 b2; ring
    _ = b1+b2 := by rw [omega_five]; unfold b1 b2; ring
    _ = _ := bases_sum

private lemma raw_product (x y : UnitPhase) :
    raw x y 1 * raw x y 2 = 1 - ((x:ℂ)+y) - ((x:ℂ)+y)^2 + 5*(x:ℂ)*y := by
  have h1 : raw x y 1 = 1+b1*(x:ℂ)+b2*(y:ℂ) := by
    simp only [raw,synth,Fin.sum_univ_succ,Fin.sum_univ_zero,Finset.sum_empty]
    change omega^0 * 1 + (omega^1*x.val + (omega^2*y.val + (omega^3*y.val + (omega^4*x.val+0)))) = _
    unfold b1 b2; ring
  have h2 : raw x y 2 = 1+b2*(x:ℂ)+b1*(y:ℂ) := by
    simp only [raw,synth,Fin.sum_univ_succ,Fin.sum_univ_zero,Finset.sum_empty]
    change omega^0 * 1 + (omega^2*x.val + (omega^4*y.val + (omega^1*y.val + (omega^3*x.val+0)))) = _
    unfold b1 b2; ring
  rw [h1,h2]
  calc
    _ = 1 + (b1+b2)*((x:ℂ)+y) + (b1*b2)*((x:ℂ)+y)^2 +
      ((b1+b2)^2-4*(b1*b2))*(x:ℂ)*y := by ring
    _ = _ := by rw [bases_sum,bases_product]; ring

private lemma curve_sum (t : UnitPhase) :
    (curveX t:ℂ) + curveY t = 2*(t:ℂ)*angleCos t := by
  calc
    _ = (t:ℂ)*((curveFactor t:ℂ)+conj (curveFactor t:ℂ)) := by
      change (t:ℂ)*_+(t:ℂ)*_=_; ring
    _ = _ := by rw [factor_sum]; push_cast; ring

private lemma curve_mul (t : UnitPhase) : (curveX t:ℂ)*(curveY t:ℂ) = (t:ℂ)^2 := by
  change ((t:ℂ)*_) * ((t:ℂ)*_) = _
  calc
    _ = (t:ℂ)^2 * ((curveFactor t : ℂ)*conj (curveFactor t:ℂ)) := by ring
    _ = _ := by rw [phase_mul_conj,mul_one]

/-- The imaginary part controlling the varying anchor cross ratio. For the upper
semicircle it is strictly negative, including arbitrarily close to the Fourier endpoint. -/
theorem varying_phase_identity (t : UnitPhase) :
    ((raw (curveX t) (curveY t) 0)^2 * conj
      (raw (curveX t) (curveY t) 1 * raw (curveX t) (curveY t) 2)).im =
      -10*angleCos t*(t:ℂ).im*(2*(t:ℂ).re^2+3) := by
  obtain h := t.property
  simp only [Complex.normSq_apply, ← sq] at h
  have hz : (t:ℂ).re^2+(t:ℂ).im^2-1=0 := by linarith
  have hc : 4*angleCos t^2+2*(t:ℂ).re*angleCos t-1=0 := by linarith [cos_poly t]
  rw [raw_zero, raw_product, show 1+2*(curveX t:ℂ)+2*(curveY t:ℂ) =
    1+2*((curveX t:ℂ)+(curveY t:ℂ)) by ring, curve_sum]
  rw [show 5*(curveX t:ℂ)*(curveY t:ℂ)=5*((curveX t:ℂ)*(curveY t:ℂ)) by ring, curve_mul]
  calc
    _ = -10*angleCos t*(t:ℂ).im*(2*(t:ℂ).re^2+3) +
      (-40*angleCos t*(t:ℂ).im)*((t:ℂ).re^2+(t:ℂ).im^2-1) +
      (10*(t:ℂ).re*(t:ℂ).im)*(4*angleCos t^2+2*(t:ℂ).re*angleCos t-1) := by
        simp [pow_two,Complex.mul_re,Complex.mul_im]; ring
    _ = _ := by rw [hz,hc]; ring

private lemma raw_pair_phase (x y : UnitPhase) (k : Index) :
    raw x y k * raw x y (2*k) =
      conj (deformedPhases x y k : ℂ) * (10 * ‖alpha x y k‖ * ‖beta x y k‖ : ℝ) := by
  have h := congrArg (fun z : ℂ => conj z) (polar_mul (beta x y k))
  simp only [map_mul, Complex.conj_ofReal] at h
  have hh := polar_mul (alpha x y k)
  have hn : ((10:ℂ)*amplitude*amplitude) = 1 := by
    rw [mul_assoc, amplitude_sq]; norm_num
  calc
    _ = (10:ℂ) * (alpha x y k * conj (beta x y k)) := by
      simp only [alpha,beta,map_mul,amplitude_conj,starRingEnd_self_apply]
      calc
        _ = (10*amplitude*amplitude) * (raw x y k * raw x y (2*k)) := by rw [hn, one_mul]
        _ = _ := by ring
    _ = _ := by
      conv_lhs => rw [← h, ← hh]
      simp [deformedPhases,seedPhases]
      ring

def curveRatio (t : UnitPhase) : ℂ :=
  let η := deformedPhases (curveX t) (curveY t)
  conj (η 0 : ℂ) / conj (η 1 : ℂ)

theorem curve_ratio_is_minor (t : UnitPhase) :
    let η := deformedPhases (curveX t) (curveY t)
    ((anchor η 0 false 1).1 * (anchor η 0 true 0).1) /
      ((anchor η 0 true 1).1 * (anchor η 0 false 0).1) = curveRatio t :=
  anchor_cross_ratio _ _ _

theorem curve_ratio_nonreal (t : UnitPhase) (hu : 0 < (t:ℂ).im) :
    (curveRatio t).im ≠ 0 := by
  let x := curveX t
  let y := curveY t
  let η := deformedPhases x y
  have h_div : curveRatio t = conj (η 0 : ℂ) * (η 1 : ℂ) := by
    change conj (η 0 : ℂ)/conj (η 1 : ℂ)=_
    have h := phase_mul_conj (η 1)
    apply (div_eq_iff (right_ne_zero_of_mul_eq_one h)).mpr
    rw [mul_assoc, h, mul_one]
  have ha : 0 < angleCos t := by
    have h := Real.sq_sqrt (show 0 ≤ (t:ℂ).re^2 + 4 by positivity)
    have hp := Real.sqrt_nonneg ((t:ℂ).re^2+4)
    unfold angleCos
    nlinarith
  have hneg : -10*angleCos t*(t:ℂ).im*(2*(t:ℂ).re^2+3) < 0 := by
    have hpos : 0 < 10*angleCos t*(t:ℂ).im*(2*(t:ℂ).re^2+3) := by positivity
    linarith
  have h0 : raw x y 0 ^ 2 = conj (η 0 : ℂ) * ↑(10*‖alpha x y 0‖*‖beta x y 0‖) := by
    simpa [pow_two] using raw_pair_phase x y 0
  have h1 : raw x y 1 * raw x y 2 = conj (η 1 : ℂ) * ↑(10*‖alpha x y 1‖*‖beta x y 1‖) := by
    simpa using raw_pair_phase x y 1
  have hv := varying_phase_identity t
  change ((raw x y 0)^2*conj (raw x y 1 * raw x y 2)).im = _ at hv
  rw [h0,h1,map_mul,Complex.conj_ofReal,starRingEnd_self_apply] at hv
  let L : ℝ := 10*‖alpha x y 0‖*‖beta x y 0‖
  let M : ℝ := 10*‖alpha x y 1‖*‖beta x y 1‖
  change (conj (η 0 : ℂ)*L*((η 1 : ℂ)*M)).im = _ at hv
  have hprod : conj (η 0 : ℂ)*L*((η 1 : ℂ)*M) = curveRatio t * ((L*M:ℝ):ℂ) := by
    rw [h_div,Complex.ofReal_mul L M]; ring
  rw [hprod,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re] at hv
  intro h
  rw [h] at hv
  linarith

private lemma synth_as_spectrum (f : Index → ℂ) (k : Index) :
    synth f k = spectrum f (-k) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [char_conj, neg_neg, char_swap]

private lemma endpoint_raw (j : Index) :
    conj (raw (curveX onePhase) (curveY onePhase) (2*j)) =
      raw (curveX onePhase) (curveY onePhase) j := by
  let x := curveX onePhase
  let y := curveY onePhase
  have hy : (y:ℂ) = conj (x:ℂ) := by simp [x,y,curveX,curveY,onePhase]
  have hy' : conj (y:ℂ) = (x:ℂ) := by rw [hy,starRingEnd_self_apply]
  let f (k : Index) : ℂ := evenFive x y k
  have hf (k : Index) : conj (f (2*k)) = f k := by
    fin_cases k
    · change conj (1:ℂ) = 1; simp
    · exact hy'
    · exact hy.symm
    · exact hy.symm
    · exact hy'
  have h := reflected_spectrum f (-j)
  simp_rw [hf] at h
  change conj (synth f (2*j)) = synth f j
  simpa only [synth_as_spectrum,mul_neg] using h.symm

theorem curve_at_fourier (j : Index) :
    deformedPhases (curveX onePhase) (curveY onePhase) j = onePhase := by
  apply Subtype.ext
  have h : beta (curveX onePhase) (curveY onePhase) j =
      alpha (curveX onePhase) (curveY onePhase) j := by simp [beta,alpha,endpoint_raw]
  change (phaseOf _ : ℂ) * conj (phaseOf _ : ℂ) = 1
  rw [h, phase_mul_conj]

theorem curve_ratio_at_fourier : curveRatio onePhase = 1 := by
  simp only [curveRatio]
  rw [curve_at_fourier,curve_at_fourier]
  simp [onePhase]

@[fun_prop] private lemma continuous_curveX : Continuous fun t => (curveX t : ℂ) := by
  change Continuous fun t : UnitPhase => (t:ℂ) * ⟨angleCos t, Real.sqrt (1-angleCos t^2)⟩
  unfold angleCos
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

@[fun_prop] private lemma continuous_curveY : Continuous fun t => (curveY t : ℂ) := by
  change Continuous fun t : UnitPhase => (t:ℂ) * conj ⟨angleCos t, Real.sqrt (1-angleCos t^2)⟩
  apply continuous_subtype_val.mul
  apply Complex.continuous_conj.comp
  unfold angleCos
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop

private lemma raw_cont (j : Index) : Continuous fun t => raw (curveX t) (curveY t) j := by
  unfold raw synth
  apply continuous_finset_sum
  intro k _
  by_cases h : k=0
  · simp only [evenFive,h,if_true]; exact continuous_const
  · by_cases k14 : k=1 ∨ k=4
    · simp only [evenFive,h,k14,if_false,if_true]; fun_prop
    · simp only [evenFive,h,k14,if_false]; fun_prop

private lemma raw_base_nonzero (k : Index) :
    raw (curveX onePhase) (curveY onePhase) k ≠ 0 := by
  have h := raw_complement _ _ (curve_power onePhase) k
  have eq := congrArg Complex.normSq (endpoint_raw k)
  rw [Complex.normSq_conj] at eq
  intro hz
  rw [eq,hz] at h
  norm_num at h

private lemma phase_continuous {X : Type*} [TopologicalSpace X] (f : X → ℂ) (x : X)
    (hf : ContinuousAt f x) (hn : f x ≠ 0) :
    ContinuousAt (fun t => (phaseOf (f t) : ℂ)) x := by
  have ev := hf.eventually_ne hn
  apply (hf.div (Complex.continuous_ofReal.continuousAt.comp hf.norm)
    (by change (‖f x‖ : ℂ) ≠ 0; exact_mod_cast norm_ne_zero_iff.mpr hn)).congr_of_eventuallyEq
  filter_upwards [ev] with t ht
  simp [phaseOf,ht]

theorem anchor_phases_continuous_at_fourier (j : Index) :
    ContinuousAt (fun t => (deformedPhases (curveX t) (curveY t) j : ℂ)) onePhase := by
  have n : amplitude ≠ 0 := by
    intro hn
    have h := amplitude_norm
    rw [hn] at h
    norm_num at h
  have ha : ContinuousAt (fun t => alpha (curveX t) (curveY t) j) onePhase :=
    (continuous_const.mul (raw_cont j)).continuousAt
  have hb : ContinuousAt (fun t => beta (curveX t) (curveY t) j) onePhase :=
    (continuous_const.mul (Complex.continuous_conj.comp (raw_cont (2*j)))).continuousAt
  exact (phase_continuous _ _ hb (mul_ne_zero n (by simpa using raw_base_nonzero (2*j)))).mul
    (Complex.continuous_conj.continuousAt.comp
      (phase_continuous _ _ ha (mul_ne_zero n (raw_base_nonzero j))))

theorem curve_ratio_continuous_at_fourier : ContinuousAt curveRatio onePhase := by
  apply (Complex.continuous_conj.continuousAt.comp (anchor_phases_continuous_at_fourier 0)).div
    (Complex.continuous_conj.continuousAt.comp (anchor_phases_continuous_at_fourier 1))
  change conj (deformedPhases (curveX onePhase) (curveY onePhase) 1 : ℂ) ≠ 0
  rw [curve_at_fourier]
  simp [onePhase]

/-- For each fixed exponent the upper arc near the Fourier endpoint has a
physical cross ratio outside all roots of that order. -/
theorem eventually_not_root (n : ℕ) (hn : 0<n) :
    ∀ᶠ t : UnitPhase in nhds onePhase, 0 < (t:ℂ).im → (curveRatio t)^n ≠ 1 := by
  let geom (z : ℂ) := ∑ k ∈ Finset.range n, z^k
  have hc : Continuous geom := by unfold geom; fun_prop
  have hh : geom (curveRatio onePhase) ≠ 0 := by
    simp [curve_ratio_at_fourier,geom, Nat.ne_of_gt hn]
  filter_upwards [(hc.continuousAt.comp curve_ratio_continuous_at_fourier).eventually_ne hh] with t ht
  intro hpos he
  have h : geom (curveRatio t)*(curveRatio t-1) = 0 := by
    change (∑ k ∈ Finset.range n, curveRatio t^k) * (curveRatio t-1) = 0
    rw [geom_sum_mul,he,sub_self]
  have h1 := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ht)
  apply curve_ratio_nonreal t hpos
  rw [h1]; rfl

/-- Rational parametrization of the unit circle used to approach the Fourier endpoint. -/
def realParameter (s : ℝ) : UnitPhase :=
  ⟨⟨(1-s^2)/(1+s^2), 2*s/(1+s^2)⟩, by
    simp only [Complex.normSq_apply]
    have hn : (1+s^2) ≠ 0 := by positivity
    field_simp
    ring⟩

@[simp] theorem realParameter_zero : realParameter 0 = onePhase := by
  apply Subtype.ext
  apply Complex.ext <;> norm_num [realParameter,onePhase]

theorem realParameter_continuous : Continuous realParameter := by
  apply Continuous.subtype_mk
  change Continuous (fun s : ℝ => (⟨(1-s^2)/(1+s^2), 2*s/(1+s^2)⟩ : ℂ))
  simp only [Complex.mk_eq_add_mul_I]
  fun_prop (disch := first | positivity | intro x; positivity)

theorem real_curve_outside_roots (n : ℕ) (hn : 0<n) :
    ∀ᶠ s : ℝ in nhds 0, 0 < s → (curveRatio (realParameter s))^n ≠ 1 := by
  have ht : Filter.Tendsto realParameter (nhds 0) (nhds onePhase) := by
    simpa only [← realParameter_zero] using realParameter_continuous.continuousAt (x := 0)
  filter_upwards [ht (eventually_not_root n hn)] with s hs
  intro hp
  exact hs (show 0 < 2*s/(1+s^2) by positivity)

theorem real_curve_outside_fourier :
    ∀ᶠ s : ℝ in nhds 0, 0 < s → (curveRatio (realParameter s))^10 ≠ 1 :=
  real_curve_outside_roots 10 (by decide)

/-- These are the actual on-curve anchor measurements approaching Fourier. -/
theorem continuous_real_anchor (j : Index) :
    ContinuousAt (fun s => (deformedPhases (curveX (realParameter s))
      (curveY (realParameter s)) j : ℂ)) 0 := by
  have h := anchor_phases_continuous_at_fourier j
  rw [← realParameter_zero] at h
  exact h.comp realParameter_continuous.continuousAt

/-- Even arbitrary nonzero row/column multipliers cannot turn the entries of
these anchors into roots of a fixed order near the endpoint. A permuted Fourier
matrix is a special case at order ten. The first physical coordinate in each
two-dimensional block already supplies the obstruction. -/
def RephasableToRoots (η : Phases) (n : ℕ) : Prop :=
  ∃ (rows : Index → ℂ) (cols : Index → Bool → ℂ),
    (∀ j, rows j ≠ 0) ∧ (∀ k b, cols k b ≠ 0) ∧
    ∀ j k b, (rows j * (anchor η k b j).1 * cols k b)^n = 1

private lemma ratio_from_roots (t : UnitPhase) (n : ℕ)
    (hh : RephasableToRoots (deformedPhases (curveX t) (curveY t)) n) :
    curveRatio t ^ n = 1 := by
  let η := deformedPhases (curveX t) (curveY t)
  obtain ⟨u,v,hu,hv,h⟩ := hh
  let A := (anchor η 0 false 1).1
  let B := (anchor η 0 true 0).1
  let C := (anchor η 0 true 1).1
  let D := (anchor η 0 false 0).1
  have hc : C ≠ 0 := by
    have hc := (anchor_flat η 0 true 1).1
    change Complex.normSq C = _ at hc
    intro hz; rw [hz] at hc; norm_num at hc
  have hd : D ≠ 0 := by
    have hd := (anchor_flat η 0 false 0).1
    change Complex.normSq D = _ at hd
    intro hz; rw [hz] at hd; norm_num at hd
  have hi : A*B/(C*D) =
      ((u 1*A*v 0 false)*(u 0*B*v 0 true))/
      ((u 1*C*v 0 true)*(u 0*D*v 0 false)) := by
    field_simp [hu,hv,hc,hd]
    ring
  rw [← curve_ratio_is_minor]
  change (A*B/(C*D))^n=1
  rw [hi,div_pow, mul_pow (u 1*A*v 0 false) (u 0*B*v 0 true),
    mul_pow (u 1*C*v 0 true) (u 0*D*v 0 false), show (u 1*A*v 0 false)^n=1 from h 1 0 false,
    show (u 0*B*v 0 true)^n=1 from h 0 0 true, show (u 1*C*v 0 true)^n=1 from h 1 0 true,
    show (u 0*D*v 0 false)^n=1 from h 0 0 false]
  norm_num

theorem near_fourier_non_equivalent (n : ℕ) (hn : 0 < n) :
    ∀ᶠ s : ℝ in nhds 0, 0 < s →
      ¬ RephasableToRoots (deformedPhases (curveX (realParameter s)) (curveY (realParameter s))) n := by
  filter_upwards [real_curve_outside_roots n hn] with s hs
  intro hp hh
  exact hs hp (ratio_from_roots _ _ hh)

/-- Since any finite list of triples has only finitely many positional cross ratios,
the explicit curve escapes every such list on a sufficiently short positive arc. -/
theorem real_curve_avoids_finite (S : Finset ℂ) :
    ∀ᶠ s : ℝ in nhds 0, 0 < s → curveRatio (realParameter s) ∉ S := by
  classical
  have hc : ContinuousAt (fun s => curveRatio (realParameter s)) 0 := by
    have h := curve_ratio_continuous_at_fourier
    rw [← realParameter_zero] at h
    exact h.comp realParameter_continuous.continuousAt
  induction S using Finset.induction_on with
  | empty => simp
  | @insert z S hz ih =>
    by_cases h : z=1
    · subst z
      filter_upwards [ih,real_curve_outside_roots 1 (by decide)] with s hs hv
      intro hp
      simpa [hs hp] using hv hp
    · have hn : curveRatio (realParameter 0) ≠ z := by simpa [curve_ratio_at_fourier] using Ne.symm h
      filter_upwards [ih,hc.eventually_ne hn] with s hs hv
      intro hp
      simp only [Finset.mem_insert,not_or]
      exact ⟨hv,hs hp⟩

/-- A complete physical MU triple for every parameter, with the standard basis
represented by flat coordinates. -/
theorem exact_triples (t : UnitPhase) :
    let x := curveX t
    let y := curveY t
    let η := deformedPhases x y
    let g := explicitSeed x y
    (∀ r b, Flat (anchor η r b) ∧ Flat (companion η g r b)) ∧
    (∀ r b s c, overlap (anchor η r b) (anchor η s c) = if r=s ∧ b=c then 1 else 0) ∧
    (∀ r b s c, overlap (companion η g r b) (companion η g s c) = if r=s ∧ b=c then 1 else 0) ∧
    (∀ r b s c, Complex.normSq (overlap (anchor η r b) (companion η g s c)) = 1/10) := by
  obtain ⟨flat,unbiased⟩ := circle_seed t
  exact ⟨fun r b => ⟨anchor_flat _ r b, companion_flat _ _ flat r b⟩,
    anchor_gram _, companion_gram _ _ flat, companion_unbiased _ _ unbiased⟩

end
end MUB10.Deformation
