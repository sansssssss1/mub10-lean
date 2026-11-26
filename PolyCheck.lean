import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Defs
import Init.Data.List.Sort.Lemmas

/-! Normalization of finite sums with Gaussian integer coefficients.
The exponent encoding is external. Only terms sharing the same key are added.
Evaluation is preserved for every additive interpretation of the coefficients
at each key. A zero coefficient is removed. -/

namespace PolyCheck

abbrev Coeff := Int × Int
abbrev Term := Nat × Coeff

def eval {R : Type*} [AddCommMonoid R]
    (φ : Nat → Coeff →+ R) (xs : List Term) : R :=
  (xs.map (fun t => φ t.1 t.2)).sum

@[simp] theorem eval_nil {R : Type*} [AddCommMonoid R] (φ : Nat → Coeff →+ R) :
    eval φ [] = 0 := rfl

@[simp] theorem eval_cons {R : Type*} [AddCommMonoid R] (φ : Nat → Coeff →+ R)
    (t : Term) (xs : List Term) : eval φ (t :: xs) = φ t.1 t.2 + eval φ xs := rfl

@[simp] theorem eval_append {R : Type*} [AddCommMonoid R] (φ : Nat → Coeff →+ R)
    (xs ys : List Term) : eval φ (xs ++ ys) = eval φ xs + eval φ ys := by
  simp [eval]

theorem eval_flatMap {R α : Type*} [AddCommMonoid R] (φ : Nat → Coeff →+ R)
    (f : α → List Term) (xs : List α) :
    eval φ (xs.flatMap f) = (xs.map (fun x => eval φ (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem eval_ofFn {R : Type*} [AddCommMonoid R] (φ : Nat → Coeff →+ R)
    {n : Nat} (f : Fin n → Term) :
    eval φ (List.ofFn f) = ∑ i, φ (f i).1 (f i).2 := by
  simp [eval, List.map_ofFn, List.sum_ofFn, Function.comp_def]

private def emit (t : Term) (xs : List Term) : List Term :=
  if t.2 = 0 then xs else t :: xs

private theorem eval_emit {R : Type*} [AddCommMonoid R] (φ : Nat → Coeff →+ R)
    (t : Term) (xs : List Term) : eval φ (emit t xs) = φ t.1 t.2 + eval φ xs := by
  rcases t with ⟨k,c⟩
  by_cases hc : c = 0 <;> simp [emit, hc]

private def insertRun (t : Term) : List Term → List Term
  | [] => emit t []
  | u :: us =>
    if t.1 = u.1 then emit (t.1, t.2 + u.2) us else emit t (u :: us)

private theorem eval_insertRun {R : Type*} [AddCommMonoid R] (φ : Nat → Coeff →+ R)
    (t : Term) (xs : List Term) :
    eval φ (insertRun t xs) = φ t.1 t.2 + eval φ xs := by
  rcases t with ⟨k,c⟩
  cases xs with
  | nil => simp [insertRun, eval_emit]
  | cons u us =>
    rcases u with ⟨l,d⟩
    by_cases h : k = l
    · subst l
      simp [insertRun, eval_emit, map_add, add_assoc]
    · simp [insertRun, h, eval_emit]

private def keyLE (a b : Term) : Bool := decide (a.1 ≤ b.1)

def compress (xs : List Term) : List Term :=
  (xs.mergeSort keyLE).foldr insertRun []

theorem eval_compress {R : Type*} [AddCommMonoid R] (φ : Nat → Coeff →+ R)
    (xs : List Term) : eval φ (compress xs) = eval φ xs := by
  have fold_ok (ys : List Term) : eval φ (ys.foldr insertRun []) = eval φ ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp only [List.foldr_cons, eval_insertRun, ih, eval_cons]
  unfold compress
  rw [fold_ok]
  exact ((List.mergeSort_perm xs keyLE).map (fun t => φ t.1 t.2)).sum_eq

/-- Apply an additive coefficient map and multiply by an arbitrary monomial value. -/
def weighted {R : Type*} [NonUnitalNonAssocSemiring R] (g : Coeff →+ R)
    (monomial : Nat → R) (k : Nat) : Coeff →+ R where
  toFun c := g c * monomial k
  map_zero' := by simp
  map_add' x y := by simp [add_mul]

@[simp] theorem weighted_apply {R : Type*} [NonUnitalNonAssocSemiring R] (g : Coeff →+ R)
    (m : Nat → R) (k : Nat) (c : Coeff) : weighted g m k c = g c * m k := rfl

end PolyCheck
