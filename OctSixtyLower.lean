import OctSixtyPool
import Mathlib.Data.Finset.Card

namespace MUB10Oct.Sixty

private def rayText := include_str "oct-ray-witnesses.txt"
private def mateText := include_str "oct-mate-witnesses.txt"
private def lines (s : String) := (s.replace "\r" "").trim.splitOn "\n"
private def wordsData (s : String) (sep : String) := if s="-" then [] else s.splitOn sep
private def rparse (s : String) : ORow := s.toList.map fun c => ((c.toNat-'0'.toNat : Nat) : O)
private def bparse (s : String) : OBasis := (wordsData s " ").map rparse

def explicitRays (i : Fin 60) : Finset ORow :=
  ((lines rayText).map bparse |>.getD i.val []).toFinset

def explicitBases (i : Fin 60) : List OBasis :=
  ((lines mateText).map fun l => (wordsData l ";").map bparse).getD i.val []

def explicitMateSets (i : Fin 60) : Finset (Finset ORow) :=
  ((explicitBases i).map List.toFinset).toFinset

def ValidRay (i : Fin 60) (r : ORow) : Prop :=
  r.head? = some 0 ∧ r.length=10 ∧ ∀ h ∈ catalogue8 i, score h r ∈ targets

def ValidBasis (i : Fin 60) (B : OBasis) : Prop :=
  B.length=10 ∧ B.Nodup ∧ (∀ r ∈ B, ValidRay i r) ∧
    ∀ r ∈ B, ∀ s ∈ B, r≠s → score r s=0

instance (i : Fin 60) (r : ORow) : Decidable (ValidRay i r) := by unfold ValidRay; infer_instance
instance (i : Fin 60) (B : OBasis) : Decidable (ValidBasis i B) := by unfold ValidBasis; infer_instance

set_option maxRecDepth 100000 in
theorem witness_valid : ∀ i : Fin 60, (∀ r ∈ explicitRays i, ValidRay i r) ∧
    ∀ B ∈ explicitBases i, ValidBasis i B := by native_decide

theorem valid_shape (i : Fin 60) (r : ORow) (h : ValidRay i r) :
    ∃ t, r=0::t ∧ t.length=9 := by
  obtain ⟨h0,hl,_⟩ := h
  cases r with
  | nil => simp at hl
  | cons a t =>
    have : a=0 := by simpa using h0
    subst a
    exact ⟨t,rfl,by simpa using hl⟩

end MUB10Oct.Sixty
