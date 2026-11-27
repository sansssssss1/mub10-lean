import OctSixtyData
import Std.Data.HashMap.Lemmas

namespace MUB10Oct.Sixty

private def words : Nat → OBasis
  | 0 => [[]]
  | n+1 => (List.finRange 8).flatMap fun d => (words n).map (d::·)

private theorem words_full (r : ORow) : r ∈ words r.length := by
  induction r with
  | nil => simp [words]
  | cons a r ih =>
    exact List.mem_flatMap.mpr ⟨a, List.mem_finRange _, List.mem_map.mpr ⟨_,ih,rfl⟩⟩

private abbrev Key := Int × Int
private abbrev Buckets := Std.HashMap Key OBasis
private def bucket (key : ORow → Key) (rs : OBasis) : Buckets :=
  rs.foldr (fun r m => m.insert (key r) (r :: m.getD (key r) [])) ∅

private theorem bucket_full (f : ORow → Key) (rs : OBasis) (r : ORow) (hr : r ∈ rs) :
    r ∈ (bucket f rs).getD (f r) [] := by
  induction rs with
  | nil => simp at hr
  | cons a rs ih =>
    change r ∈ ((bucket f rs).insert (f a) (a :: (bucket f rs).getD (f a) [])).getD (f r) []
    rw [Std.HashMap.getD_insert]
    rcases List.mem_cons.mp hr with hr|hr
    · subst a; simp
    · by_cases h : f a = f r <;> simp [h, ih hr]

private theorem score_cut (n : Nat) (h r : ORow) :
    score h r = score (h.take n) (r.take n) + score (h.drop n) (r.drop n) := by
  induction n generalizing h r with
  | zero => simp [score]
  | succ n ih =>
    cases h with
    | nil => simp [score]
    | cons a h =>
      cases r with
      | nil => simp [score]
      | cons b r =>
        simpa [score, add_assoc] using congrArg (valCode (b-a)+·) (ih h r)

private def leftWords : OBasis := (words 4).map (0::·)
private def fromPair (h k : ORow) : OBasis :=
  let f (r : ORow) : Key := (score (h.drop 5) r, score (k.drop 5) r)
  let m := bucket f (words 5)
  leftWords.flatMap fun l =>
    let a := score (h.take 5) l
    let b := score (k.take 5) l
    targets.flatMap fun u => targets.flatMap fun v =>
      (m.getD (u-a,v-b) []).map (l++·)

private theorem fromPair_full (h k r : ORow) (hn : ∃ t, r=0::t ∧ t.length=9)
    (hh : score h r ∈ targets) (hk : score k r ∈ targets) : r ∈ fromPair h k := by
  have hl : r.take 5 ∈ leftWords := by
    obtain ⟨t,rfl,ht⟩ := hn
    exact List.mem_map.mpr ⟨_, by simpa [ht] using words_full (t.take 4), rfl⟩
  have hr : r.drop 5 ∈ words 5 := by
    obtain ⟨t,rfl,ht⟩ := hn
    simpa [ht] using words_full ((0::t).drop 5)
  have eh : score h r - score (h.take 5) (r.take 5) = score (h.drop 5) (r.drop 5) := by
    rw [score_cut 5 h r]; omega
  have ek : score k r - score (k.take 5) (r.take 5) = score (k.drop 5) (r.drop 5) := by
    rw [score_cut 5 k r]; omega
  unfold fromPair
  refine List.mem_flatMap.mpr ⟨_,hl,List.mem_flatMap.mpr
    ⟨_,hh,List.mem_flatMap.mpr ⟨_,hk,List.mem_map.mpr ⟨r.drop 5,?_,List.take_append_drop 5 r⟩⟩⟩⟩
  rw [eh,ek]
  exact bucket_full _ _ _ hr

private def row (i : Fin 60) (n : Nat) : ORow := (catalogue8 i).getD n []
private def twoRep (g : Fin 4) : Fin 60 := #[0,50,55,58].getD g.val 0
private def twoGroup (i : Fin 60) : Fin 4 :=
  if i.val < 50 then 0 else if i.val < 55 then 1 else if i.val < 58 then 2 else 3

private def threeRep (g : Fin 24) : Fin 60 :=
  #[0,11,26,31,32,33,34,35,36,40,42,45,47,48,50,51,52,53,54,55,56,57,58,59].getD g.val 0
private def threeGroup (i : Fin 60) : Fin 24 :=
  #[0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,
    4,5,6,7,8,8,8,8,9,9,10,10,10,11,11,12,13,13,14,15,16,17,18,19,20,21,22,23].getD i.val 0

private def seedsTwo : List OBasis := List.ofFn fun g : Fin 4 =>
  fromPair (row (twoRep g) 0) (row (twoRep g) 1)

private def seedsThree : List OBasis := List.ofFn fun g : Fin 24 =>
  let i := threeRep g
  let rs := seedsTwo.getD (twoGroup i).val []
  rs.filter fun r => targets.contains (score (row i 2) r)

def octPool (i : Fin 60) : OBasis :=
  (seedsThree.getD (threeGroup i).val []).filter fun r =>
    (catalogue8 i).all fun h => targets.contains (score h r)

private theorem origins : ∀ i : Fin 60,
    let g := threeRep (threeGroup i)
    let k := twoRep (twoGroup g)
    row k 0 ∈ catalogue8 i ∧ row k 1 ∈ catalogue8 i ∧ row g 2 ∈ catalogue8 i := by native_decide

private theorem get_ofFn {n} {α} (f : Fin n → α) (i : Fin n) (a : α) :
    (List.ofFn f).getD i.val a = f i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos i.isLt,Option.getD_some]

theorem octPool_full (i : Fin 60) (r : ORow) (hn : ∃ t, r=0::t ∧ t.length=9)
    (hu : ∀ h ∈ catalogue8 i, score h r ∈ targets) : r ∈ octPool i := by
  apply List.mem_filter.mpr
  refine ⟨?_, List.all_eq_true.mpr (fun h hh => by simpa using hu h hh)⟩
  simp only [seedsThree,get_ofFn]
  apply List.mem_filter.mpr
  refine ⟨?_,by simpa using hu _ (origins i).2.2⟩
  simp only [seedsTwo,get_ofFn]
  exact fromPair_full _ _ _ hn (hu _ (origins i).1) (hu _ (origins i).2.1)

end MUB10Oct.Sixty
