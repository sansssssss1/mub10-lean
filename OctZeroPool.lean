import OctSixtyData
import Std.Data.HashMap.Lemmas

namespace MUB10Oct.Sixty.Zero

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
def fromPair (h k : ORow) : OBasis :=
  let f (r : ORow) : Key := (score (h.drop 5) r, score (k.drop 5) r)
  let m := bucket f (words 5)
  leftWords.flatMap fun l =>
    let a := score (h.take 5) l
    let b := score (k.take 5) l
    (m.getD (0-a,0-b) []).map (l++·)

theorem fromPair_full (h k r : ORow) (hn : ∃ t, r=0::t ∧ t.length=9)
    (hh : score h r = 0) (hk : score k r = 0) : r ∈ fromPair h k := by
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
  refine List.mem_flatMap.mpr ⟨_,hl,List.mem_map.mpr ⟨r.drop 5,?_,List.take_append_drop 5 r⟩⟩
  rw [hh] at eh
  rw [hk] at ek
  rw [eh,ek]
  exact bucket_full _ _ _ hr

end MUB10Oct.Sixty.Zero
