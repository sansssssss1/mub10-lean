import OctPacked

namespace MUB10Oct.Sixty

private def collect {α β : Type} (f : α → List β) (xs : List α) :=
  ((xs.map (fun x => Task.spawn (fun _ => f x))).map Task.get).flatten

private theorem collect_eq {α β : Type} (f : α → List β) (xs : List α) :
    collect f xs = xs.flatMap f := by
  unfold collect
  simp only [List.map_map]
  rfl

def joined : OBasis → List OBasis := collect leavesWith

theorem joined_eq (rows : OBasis) : joined rows = rows.flatMap leavesWith :=
  collect_eq leavesWith rows

end MUB10Oct.Sixty
