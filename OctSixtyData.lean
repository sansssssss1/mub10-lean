import OctBasics

namespace MUB10Oct.Sixty

def valCode (e : O) : Int :=
  #[1,1024,32,32768,-1,-1024,-32,-32768].getD e.val 0

def score (h r : ORow) : Int :=
  (List.zipWith (fun x y : O => valCode (y-x)) h r).sum

def targets : List Int :=
  let z : List Int := [97,-95,95,-97,35,-29,29,-35]
  z ++ z.map (· * 1024)

private def rawCatalogue := include_str "BH-10-8.txt"

def catalogue8Rows : List OBasis :=
  ((rawCatalogue.replace "\r" "").trim.splitOn "\n").map fun line =>
    let digits : ORow := (line.toList.drop 6).map fun c => ((c.toNat - '0'.toNat : Nat) : O)
    (List.range 10).map fun r => (digits.drop (10*r)).take 10

def catalogue8 (i : Fin 60) : OBasis := catalogue8Rows.getD i.val []

theorem catalogue8_shape : catalogue8Rows.length = 60 ∧ ∀ i : Fin 60,
    (catalogue8 i).length = 10 ∧ ∀ h ∈ catalogue8 i, h.length = 10 := by native_decide

end MUB10Oct.Sixty
