import ComplexBridge
import Monomials
import PolyCheck

namespace MUB10.Certificate
open PolyCheck

structure Multiplier where
  row : Fin 20
  key : Nat
  coeff : Coeff

-- A parsing default can only change the candidate certificate. Its full
-- expansion is checked below against a nonzero constant.
def readWeight (s : String) : Coeff :=
  match s.splitOn " " with
  | [a,b] => (a.toInt?.getD 0, b.toInt?.getD 0)
  | _ => (0,0)

def weights : Array Coeff :=
  ((((include_str "weights.txt").replace "\r" "").trim.splitOn "\n").map readWeight).toArray

def readMultiplier (s : String) : Multiplier :=
  match s.splitOn " " with
  | [r,m,w] => ⟨Fin.ofNat' 20 (r.toNat?.getD 0), m.toNat?.getD 0,
      weights[w.toNat?.getD 0]?.getD (0,0)⟩
  | _ => ⟨0,0,(0,0)⟩

def pages : List (List (List Multiplier)) :=
  ((((include_str "multipliers.txt").replace "\r" "").trim.splitOn "\n\n").map fun page =>
    (page.splitOn "\n").map fun line => (line.splitOn ";").map readMultiplier)

def rot (n : Nat) (c : Coeff) : Coeff :=
  match n with
  | 0 => c
  | 1 => (-c.2, c.1)
  | 2 => (-c.1, -c.2)
  | _ => (c.2, -c.1)

def SafeKey (m : Nat) : Prop := ∀ q : Fin 10, -2 ≤ digit m q ∧ digit m q ≤ 2

instance (m : Nat) : Decidable (SafeKey m) := by unfold SafeKey; infer_instance

def elementary (w : Multiplier) (j k : Fin 10) : Term :=
  if j = k then (center,(0,0)) else
    (stepKey w.key j k, rot ((phase w.row.val k + 4 - phase w.row.val j) % 4) w.coeff)

def expand (w : Multiplier) : List Term :=
  if SafeKey w.key then (List.ofFn fun j => List.ofFn (elementary w j)).flatten else []

def block (xs : List Multiplier) := compress (xs.flatMap expand)
def page (xs : List (List Multiplier)) := compress (xs.flatMap block)
def polynomial := compress (pages.flatMap page)

def constantValue : Nat :=
  4088025093986974733066685159265928378515297600450045180418354602820446241179955179855400100887976407901284800975735311292079121142429802007760702558121633823379009129789432707702115834759067553577049289825091501644422838803226250189720218708450559937642332781345938481094192783239141807498437592580579369408000000

set_option maxRecDepth 100000 in
theorem exact_certificate : polynomial = [(center, ((constantValue : Int),0))] := by
  native_decide

end MUB10.Certificate
