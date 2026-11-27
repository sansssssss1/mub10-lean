import MainResult

/-! Finite coverage of octonary mates for quaternary Hadamard anchors in dimension ten. -/
namespace MUB10Oct
open MUB10Catalogue
abbrev O := Fin 8
abbrev OQ := Fin 10 → O
abbrev ORow := List O
abbrev OBasis := List ORow

def digit (x : O) : Phase := (x.val/2 : Nat)
def bit (x : O) : Bool := x.val % 2 == 1
def oct (b : Bool) (p : Phase) : O := (2*p.val + (if b then 1 else 0) : Nat)

end MUB10Oct
