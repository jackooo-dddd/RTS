import Prosa.Util.Int

namespace Prosa.Validation.IntModuleInterface

/-!
Actual compiled-interface probe for the zero-declaration `util/int.v`
translation boundary.  Every declaration below is validation-only.
-/

def carrier : Type := Int
def ofNat (n : Nat) : Int := Int.ofNat n
def negSucc (n : Nat) : Int := Int.negSucc n
def add (x y : Int) : Int := x + y
def sub (x y : Int) : Int := x - y
def le (x y : Int) : Prop := x ≤ y
def lt (x y : Int) : Prop := x < y

example : CommRing Int := inferInstance
example : LinearOrder Int := inferInstance
example : IsStrictOrderedRing Int := inferInstance
example : DecidableEq Int := inferInstance

end Prosa.Validation.IntModuleInterface

#print axioms Prosa.Validation.IntModuleInterface.carrier
#print axioms Prosa.Validation.IntModuleInterface.ofNat
#print axioms Prosa.Validation.IntModuleInterface.negSucc
#print axioms Prosa.Validation.IntModuleInterface.add
#print axioms Prosa.Validation.IntModuleInterface.sub
#print axioms Prosa.Validation.IntModuleInterface.le
#print axioms Prosa.Validation.IntModuleInterface.lt
