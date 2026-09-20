import Mathlib

/- Validation-only smoke fixture. It is not a Prosa translation declaration
   and is excluded from production coverage. -/

set_option autoImplicit false

namespace ProsaV06WorkspaceSmoke

example : (1 : Nat) + 1 = 2 := by decide

end ProsaV06WorkspaceSmoke
