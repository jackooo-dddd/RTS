-- Translated from: util/ssromega.v

namespace Prosa.Util.Ssromega

/-- The `ssromega` tactic: in Lean 4, `omega` already handles natural number
    arithmetic directly, so `ssromega` is simply an alias for `omega`. -/
macro "ssromega" : tactic => `(tactic| omega)

end Prosa.Util.Ssromega
