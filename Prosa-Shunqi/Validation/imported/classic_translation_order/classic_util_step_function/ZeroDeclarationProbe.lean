import Prosa.Classic.Util.StepFunction
import Lean
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `Prosa.Classic.Util.StepFunction | throwError "module missing"
  IO.println s!"ZERO_DECLARATION_PROBE {(env.header.moduleData[idx.toNat]!).constNames.size}"
