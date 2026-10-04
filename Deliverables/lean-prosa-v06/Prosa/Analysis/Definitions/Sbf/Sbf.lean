-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/sbf/sbf.v

import Prosa.Behavior.Job

namespace Prosa.Analysis.Definitions.Sbf

open Prosa.Behavior.Time Prosa.Behavior.Job

/-- A supply bound function maps a duration to a guaranteed amount of work. -/
class SupplyBoundFunction where
  supply_bound_function : duration → work

end Prosa.Analysis.Definitions.Sbf
