-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/preemption/fully_preemptive.v

import Prosa.Model.Preemption.Parameter

/-!
The authoritative module has no public declaration: it re-exports
`model/preemption/parameter.v` and declares, inside a section, the
`#[local] Instance fully_preemptive_job_model` (a named constant whose
instance registration is section-local; later source files enable it with
`#[local] Existing Instance`). Its Lean counterpart is the plain definition
below, which later translations enable locally in the same way.
-/

namespace Prosa.Model.Preemption.FullyPreemptive

open Prosa.Behavior.Job
open Prosa.Model.Preemption.Parameter

/-- Any job may be preempted at any time. -/
@[reducible] def fully_preemptive_job_model {Job : JobType} [DecidableEq Job] :
    JobPreemptable Job where
  job_preemptable _ _ := true

end Prosa.Model.Preemption.FullyPreemptive
