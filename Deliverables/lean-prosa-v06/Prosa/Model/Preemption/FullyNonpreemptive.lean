-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/preemption/fully_nonpreemptive.v

import Prosa.Model.Preemption.Parameter

/-!
The authoritative module has no public declaration: it re-exports
`model/preemption/parameter.v` and declares, inside a section, the
`#[local] Instance fully_nonpreemptive_job_model` (a named constant whose
instance registration is section-local; later source files enable it with
`#[local] Existing Instance`). Its Lean counterpart is the plain definition
below, which later translations enable locally in the same way.
-/

namespace Prosa.Model.Preemption.FullyNonpreemptive

open Prosa.Behavior.Job
open Prosa.Model.Preemption.Parameter

/-- No job can be preempted until its completion: preemption is possible
only at progress `0` or at the job's cost. -/
@[reducible] def fully_nonpreemptive_job_model {Job : JobType} [DecidableEq Job] [JobCost Job] :
    JobPreemptable Job where
  job_preemptable j ρ := decide (ρ = 0) || decide (ρ = job_cost j)

end Prosa.Model.Preemption.FullyNonpreemptive
