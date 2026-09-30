-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/service_inversion/readiness_aware.v

import Prosa.Analysis.Abstract.Definitions
import Prosa.Analysis.Definitions.ReadinessInterference
import Prosa.Analysis.Definitions.ServiceInversion.Pred

namespace Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Definitions.ReadinessInterference
open scoped BigOperators

/-! Readiness-aware service inversion.

Binders follow the elaborated source types (the unused uniprocessor hypothesis is absent). The JLFP policy reaches
the JLDP-based readiness-oblivious service inversion (`pred.service_inversion`) through the accepted low-priority
`JLFP_to_JLDP` instance, as the source coercion does; the section-local abbreviation
`readiness_oblivious_service_inversion` is unfolded. Representation: the interval sum `\sum_(t1 <= t < t2) F t` is
the `Finset.Ico` sum over `Nat`; `nat_of_bool` is `Bool.toNat`; `a <= b` in `Prop` position is `a ≤ b`. -/

section ServiceInversion

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job} [JobReady Job PState]
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLFP_policy Job]

/-- `j` incurs readiness-aware service inversion at `t` if some higher-or-equal-priority job is ready and a
lower-priority job is served. -/
noncomputable def service_inversion (j : Job) (t : instant) : Bool :=
  some_hep_job_ready arr_seq sched j t &&
    Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion arr_seq sched j t

/-- The readiness-aware service inversion of `j` within `[t1, t2)`. -/
noncomputable def cumulative_service_inversion (j : Job) (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico (α := Nat) t1 t2, (service_inversion arr_seq sched j t).toNat

variable [Interference Job] [InterferingWorkload Job]

/-- `B` bounds the readiness-aware cumulative service inversion of every job within its busy-interval
prefixes. -/
def service_inversion_is_bounded (B : duration → duration) : Prop :=
  ∀ (j : Job) (t1 t2 : instant),
    busy_interval_prefix sched j t1 t2 →
      cumulative_service_inversion arr_seq sched j t1 t2 ≤ B (job_arrival j - t1)

end ServiceInversion

end Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware
