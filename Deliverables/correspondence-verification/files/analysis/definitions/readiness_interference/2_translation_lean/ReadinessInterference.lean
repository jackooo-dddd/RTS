-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/readiness_interference.v

import Prosa.Model.Job.Properties
import Prosa.Model.Priority.Definitions
import Prosa.Analysis.Abstract.Definitions

namespace Prosa.Analysis.Definitions.ReadinessInterference

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Abstract.Definitions

section ReadinessInterference

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job} [JobReady Job PState]
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLFP_policy Job]

/-- Some higher-or-equal-priority job (w.r.t. `j`) that arrived by `t` is
ready at `t`. -/
def some_hep_job_ready (j : Job) (t : instant) : Bool :=
  ((arrivals_up_to arr_seq t).filter (fun j' => hep_job j' j)).any
    (fun j' => job_ready sched j' t)

/-- Instants in `[t1, t2)` without any ready higher-or-equal-priority job. -/
noncomputable def cumulative_readiness_interference (j : Job) (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (!some_hep_job_ready arr_seq sched j t).toNat

variable [Interference Job] [InterferingWorkload Job]

/-- `B` bounds the readiness interference inside any busy-interval prefix. -/
def readiness_interference_is_bounded (B : duration → duration → duration) : Prop :=
  ∀ (j : Job) (t1 t2 Δ : instant),
    t1 + Δ ≤ t2 →
    busy_interval_prefix sched j t1 t2 →
    cumulative_readiness_interference arr_seq sched j t1 (t1 + Δ) ≤
      B (job_arrival j - t1) Δ

end ReadinessInterference

end Prosa.Analysis.Definitions.ReadinessInterference
