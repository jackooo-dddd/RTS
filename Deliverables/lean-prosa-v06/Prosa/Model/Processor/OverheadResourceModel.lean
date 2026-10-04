-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/overhead_resource_model.v

import Prosa.Model.Processor.Overheads
import Prosa.Analysis.Definitions.Overheads.ScheduleChange
import Prosa.Analysis.Facts.Model.Overheads.ScheduleChange

namespace Prosa.Model.Processor.OverheadResourceModel

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Overheads
open Prosa.Analysis.Definitions.Overheads.ScheduleChange

/-! A scheduling model with overheads inspired by real-world uniprocessor OS implementations: the time a
job (or the idle thread, `none`) spends in each kind of overhead, bounds on these times while the scheduled
job does not change, and the temporal ordering of the overhead phases. -/

variable {Job : JobType} [DecidableEq Job]

/-- Time spent in dispatch overhead by the job `oj` (or the idle thread) during `[t1, t2)`. -/
noncomputable def time_spent_in_dispatch (sched : schedule (processor_state Job)) (oj : Option Job)
    (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (decide (scheduled_job sched t = oj) && is_dispatch sched t).toNat

/-- Time spent in context-switch overhead by `oj` during `[t1, t2)`. -/
noncomputable def time_spent_in_context_switch (sched : schedule (processor_state Job)) (oj : Option Job)
    (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (decide (scheduled_job sched t = oj) && is_context_switch sched t).toNat

/-- Time spent in cache-related preemption delay by `oj` during `[t1, t2)`. -/
noncomputable def time_spent_in_CRPD (sched : schedule (processor_state Job)) (oj : Option Job)
    (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (decide (scheduled_job sched t = oj) && is_CRPD sched t).toNat

/-- While the same job (or idle) is continuously scheduled, dispatch overhead is at most `DB`. -/
def time_spent_in_dispatch_is_bounded_by (sched : schedule (processor_state Job)) (DB : Nat) : Prop :=
  ∀ (t1 t2 : instant) (oj : Option Job),
    scheduled_job_invariant sched oj t1 t2 = true → time_spent_in_dispatch sched oj t1 t2 ≤ DB

/-- While the same job (or idle) is continuously scheduled, context-switch overhead is at most `CSB`. -/
def time_spent_in_context_switch_is_bounded_by (sched : schedule (processor_state Job)) (CSB : Nat) : Prop :=
  ∀ (t1 t2 : instant) (oj : Option Job),
    scheduled_job_invariant sched oj t1 t2 = true → time_spent_in_context_switch sched oj t1 t2 ≤ CSB

/-- While the same job (or idle) is continuously scheduled, CRPD overhead is at most `CRPDB`. -/
def time_spent_in_CRPD_is_bounded_by (sched : schedule (processor_state Job)) (CRPDB : Nat) : Prop :=
  ∀ (t1 t2 : instant) (oj : Option Job),
    scheduled_job_invariant sched oj t1 t2 = true → time_spent_in_CRPD sched oj t1 t2 ≤ CRPDB

/-- Within an invariant stretch, no context switch happens up to a dispatch instant. -/
def dispatch_precedes_context_switch (sched : schedule (processor_state Job)) : Prop :=
  ∀ (oj : Option Job) (t1 t2 : instant), scheduled_job_invariant sched oj t1 t2 = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → is_dispatch sched t = true →
      ∀ t' : Nat, (decide (t1 ≤ t') && decide (t' ≤ t)) = true → (!is_context_switch sched t') = true

/-- Within an invariant stretch, no progress happens up to a context-switch instant. -/
def context_switch_precedes_progress (sched : schedule (processor_state Job)) : Prop :=
  ∀ (oj : Option Job) (t1 t2 : instant), scheduled_job_invariant sched oj t1 t2 = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → is_context_switch sched t = true →
      ∀ t' : Nat, (decide (t1 ≤ t') && decide (t' ≤ t)) = true → (!is_progress sched t') = true

/-- Within an invariant stretch, no CRPD happens up to a context-switch instant. -/
def context_switch_precedes_CRPD (sched : schedule (processor_state Job)) : Prop :=
  ∀ (oj : Option Job) (t1 t2 : instant), scheduled_job_invariant sched oj t1 t2 = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → is_context_switch sched t = true →
      ∀ t' : Nat, (decide (t1 ≤ t') && decide (t' ≤ t)) = true → (!is_CRPD sched t') = true

/-- The overhead resource model: bounded overheads of each kind and the ordering of the overhead phases. -/
def overhead_resource_model (sched : schedule (processor_state Job)) (DB CSB CRPDB : duration) : Prop :=
  time_spent_in_dispatch_is_bounded_by sched DB ∧
  time_spent_in_context_switch_is_bounded_by sched CSB ∧
  time_spent_in_CRPD_is_bounded_by sched CRPDB ∧
  dispatch_precedes_context_switch sched ∧
  context_switch_precedes_progress sched ∧
  context_switch_precedes_CRPD sched

end Prosa.Model.Processor.OverheadResourceModel
