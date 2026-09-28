-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/task_intra_interference_bound.v

import Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta
import Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
import Prosa.Analysis.Definitions.Sbf.Busy
import Prosa.Analysis.Definitions.Workload.Bounded
import Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix

namespace Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.ServiceInversion.Pred
open Prosa.Analysis.Definitions.Workload.Bounded
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.AbstractRta
open Prosa.Analysis.Abstract.IBF.SupplyTask
open Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Behavior.Completion

/-! The task intra-supply interference bound of the restricted-supply analysis:
the sum of a bound on service inversion and a bound on the
higher-or-equal-priority workload of other tasks.

Binders follow the elaborated source types: the lemma takes only the section
inputs and hypotheses it uses, in their elaborated order (the unused
sequential-tasks hypothesis is absent, as in the elaborated type); instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
The source's section-local instances `rs_jlfp_interference` and
`rs_jlfp_interfering_workload` re-expose the accepted restricted-supply
instantiation; they are the accepted definitions of the same names, passed
explicitly where the elaborated statement uses them implicitly. The service
inversion bound is the classical one of
`analysis/definitions/service_inversion/busy_prefix.v` (the name the
elaborated type resolves to). -/

/-- The interference bound: service inversion plus the higher-or-equal-priority
workload of other tasks. -/
def task_intra_IBF (service_inversion_bound : duration → duration)
    (athep_workload_bound : duration → duration → duration) (A R : duration) : Nat :=
  service_inversion_bound A + athep_workload_bound A R

/-- `task_intra_IBF` bounds the cumulative task intra-supply interference. -/
theorem instantiated_task_intra_interference_is_bounded {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [Cost : JobCost Job] [JobArrival Job] [JobTask Job Task]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (tsk : Task) (service_inversion_bound : duration → duration),
      Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_is_bounded_by arr_seq sched tsk
        service_inversion_bound →
    ∀ athep_workload_bound : duration → duration → duration,
      athep_workload_is_bounded arr_seq sched tsk athep_workload_bound →
      @task_intra_interference_is_bounded_by Job _ Task _ _ _ _ PState arr_seq sched tsk
        (rs_jlfp_interference arr_seq sched) (rs_jlfp_interfering_workload arr_seq sched)
        (task_intra_IBF service_inversion_bound athep_workload_bound) := by
  intro huni hsup hcons JLFP hrefl arr_seq hva sched hfrom hmust hcde tsk SIB hSIB AWB hAWB
  unfold task_intra_interference_is_bounded_by cond_interference_is_bounded_by
  intro t1 t2 Δ j harr htsk hbusy hlt hnc A hA
  have hEq : A = job_arrival j - t1 := hA t1 t2 hbusy
  subst hEq
  have hu := unit_supply_is_unit_service PState hsup
  have hposb := incomplete_implies_positive_cost sched j (t1 + Δ) hnc
  have hpos : 0 < job_cost j := by unfold job_cost_positive at hposb; exact of_decide_eq_true hposb
  refine Nat.le_trans (cumulative_task_interference_split huni hcons arr_seq hva sched hfrom hmust hrefl tsk j t1
    (t1 + Δ) harr htsk hnc) ?_
  unfold task_intra_IBF
  apply Nat.add_le_add
  · have hpref := abstract_busy_interval_classic_busy_interval_prefix huni hsup hcons arr_seq hva sched hfrom
      hmust hcde hrefl j harr t1 t2 hbusy
    have hb := hSIB j harr htsk hpos t1 t2 hpref
    refine Nat.le_trans ?_ hb
    unfold cumulative_service_inversion
    exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right (by omega'))
  · have hq := abstract_busy_interval_classic_quiet_time huni hsup hcons arr_seq hva sched hfrom hmust hcde
      hrefl j harr t1 t2 hbusy
    rw [cumulative_i_thep_eq_service_of_othep huni arr_seq hva sched hmust hcde JLFP hu j t1 (t1 + Δ) hq]
    refine Nat.le_trans (service_of_jobs_le_workload hu sched hcde _ _ t1 (t1 + Δ)) ?_
    exact hAWB j t1 Δ hposb htsk hq

end Prosa.Analysis.Abstract.RestrictedSupply.TaskIntraInterferenceBound
