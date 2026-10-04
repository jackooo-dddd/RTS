-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/task_ibf_readiness.v

import Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness
import Prosa.Analysis.Definitions.Workload.Bounded

namespace Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.ReadinessInterference
open Prosa.Analysis.Definitions.ServiceInversion
open Prosa.Analysis.Definitions.Workload.Bounded
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.IBF.SupplyTask
open Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness
open Prosa.Analysis.Facts.Interference
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open scoped BigOperators

/-! The task intra-supply interference bound of the readiness-aware restricted-supply analysis: the sum of bounds
on the higher-or-equal-priority workload of other tasks, on the readiness-aware service inversion and on the
readiness interference.

Binders follow the elaborated source types: the lemma takes only the section inputs and hypotheses it uses, in
their elaborated order (the unused sequential-tasks hypothesis is absent, as in the elaborated type); instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position. The source's section-local instances
`rs_jlfp_interference` and `rs_jlfp_interfering_workload` re-expose the accepted readiness-aware instantiation;
they are the accepted definitions `rs_readiness_jlfp_interference` / `rs_readiness_jlfp_interfering_workload`,
passed explicitly where the elaborated statement uses them implicitly. The service-inversion bound is the
readiness-aware one (`readiness_aware.service_inversion_is_bounded`, the name the elaborated type resolves to). -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-- The interference bound: the higher-or-equal-priority workload of other tasks, the service inversion and the
readiness interference. -/
def task_intra_IBF (service_inversion_bound : duration → duration)
    (athep_workload_bound : duration → duration → duration)
    (readiness_interference_bound : duration → duration → duration) (A R : duration) : Nat :=
  athep_workload_bound A R + service_inversion_bound A + readiness_interference_bound A R

/-- `task_intra_IBF` bounds the cumulative task intra-supply interference. -/
theorem instantiated_task_intra_interference_is_bounded {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [Cost : JobCost Job] [JobArrival Job] [JobTask Job Task]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState → fully_consuming_proc_model PState →
    ∀ [JobReady0 : JobReady Job PState] [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, valid_schedule sched arr_seq →
    ∀ (tsk : Task) (service_inversion_bound : duration → duration),
      @ReadinessAware.service_inversion_is_bounded Job _ _ _ PState _ arr_seq sched _
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        service_inversion_bound →
    ∀ athep_workload_bound : duration → duration → duration,
      athep_workload_is_bounded arr_seq sched tsk athep_workload_bound →
    ∀ readiness_interference_bound : duration → duration → duration,
      @readiness_interference_is_bounded Job _ _ _ PState _ arr_seq sched _
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        readiness_interference_bound →
      @task_intra_interference_is_bounded_by Job _ Task _ _ _ _ PState arr_seq sched tsk
        (rs_readiness_jlfp_interference arr_seq sched) (rs_readiness_jlfp_interfering_workload arr_seq sched)
        (task_intra_IBF service_inversion_bound athep_workload_bound readiness_interference_bound) := by
  intro huni hsup hcons JobReady0 JLFP hrefl arr_seq hva sched hvs tsk SIB hSIB AWB hAWB RIB hRIB
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  unfold task_intra_interference_is_bounded_by cond_interference_is_bounded_by
  intro t1 t2 Δ j harr htsk hbusy hlt hnc A hA
  have hEq : A = job_arrival j - t1 := hA t1 t2 hbusy
  subst hEq
  have hu := unit_supply_is_unit_service PState hsup
  have hposb := incomplete_implies_positive_cost sched j (t1 + Δ) hnc
  refine Nat.le_trans (cumulative_task_interference_split huni hcons arr_seq hva sched hvs tsk j t1
    (t1 + Δ) harr htsk hnc) ?_
  unfold task_intra_IBF
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · have hq := abstract_busy_interval_classic_quiet_time huni hsup arr_seq hva sched hvs hrefl j harr t1 t2 hbusy
      rw [cumulative_i_thep_eq_service_of_othep huni arr_seq hva sched hmust hcde JLFP hu j t1 (t1 + Δ) hq]
      refine Nat.le_trans (service_of_jobs_le_workload hu sched hcde _ _ t1 (t1 + Δ)) ?_
      exact hAWB j t1 Δ hposb htsk hq
    · have hb := hSIB j t1 t2 hbusy.1
      refine Nat.le_trans ?_ hb
      unfold ReadinessAware.cumulative_service_inversion
      exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right (by omega'))
  · have hb := hRIB j t1 t2 Δ (by omega') hbusy.1
    refine Nat.le_trans ?_ hb
    unfold cumulative_readiness_interference
    apply Finset.sum_le_sum
    intro t _
    cases has_supply sched t <;> cases some_hep_job_ready arr_seq sched j t <;> decide

end Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness
