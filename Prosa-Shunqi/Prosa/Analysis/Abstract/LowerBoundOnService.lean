-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/lower_bound_on_service.v

import Prosa.Analysis.Facts.Model.ServiceOfJobs
import Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
import Prosa.Analysis.Abstract.Definitions
import Prosa.Analysis.Abstract.BusyInterval

namespace Prosa.Analysis.Abstract.LowerBoundOnService

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.BusyInterval
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Util.Sum
open scoped BigOperators

/-! Lower bound on the service of a job within an abstract busy interval.
Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order (the unused task-cost
and preemption context and the arrival hypotheses are absent). Representation:
a Boolean in `Prop` position is `= true`. -/

section LowerBoundOnService

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}

theorem interference_is_complement_to_schedule (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (tsk : Task) [Interference Job] [InterferingWorkload Job] :
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
      ∀ t1 t2 : instant, busy_interval_prefix sched j t1 t2 →
        ∀ (t : instant) (δ : duration), t1 ≤ t → t + δ ≤ t2 →
          δ ≤ service_during sched j t (t + δ) + cumulative_interference j t (t + δ) := by
  intro hwc j ha _ hpos t1 t2 hpre t δ h1 h2
  have hpos' : job_cost j > 0 := of_decide_eq_true hpos
  unfold service_during cumulative_interference cumul_cond_interference
  rw [← Finset.sum_add_distrib]
  calc δ = ∑ x ∈ Finset.Ico t (t + δ), (1 : Nat) := (sum_of_ones t δ).symm
    _ ≤ ∑ x ∈ Finset.Ico t (t + δ),
          (service_at sched j x + (cond_interference (fun _ _ => true) j x).toNat) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_Ico] at hx
        have hw := hwc j t1 t2 x ha hpos' hpre ⟨by omega', by omega'⟩
        unfold cond_interference
        simp only [Bool.true_and]
        cases hi : interference j x
        · have hr := hw.mp (by rw [hi]; simp)
          unfold receives_service_at at hr
          have := of_decide_eq_true hr
          simp only [Bool.toNat_false]
          omega'
        · simp only [Bool.toNat_true]
          omega'

theorem service_and_interference_bounded (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (tsk : Task) [Interference Job] [InterferingWorkload Job] :
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
      ∀ t1 t2 : instant, busy_interval_prefix sched j t1 t2 →
        ∀ (t : instant) (δ : duration), t1 ≤ t → t + δ ≤ t2 →
          unit_service_proc_model PState →
          service_during sched j t (t + δ) + cumulative_interference j t (t + δ) ≤ δ := by
  intro hwc j ha _ hpos t1 t2 hpre t δ h1 h2 hunit
  have hpos' : job_cost j > 0 := of_decide_eq_true hpos
  unfold service_during cumulative_interference cumul_cond_interference
  rw [← Finset.sum_add_distrib]
  calc ∑ x ∈ Finset.Ico t (t + δ), (service_at sched j x + (cond_interference (fun _ _ => true) j x).toNat)
      ≤ ∑ x ∈ Finset.Ico t (t + δ), (1 : Nat) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mem_Ico] at hx
        have hw := hwc j t1 t2 x ha hpos' hpre ⟨by omega', by omega'⟩
        unfold cond_interference
        simp only [Bool.true_and]
        cases hi : interference j x
        · have hs : service_at sched j x ≤ 1 := hunit j (sched x)
          simp only [Bool.toNat_false]
          omega'
        · have hns : ¬ receives_service_at sched j x = true := fun hr => (hw.mpr hr) hi
          unfold receives_service_at at hns
          have : service_at sched j x = 0 := by
            by_contra hne
            exact hns (decide_eq_true (Nat.pos_of_ne_zero hne))
          simp only [this, Bool.toNat_true]
          omega'
    _ = δ := sum_of_ones t δ

theorem j_receives_enough_service (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (tsk : Task) [Interference Job] [InterferingWorkload Job] :
    work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
      ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
        ∀ progress_of_job : duration, progress_of_job ≤ job_cost j →
          ∀ δ : duration, progress_of_job + cumulative_interference j t1 (t1 + δ) ≤ δ →
            progress_of_job ≤ service sched j (t1 + δ) := by
  intro hwc j ha hjt hpos t1 t2 hbi p hp δ hbound
  by_cases hle : t1 + δ ≤ t2
  · have hc := interference_is_complement_to_schedule arr_seq sched tsk hwc j ha hjt hpos t1 t2 hbi.1
      t1 δ (Nat.le_refl _) hle
    have hcat := service_cat sched j t1 (t1 + δ) (Nat.le_add_right t1 δ)
    omega'
  · have hcompl := job_completes_within_busy_interval sched j t1 t2 hbi
    unfold completed_by at hcompl
    have hc := of_decide_eq_true hcompl
    have hcat := service_cat sched j t2 (t1 + δ) (by omega')
    omega'

end LowerBoundOnService

end Prosa.Analysis.Abstract.LowerBoundOnService
