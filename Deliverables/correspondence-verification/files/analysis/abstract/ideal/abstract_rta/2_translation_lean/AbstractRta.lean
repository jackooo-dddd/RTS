-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/ideal/abstract_rta.v

import Prosa.Analysis.Abstract.AbstractRta
import Prosa.Analysis.Abstract.IwAuxiliary
import Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
import Prosa.Model.Processor.PlatformProperties

namespace Prosa.Analysis.Abstract.Ideal.AbstractRta

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.SearchSpace
open Prosa.Analysis.Abstract.BusyInterval
open Prosa.Analysis.Abstract.IwAuxiliary
open Prosa.Analysis.Abstract.LowerBoundOnService
open Prosa.Analysis.Abstract.AbstractRta

/-! Abstract response-time analysis for the ideal-progress processor model.
Binders follow the elaborated source types: every theorem takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `tsk \in ts` is
`decide (tsk ∈ ts) = true`. -/

section AbstractRTAIdeal

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskRunToCompletionThreshold Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
  [JobPreemptable Job]
variable {PState : ProcessorState Job}

/-- In the non-preemptive stage an ideal-progress job incurs no further
interference, so `IBF_NP F Δ := F - task_rtct tsk` bounds its interference. -/
theorem nonpreemptive_interference_is_bounded :
    ideal_progress_proc_model PState → unit_service_proc_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState),
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [Interference Job] [InterferingWorkload Job],
      work_conserving arr_seq sched →
    ∀ interference_bound_function : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk (fun F _ => F - task_rtct tsk)
        (relative_time_to_reach_rtct sched tsk interference_bound_function) := by
  intro hideal hunit arr_seq sched harr hcomp ts tsk _ hvalid hrtc _ _ hwc ibf
  intro t1 t2 Δ j ha hjt hbi hlt hnc F hrel
  obtain ⟨hfix, hsvc⟩ := hrel t1 t2 hbi
  have hpos' : job_cost j > 0 := by
    simp only [completed_by, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hnc
    omega'
  have hpos : job_cost_positive j = true := decide_eq_true hpos'
  have ⟨⟨⟨hle1, hle2⟩, _, _⟩, _⟩ := hbi
  change cumulative_interference j t1 (t1 + Δ) ≤ F - task_rtct tsk
  -- the busy interval of [j] has length at least the first-stage bound
  have hsvc_le : service sched j t1 = 0 := by
    have h := no_service_before_busy_interval sched harr j hpos t1 t2 hbi t1
    rw [h]; simp [service_during]
  have hbound : ∀ δ, t1 + δ ≤ t2 →
      service_during sched j t1 (t1 + δ) + cumulative_interference j t1 (t1 + δ) ≤ δ :=
    fun δ hδ => service_and_interference_bounded arr_seq sched tsk hwc j ha hjt hpos t1 t2 hbi.1
      t1 δ (Nat.le_refl _) hδ hunit
  have hcat := fun δ => service_cat sched j t1 (t1 + δ) (Nat.le_add_right t1 δ)
  rcases Nat.lt_or_ge (t1 + F) t2 with hF | hF
  · rcases Nat.le_total F Δ with hFD | hDF
    · -- no interference once the job has become non-preemptive
      have hzero : cumul_cond_interference (fun _ _ => true) j (t1 + F) (t1 + Δ) = 0 := by
        unfold cumul_cond_interference
        apply Finset.sum_eq_zero
        intro t ht
        rw [Finset.mem_Ico] at ht
        have hsched : scheduled_at sched j t = true := by
          apply job_nonpreemptive_after_run_to_completion_threshold arr_seq sched hvalid j ha
            (t1 + F) t ht.1
          · exact Nat.le_trans (hrtc.2 j ha hjt) hsvc
          · have := completion_monotonic sched j t (t1 + Δ) (Nat.le_of_lt ht.2)
            cases hc : completed_by sched j t
            · rfl
            · rw [hc] at this
              have := this rfl
              rw [this] at hnc
              exact absurd hnc (by decide)
        have hserv : receives_service_at sched j t = true := by
          unfold receives_service_at service_at
          exact decide_eq_true (hideal j (sched t) hsched)
        have hw := hwc j t1 t2 t ha hpos' hbi.1 ⟨by omega', by omega'⟩
        unfold cond_interference
        cases hi : interference j t
        · rfl
        · exact absurd hi (hw.mpr hserv)
      have hsplit := cumulative_interference_cat (fun _ _ => true) j (t1 + F) t1 (t1 + Δ)
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      have hb := hbound F (Nat.le_of_lt hF)
      have hc := hcat F
      unfold cumulative_interference at hb ⊢
      omega'
    · have hsub := cumulative_interference_sub (fun _ _ => true) j t1 (t1 + Δ) t1 (t1 + F)
        (Nat.le_refl _) (by omega')
      have hb := hbound F (Nat.le_of_lt hF)
      have hc := hcat F
      unfold cumulative_interference at hb ⊢
      omega'
  · -- the first-stage solution lies beyond the busy interval
    have hcost := service_within_busy_interval_ge_job_cost sched harr j hpos t1 t2 hbi
    have hmost := service_at_most_cost sched hcomp j hunit (t1 + F)
    have hsub := cumulative_interference_sub (fun _ _ => true) j t1 (t1 + Δ) t1 t2
      (Nat.le_refl _) (by omega')
    have hb := hbound (t2 - t1) (by omega')
    have ht2 : t1 + (t2 - t1) = t2 := by omega'
    rw [ht2] at hb
    unfold cumulative_interference at hb ⊢
    omega'

/-- `R` bounds the response time of the jobs of `tsk` under the ideal-progress
processor model. -/
theorem uniprocessor_response_time_bound_ideal :
    ideal_progress_proc_model PState → unit_service_proc_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState),
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [Interference Job] [InterferingWorkload Job],
      work_conserving arr_seq sched →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ interference_bound_function : duration → duration → duration,
      job_interference_is_bounded_by arr_seq sched tsk interference_bound_function
        (relative_arrival_time_of_job_is_A sched) →
    ∀ R : duration,
      (∀ A : Nat, is_in_search_space L interference_bound_function A →
        ∃ F : Nat, task_rtct tsk + interference_bound_function A (A + F) ≤ A + F ∧
          F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hideal hunit arr_seq sched harr hcomp hvalid ts tsk hts hpm hrtc _ _ hwc L hL ibf hP R hmax
  have hle : task_rtct tsk ≤ task_cost tsk := of_decide_eq_true hrtc.1
  refine uniprocessor_response_time_bound arr_seq sched hvalid ts tsk hts hwc L hL ibf hP
    (fun F _ => F - task_rtct tsk)
    (nonpreemptive_interference_is_bounded hideal hunit arr_seq sched harr hcomp ts tsk hts hpm hrtc
      hwc ibf)
    (fun F _ => by omega') R ?_
  intro A hsp
  obtain ⟨F, h1, h2⟩ := hmax A hsp
  exact ⟨A + F, h1, by omega'⟩

end AbstractRTAIdeal

end Prosa.Analysis.Abstract.Ideal.AbstractRta
