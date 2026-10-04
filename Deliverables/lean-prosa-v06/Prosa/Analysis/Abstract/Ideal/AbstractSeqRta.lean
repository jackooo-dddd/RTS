-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/ideal/abstract_seq_rta.v

import Prosa.Analysis.Definitions.TaskSchedule
import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Facts.Model.TaskArrivals
import Prosa.Analysis.Facts.Model.TaskSchedule
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Analysis.Abstract.Ideal.AbstractRta
import Prosa.Analysis.Abstract.IBF.Task

namespace Prosa.Analysis.Abstract.Ideal.AbstractSeqRta

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Processor.PlatformProperties
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.SearchSpace
open Prosa.Analysis.Abstract.AbstractRta
open Prosa.Analysis.Abstract.Ideal.AbstractRta
open Prosa.Analysis.Abstract.IBF.Task

/-! Abstract response-time analysis for uniprocessors with sequential tasks.
Binders follow the elaborated source types: every declaration takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `tsk \in ts` is
`decide (tsk ∈ ts) = true`; `ε` is `1`; the source's `search_space`-qualified
`is_in_search_space` is the abstract search space; the section `Let`s
`task_rbf` and `total_interference_bound` are inlined. -/

section SequentialAbstractRTA

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- The sequential response-time recurrence implies the recurrence of the
general ideal abstract RTA, provided the arrival curve is not pathological. -/
theorem max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis [TaskCost Task]
    [TaskRunToCompletionThreshold Task] [JobTask Job Task] [JobCost Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals →
    ∀ (L : duration) (task_IBF : duration → duration → duration) (R : duration),
      (∀ A : duration,
        is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk + task_IBF A0 Δ) A →
        ∃ F : duration,
          task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk) + task_IBF A (A + F) ≤
            A + F ∧
          F + (task_cost tsk - task_rtct tsk) ≤ R) →
      0 < max_arrivals tsk 1 →
      ∀ A : duration,
        is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk + task_IBF A0 Δ) A →
        ∃ F : duration,
          task_rtct tsk + (task_request_bound_function tsk (A + 1) - task_cost tsk + task_IBF A (A + F)) ≤
            A + F ∧
          F + (task_cost tsk - task_rtct tsk) ≤ R := by
  intro hin hrtc _ hvac L task_IBF R hmax hpos A hA
  obtain ⟨F, h1, h2⟩ := hmax A hA
  refine ⟨F, ?_, h2⟩
  have hle : task_rtct tsk ≤ task_cost tsk := of_decide_eq_true hrtc.1
  have hc1 : task_cost tsk ≤ task_request_bound_function tsk 1 := task_rbf_1_ge_task_cost tsk hpos
  have hmono := of_decide_eq_true
    (task_rbf_monotone tsk (hvac tsk hin) 1 (A + 1) (decide_eq_true (by omega')))
  omega'

/-- `R` bounds the response time of the jobs of `tsk` under sequential tasks. -/
theorem uniprocessor_response_time_bound_seq [TaskCost Task] [TaskRunToCompletionThreshold Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] [JobPreemptable Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_service_proc_model PState → ideal_progress_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals →
      taskset_respects_max_arrivals arr_seq ts →
    ∀ [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ L : duration, busy_intervals_are_bounded_by arr_seq sched tsk L →
    ∀ task_IBF : duration → duration → duration,
      task_interference_is_bounded_by arr_seq sched tsk task_IBF →
    ∀ R : duration,
      (∀ A : duration,
        is_in_search_space L
          (fun A0 Δ => task_request_bound_function tsk (A0 + 1) - task_cost tsk + task_IBF A0 Δ) A →
        ∃ F : duration,
          task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk) + task_IBF A (A + F) ≤
            A + F ∧
          F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro huni hunit hideal arr_seq hva sched hfrom hmust hcomp hvjc ts tsk hin hpm hrtc _ hvac hresp _ _
    hwc hseq hcons L hL task_IBF htib R hmax j hj htsk
  have hpos := non_pathological_max_arrivals tsk arr_seq (hresp tsk hin) j htsk hj
  exact uniprocessor_response_time_bound_ideal hideal hunit arr_seq sched hmust hcomp hvjc ts tsk hin hpm hrtc
    hwc L hL _
    (task_IBF_implies_job_IBF huni hunit arr_seq hva sched hfrom hmust hcomp hvjc ts tsk hin hresp hwc hseq
      hcons task_IBF htib) R
    (max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis arr_seq ts tsk hin hrtc hvac L task_IBF R hmax hpos)
    j hj htsk

end SequentialAbstractRTA

end Prosa.Analysis.Abstract.Ideal.AbstractSeqRta
