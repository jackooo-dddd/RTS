-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/jitter.v

import Prosa.Analysis.Facts.DelayPropagation
import Prosa.Model.Schedule.WorkConserving
import Prosa.Model.Readiness.Basic
import Prosa.Model.Schedule.PriorityDriven
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Analysis.Facts.Model.Scheduled
import Prosa.Analysis.Facts.Behavior.Completion

namespace Prosa.Analysis.Facts.Jitter

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Jitter
open Prosa.Model.Readiness.Jitter
open Prosa.Model.Readiness.Basic
open Prosa.Model.Priority.Definitions
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.WorkConserving
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.DelayPropagation
open Prosa.Analysis.Facts.DelayPropagation
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion

/-! Propagation of release jitter into arrival curves.

Binders follow the elaborated source types: every declaration takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
The source's section-local instances `release_as_arrival` and
`release_curve` of `analysis/definitions/delay_propagation.v` are the
definitions of the same names below (the release time
`job_arrival j + job_jitter j` of the original arrival instance, and the
accepted `propagated_arrival_curve id task_jitter`); like the source-local
readiness instances `jitter_ready_instance` and `basic_ready_instance`, they
are passed explicitly wherever the elaborated statements use them.
Representation: a Boolean in `Prop` position is `= true`; `x \in s` is
`decide (x ∈ s)`; an arrival curve as a function is its `max_arrivals`
field. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

/-- The source's local instance: release times reinterpreted as arrival times. -/
@[reducible] def release_as_arrival {Job : JobType} [DecidableEq Job]
    (original_arrival : JobArrival Job) [JobJitter Job] : JobArrival Job :=
  ⟨fun j => original_arrival.job_arrival j + job_jitter j⟩

/-- The source's local instance: the arrival curve propagated by the jitter bounds. -/
@[reducible] def release_curve {Task : TaskType} [DecidableEq Task]
    (arrival_curve : MaxArrivals Task) [TaskJitter Task] : MaxArrivals Task :=
  @propagated_arrival_curve Task Task _ _ id task_jitter arrival_curve

section JitterPropagationFacts

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- The arrival and release sequences contain the same jobs. -/
theorem jitter_arrives_in_iff [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ j : Job, arrives_in arr_seq j ↔ arrives_in (release_sequence original_arrival arr_seq) j := by
  intro hva ts hvj j
  have hmap := jitter_arr_seq_mapping_valid original_arrival ts arr_seq hvj
  constructor
  · intro h
    exact @arrives_in_propagated_if Task _ Job Job _ _ _ original_arrival (release_as_arrival original_arrival)
      id (fun j => [j]) job_jitter task_jitter ts arr_seq hmap j hva.1 h
  · intro h
    exact @arrives_in_propagated_only_if Task _ Job Job _ _ _ original_arrival (release_as_arrival original_arrival)
      id (fun j => [j]) job_jitter task_jitter ts arr_seq hmap j h

/-- The induced release sequence is valid. -/
theorem valid_release_sequence [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
      @valid_arrival_sequence Job _ (release_as_arrival original_arrival)
        (release_sequence original_arrival arr_seq) := by
  intro hva ts hvj
  exact @valid_propagated_arrival_sequence Task _ Job Job _ _ _ original_arrival
    (release_as_arrival original_arrival) id (fun j => [j]) job_jitter task_jitter ts arr_seq
    (jitter_arr_seq_mapping_valid original_arrival ts arr_seq hvj) hva

/-- A structurally valid arrival curve induces a structurally valid release curve. -/
theorem valid_release_curve (arrival_curve : MaxArrivals Task) [TaskJitter Task] (ts : TaskSet Task) :
    valid_taskset_arrival_curve ts (@MaxArrivals.max_arrivals Task _ arrival_curve) →
      valid_taskset_arrival_curve ts (@MaxArrivals.max_arrivals Task _ (release_curve arrival_curve)) := by
  intro hvalid
  exact @propagated_arrival_curve_valid Task Task _ _ id task_jitter ts arrival_curve
    (fun tsk hin => (hvalid tsk hin).2)

/-- If the arrival curve bounds the arrivals, the release curve bounds the releases. -/
theorem release_curve_respected (arrival_curve : MaxArrivals Task) [JobTask Job Task]
    (original_arrival : JobArrival Job) [TaskJitter Task] [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
      valid_taskset_arrival_curve ts (@MaxArrivals.max_arrivals Task _ arrival_curve) →
      @taskset_respects_max_arrivals Task _ Job _ _ arr_seq arrival_curve ts →
      @taskset_respects_max_arrivals Task _ Job _ _ (release_sequence original_arrival arr_seq)
        (release_curve arrival_curve) ts := by
  intro hva ts hvj hvac hresp
  have hvac' : valid_taskset_arrival_curve (ts.map id) (@MaxArrivals.max_arrivals Task _ arrival_curve) := by
    rw [List.map_id]; exact hvac
  have hresp' : @taskset_respects_max_arrivals Task _ Job _ _ arr_seq arrival_curve (ts.map id) := by
    rw [List.map_id]; exact hresp
  exact @propagated_arrival_curve_respected Task Task _ _ Job Job _ _ _ _ original_arrival
    (release_as_arrival original_arrival) id id (fun j => [j]) job_jitter task_jitter ts
    (jitter_delay_mapping_valid original_arrival ts hvj) arrival_curve arr_seq
    (jitter_arr_seq_mapping_valid original_arrival ts arr_seq hvj)
    (fun _ _ _ _ => by simp) hva hvac' hresp'

/-- All released jobs still belong to the task set. -/
theorem jitter_prop_same_jobs [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
      all_jobs_from_taskset arr_seq ts → all_jobs_from_taskset (release_sequence original_arrival arr_seq) ts := by
  intro hva ts hvj hall j hj
  exact hall j ((jitter_arrives_in_iff original_arrival arr_seq hva ts hvj j).mpr hj)

/-- All scheduled jobs still come from the release sequence. -/
theorem jitter_prop_same_jobs' [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ (PState : ProcessorState Job) (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq →
        jobs_come_from_arrival_sequence sched (release_sequence original_arrival arr_seq) := by
  intro hva ts hvj PState sched hfrom j t hs
  exact (jitter_arrives_in_iff original_arrival arr_seq hva ts hvj j).mp (hfrom j t hs)

/-- Job costs remain valid. -/
theorem jitter_prop_valid_costs [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ [JobCost Job] [TaskCost Task],
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
        arrivals_have_valid_job_costs (Task := Task) (release_sequence original_arrival arr_seq) := by
  intro hva ts hvj _ _ hv j hj
  exact hv j ((jitter_arrives_in_iff original_arrival arr_seq hva ts hvj j).mpr hj)

/-- Jitter-aware readiness implies basic readiness w.r.t. release times. -/
theorem jitter_ready_to_execute (original_arrival : JobArrival Job) [JobJitter Job]
    {PState : ProcessorState Job} (sched : schedule PState) [JobCost Job] :
    @jobs_must_be_ready_to_execute Job _ original_arrival PState sched _
        (@jitter_ready_instance Job _ original_arrival _ PState _) →
      @jobs_must_be_ready_to_execute Job _ (release_as_arrival original_arrival) PState sched _
        (@basic_ready_instance Job _ PState (release_as_arrival original_arrival) _) := by
  intro h j t hs
  exact h j t hs

/-- Work conservation is preserved. -/
theorem jitter_work_conservation [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ (PState : ProcessorState Job) (sched : schedule PState) [JobCost Job],
      @work_conserving Job _ original_arrival _ PState
          (@jitter_ready_instance Job _ original_arrival _ PState _) arr_seq sched →
        @work_conserving Job _ (release_as_arrival original_arrival) _ PState
          (@basic_ready_instance Job _ PState (release_as_arrival original_arrival) _)
          (release_sequence original_arrival arr_seq) sched := by
  intro hva ts hvj PState sched _ hwc j t harr hbl
  exact hwc j t ((jitter_arrives_in_iff original_arrival arr_seq hva ts hvj j).mpr harr) hbl

/-- Schedule validity is preserved. -/
theorem jitter_valid_schedule [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ (PState : ProcessorState Job) (sched : schedule PState) [JobCost Job],
      @valid_schedule Job _ original_arrival PState sched _
          (@jitter_ready_instance Job _ original_arrival _ PState _) arr_seq →
        @valid_schedule Job _ (release_as_arrival original_arrival) PState sched _
          (@basic_ready_instance Job _ PState (release_as_arrival original_arrival) _)
          (release_sequence original_arrival arr_seq) := by
  intro hva ts hvj PState sched _ hvs
  exact ⟨jitter_prop_same_jobs' original_arrival arr_seq hva ts hvj PState sched hvs.1,
    jitter_ready_to_execute original_arrival sched hvs.2⟩

/-- The two readings of a valid schedule: jobs arrive (w.r.t. release times) before executing. -/
private theorem release_must_arrive (original_arrival : JobArrival Job) [JobJitter Job]
    {PState : ProcessorState Job} (sched : schedule PState) [JobCost Job] :
    @jobs_must_be_ready_to_execute Job _ original_arrival PState sched _
        (@jitter_ready_instance Job _ original_arrival _ PState _) →
      @jobs_must_arrive_to_execute Job _ (release_as_arrival original_arrival) PState sched := fun h =>
  @jobs_must_arrive_to_be_ready Job _ PState sched _ (release_as_arrival original_arrival)
    (@basic_ready_instance Job _ PState (release_as_arrival original_arrival) _)
    (jitter_ready_to_execute original_arrival sched h)

/-- The set of scheduled jobs is unchanged. -/
theorem jitter_scheduled_jobs_at_equiv [JobTask Job Task] (original_arrival : JobArrival Job)
    [TaskJitter Task] [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ (PState : ProcessorState Job) (sched : schedule PState) [JobCost Job],
      @valid_schedule Job _ original_arrival PState sched _
          (@jitter_ready_instance Job _ original_arrival _ PState _) arr_seq →
      ∀ (t : instant) (j : Job),
        decide (j ∈ scheduled_jobs_at (release_sequence original_arrival arr_seq) sched t) =
          decide (j ∈ scheduled_jobs_at arr_seq sched t) := by
  intro hva ts hvj PState sched _ hvs t j
  have hmust : @jobs_must_arrive_to_execute Job _ original_arrival PState sched :=
    @jobs_must_arrive_to_be_ready Job _ PState sched _ original_arrival
      (@jitter_ready_instance Job _ original_arrival _ PState _) hvs.2
  rw [scheduled_jobs_at_iff arr_seq hva sched hvs.1 hmust j t,
    @scheduled_jobs_at_iff Job _ (release_as_arrival original_arrival) PState
      (release_sequence original_arrival arr_seq)
      (valid_release_sequence original_arrival arr_seq hva ts hvj) sched
      (jitter_prop_same_jobs' original_arrival arr_seq hva ts hvj PState sched hvs.1)
      (release_must_arrive original_arrival sched hvs.2) j t]

/-- On a uniprocessor, the scheduled job is unchanged. -/
theorem jitter_scheduled_job_at_eq [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ (PState : ProcessorState Job) (sched : schedule PState) [JobCost Job],
      @valid_schedule Job _ original_arrival PState sched _
          (@jitter_ready_instance Job _ original_arrival _ PState _) arr_seq →
      ∀ t : instant, uniprocessor_model PState →
        scheduled_job_at arr_seq sched t = scheduled_job_at (release_sequence original_arrival arr_seq) sched t := by
  intro hva ts hvj PState sched _ hvs t huni
  have hmust : @jobs_must_arrive_to_execute Job _ original_arrival PState sched :=
    @jobs_must_arrive_to_be_ready Job _ PState sched _ original_arrival
      (@jitter_ready_instance Job _ original_arrival _ PState _) hvs.2
  have hva' := valid_release_sequence original_arrival arr_seq hva ts hvj
  have hfrom' := jitter_prop_same_jobs' original_arrival arr_seq hva ts hvj PState sched hvs.1
  have hmust' := release_must_arrive original_arrival sched hvs.2
  have hsa := fun j => scheduled_job_at_scheduled_at arr_seq hva sched hvs.1 hmust huni j t
  have hsa' := fun j => @scheduled_job_at_scheduled_at Job _ (release_as_arrival original_arrival) PState
    (release_sequence original_arrival arr_seq) hva' sched hfrom' hmust' huni j t
  have hnone := scheduled_job_at_none arr_seq hva sched hvs.1 hmust t
  have hnone' := @scheduled_job_at_none Job _ (release_as_arrival original_arrival) PState
    (release_sequence original_arrival arr_seq) hva' sched hfrom' hmust' t
  cases h1 : scheduled_job_at arr_seq sched t with
  | none =>
    have hall := hnone.mp h1
    exact (hnone'.mpr hall).symm
  | some j =>
    have hj : scheduled_at sched j t = true := by rw [← hsa j, h1]; simp
    cases h2 : scheduled_job_at (release_sequence original_arrival arr_seq) sched t with
    | none =>
      have := hnone'.mp h2 j
      rw [hj] at this
      exact absurd this (by decide)
    | some j' =>
      have hj' : scheduled_at sched j' t = true := by rw [← hsa' j', h2]; simp
      rw [huni j j' sched t hj hj']

/-- FP-policy compliance is preserved. -/
theorem jitter_FP_compliance [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ (PState : ProcessorState Job) (sched : schedule PState) [JobCost Job],
      @valid_schedule Job _ original_arrival PState sched _
          (@jitter_ready_instance Job _ original_arrival _ PState _) arr_seq →
      ∀ (FP : FP_policy Task) [JobPreemptable Job], uniprocessor_model PState →
        @respects_FP_policy_at_preemption_point Task _ Job _ _ original_arrival _ PState _
            (@jitter_ready_instance Job _ original_arrival _ PState _) arr_seq sched FP →
          @respects_FP_policy_at_preemption_point Task _ Job _ _ (release_as_arrival original_arrival) _ PState _
            (@basic_ready_instance Job _ PState (release_as_arrival original_arrival) _)
            (release_sequence original_arrival arr_seq) sched FP := by
  intro hva ts hvj PState sched _ hvs FP _ huni hresp j j_hp t harr hpt hbl hsched
  have heq := jitter_scheduled_job_at_eq original_arrival arr_seq hva ts hvj PState sched hvs t huni
  refine hresp j j_hp t ((jitter_arrives_in_iff original_arrival arr_seq hva ts hvj j).mpr harr) ?_ hbl hsched
  unfold preemption_time at hpt ⊢
  rw [heq]
  exact hpt

/-- Response-time bounds after jitter propagation transfer, increased by the task's jitter bound. -/
theorem jitter_response_time_bound [JobTask Job Task] (original_arrival : JobArrival Job) [TaskJitter Task]
    [JobJitter Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : TaskSet Task, valid_jitter_bounds (Job := Job) ts →
    ∀ (PState : ProcessorState Job) (sched : schedule PState) [JobCost Job] (tsk : Task) (R : duration),
      decide (tsk ∈ ts) = true →
      @task_response_time_bound Task _ Job _ (release_as_arrival original_arrival) _ _ PState
          (release_sequence original_arrival arr_seq) sched tsk R →
        @task_response_time_bound Task _ Job _ original_arrival _ _ PState arr_seq sched tsk
          (task_jitter tsk + R) := by
  intro hva ts hvj PState sched _ tsk R hin hrtb j harr htsk
  have hrel := hrtb j ((jitter_arrives_in_iff original_arrival arr_seq hva ts hvj j).mp harr) htsk
  have htask : job_task j = tsk := of_decide_eq_true htsk
  have hjit : job_jitter j ≤ task_jitter tsk := hvj tsk hin j htask
  unfold job_response_time_bound at hrel ⊢
  exact completion_monotonic sched j _ _
    (show original_arrival.job_arrival j + job_jitter j + R ≤ original_arrival.job_arrival j + (task_jitter tsk + R)
      by omega') hrel

end JitterPropagationFacts

end Prosa.Analysis.Facts.Jitter
