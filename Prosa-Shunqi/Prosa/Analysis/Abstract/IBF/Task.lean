-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/IBF/task.v

import Prosa.Analysis.Definitions.TaskSchedule
import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Facts.Model.TaskSchedule
import Prosa.Analysis.Facts.Model.Sequential
import Prosa.Analysis.Abstract.AbstractRta

namespace Prosa.Analysis.Abstract.IBF.Task

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.TaskSchedule
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Abstract.Definitions
open Prosa.Analysis.Abstract.AbstractRta
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.TaskSchedule
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Model.Sequential
open scoped BigOperators

/-! Task interference and the reduction from a task interference bound to a
job interference bound under sequential tasks.
Binders follow the elaborated source types: every declaration takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `~~ b` is
`(!b) = true`; `a <= b < c` is a Boolean conjunction of decides; a Boolean
summand is `Bool.toNat`; `ε` is `1`; `tsk \in ts` is `decide (tsk ∈ ts) = true`. -/

section TaskInterferenceBound

variable {Job : JobType} [DecidableEq Job] {Task : TaskType} [DecidableEq Task]

/-- The task of `j` is not served at `t`. -/
noncomputable def nonself [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  !task_served_at arr_seq sched (job_task (Task := Task) j) t

/-- Interference not caused by the job's own task. -/
noncomputable def task_interference [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [Interference Job] (j : Job)
    (t : instant) : Bool :=
  cond_interference (nonself (Task := Task) arr_seq sched) j t

/-- Cumulative task interference over `[t1, t2)`. -/
noncomputable def cumul_task_interference [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [Interference Job] (j : Job)
    (t1 t2 : Nat) : Nat :=
  cumul_cond_interference (nonself (Task := Task) arr_seq sched) j t1 t2

/-- Task interference of the jobs of `tsk` is bounded by `task_IBF`. -/
def task_interference_is_bounded_by [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) [Interference Job] [InterferingWorkload Job]
    (task_IBF : duration → duration → work) : Prop :=
  cond_interference_is_bounded_by arr_seq sched tsk task_IBF (relative_arrival_time_of_job_is_A sched)
    (nonself (Task := Task) arr_seq sched)

end TaskInterferenceBound

section TaskIBFtoJobIBF

variable {Job : JobType} [DecidableEq Job] {Task : TaskType} [DecidableEq Task]

/-- At the start of a busy interval of a job of `tsk`, the task workload and
the task service released before it coincide. -/
def interference_and_workload_consistent_with_sequential_tasks [JobTask Job Task] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (tsk : Task) [Interference Job] [InterferingWorkload Job] : Prop :=
  ∀ (j : Job) (t1 t2 : instant),
    arrives_in arr_seq j → job_of_task tsk j = true → job_cost j > 0 →
    busy_interval sched j t1 t2 →
    task_workload_between arr_seq tsk 0 t1 =
      task_service_of_jobs_in sched tsk (arrivals_between arr_seq 0 t1) 0 t1

/-- LEAN_HELPER: a selected summand is bounded by the filtered sum. -/
private theorem le_sumFiltered' (l : List Job) (P : Job → Bool) (F : Job → Nat) (x : Job)
    (hx : x ∈ l) (hP : P x = true) : F x ≤ sumFiltered l P F := by
  unfold sumFiltered
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
    (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, hP⟩, rfl⟩)

/-- LEAN_HELPER: a selected summand splits off the filtered sum. -/
private theorem sumFiltered_erase (l : List Job) (P : Job → Bool) (F : Job → Nat) (x : Job)
    (hx : x ∈ l) (hP : P x = true) :
    sumFiltered l P F = F x + sumFiltered (l.erase x) P F := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    unfold sumFiltered at ih ⊢
    by_cases hax : a = x
    · subst hax
      simp [List.erase_cons_head, List.filter_cons, hP]
    · have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hax
        · exact h
      rw [List.erase_cons_tail (by simpa using hax)]
      by_cases hPa : P a = true
      · simp only [List.filter_cons, hPa, if_true, List.map_cons, List.sum_cons]
        rw [ih hx']
        omega'
      · simp only [List.filter_cons, hPa, if_false]
        exact ih hx'

/-- LEAN_HELPER: when no selected job is scheduled, the service vanishes. -/
private theorem service_of_jobs_at_zero {PState : ProcessorState Job} (sched : schedule PState)
    (P : Job → Bool) (l : List Job) (t : instant)
    (h : ∀ x, (!scheduled_at sched x t) = true) : service_of_jobs_at sched P l t = 0 := by
  unfold service_of_jobs_at sumFiltered
  rw [List.sum_eq_zero_iff]
  intro n hn
  rw [List.mem_map] at hn
  obtain ⟨x, _, rfl⟩ := hn
  exact not_scheduled_implies_no_service sched x t (h x)

/-- A job of `tsk` that arrived before a busy interval of another job of
`tsk` is complete at its start. -/
theorem completed_before_beginning_of_busy_interval [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (tsk : Task) [Interference Job] [InterferingWorkload Job],
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_of_task tsk j1 = true →
      job_of_task tsk j2 = true → job_cost_positive j1 = true →
    ∀ t1 t2 : instant, busy_interval sched j1 t1 t2 →
      job_arrival j2 < t1 → completed_by sched j2 t1 = true := by
  intro hus arr_seq hva sched hmust hcomp tsk _ _ hcons j1 j2 ha1 ha2 htsk1 htsk2 hpos t1 t2 hbi hlt
  have hc := hcons j1 t1 t2 ha1 htsk1 (by unfold job_cost_positive at hpos; exact of_decide_eq_true hpos) hbi
  unfold task_workload_between task_workload task_service_of_jobs_in at hc
  have hall := (all_jobs_have_completed_equiv_workload_eq_service hus arr_seq hva.1 sched hmust hcomp
    (job_of_task tsk) 0 t1 t1).2 hc
  exact hall j2 (arrived_between_implies_in_arrivals arr_seq hva.1 j2 0 t1 ha2
    (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega')) htsk2

/-- A job of `tsk` pending inside a busy interval of another job of `tsk`
arrived inside it. -/
theorem arrives_after_beginning_of_busy_interval [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (tsk : Task) [Interference Job] [InterferingWorkload Job],
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_of_task tsk j1 = true →
      job_of_task tsk j2 = true → job_cost_positive j1 = true →
    ∀ t1 t2 : instant, busy_interval sched j1 t1 t2 →
    ∀ t : Nat, t1 ≤ t → pending sched j2 t = true → arrived_between j2 t1 (t + 1) = true := by
  intro hus arr_seq hva sched hmust hcomp tsk _ _ hcons j1 j2 ha1 ha2 htsk1 htsk2 hpos t1 t2 hbi t hge
    hpend
  unfold pending has_arrived at hpend
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpend
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega'⟩
  by_contra hlt
  have hc := completed_before_beginning_of_busy_interval hus arr_seq hva sched hmust hcomp tsk hcons j1 j2
    ha1 ha2 htsk1 htsk2 hpos t1 t2 hbi (by omega')
  have hc' := completion_monotonic sched j2 t1 t hge hc
  rw [hc'] at hpend
  exact absurd hpend.2 (by decide)

/-- Case: the processor is idle. -/
theorem interference_plus_sched_le_serv_of_task_plus_task_interference_idle [JobTask Job Task]
    [JobArrival Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ (tsk : Task) [Interference Job] (j : Job) (t1 t : instant), is_idle arr_seq sched t = true →
      (interference j t).toNat + service_at sched j t ≤
        service_of_jobs_at sched (job_of_task tsk)
            (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1)) t +
          (task_interference (Task := Task) arr_seq sched j t).toNat := by
  intro hva sched hfrom hmust tsk _ j t1 t hidle
  have hns := fun x => not_scheduled_when_idle arr_seq hva sched hfrom hmust x t hidle
  rw [service_of_jobs_at_zero sched _ _ t hns, not_scheduled_implies_no_service sched j t (hns j)]
  have hnt := no_task_served_when_idle arr_seq hva PState sched hfrom hmust (job_task (Task := Task) j) t
    hidle
  unfold task_interference cond_interference nonself
  rw [hnt]
  simp

/-- Case: a job of another task is scheduled. -/
theorem interference_plus_sched_le_serv_of_task_plus_task_interference_task [JobTask Job Task]
    [JobArrival Job] {PState : ProcessorState Job} :
    uniprocessor_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ (tsk : Task) [Interference Job] (j : Job), job_of_task tsk j = true →
    ∀ (t1 t : instant) (j' : Job), scheduled_at sched j' t = true → (!job_of_task tsk j') = true →
      (interference j t).toNat + service_at sched j t ≤
        service_of_jobs_at sched (job_of_task tsk)
            (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1)) t +
          (task_interference (Task := Task) arr_seq sched j t).toNat := by
  intro huni arr_seq hva sched hfrom hmust tsk _ j htsk t1 t j' hs hnt
  have htj : job_task (Task := Task) j = tsk := by
    unfold job_of_task at htsk; exact of_decide_eq_true htsk
  have hsj : service_at sched j t = 0 := by
    apply not_scheduled_implies_no_service
    cases hsc : scheduled_at sched j t
    · rfl
    · exfalso
      have heq := huni j' j sched t hs hsc
      subst heq
      rw [htsk] at hnt
      exact absurd hnt (by decide)
  have hns := job_of_other_task_scheduled' arr_seq hva PState huni sched hfrom hmust
    (job_task (Task := Task) j) j' t (by rw [htj]; exact hnt) hs
  rw [hsj]
  unfold task_interference cond_interference nonself
  rw [hns]
  simp

/-- Case: a job of `tsk` is scheduled but receives no service. -/
theorem interference_plus_sched_le_serv_of_task_plus_task_interference_job [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched →
    ∀ (tsk : Task) [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ x : duration, t1 + x < t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t1 + x)) = true →
    ∀ j' : Job, scheduled_at sched j' t = true → job_of_task tsk j' = true → service_at sched j' t = 0 →
      (interference j t).toNat + service_at sched j t ≤
        service_of_jobs_at sched (job_of_task tsk)
            (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1)) t +
          (task_interference (Task := Task) arr_seq sched j t).toNat := by
  intro huni hus arr_seq hva sched hfrom hmust tsk _ _ hwc j ha htsk hpos t1 t2 hbi x hx t ht j' hs htsk'
    hserv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  have htj : job_task (Task := Task) j = tsk := by
    unfold job_of_task at htsk; exact of_decide_eq_true htsk
  have hsj : service_at sched j t = 0 := by
    rcases service_is_zero_or_one hus sched j t with h0 | h1
    · exact h0
    · exfalso
      have hsc : scheduled_at sched j t = true :=
        service_at_implies_scheduled_at sched j t (by rw [h1]; decide)
      have heq := huni j' j sched t hs hsc
      subst heq
      rw [hserv] at h1
      exact absurd h1 (by decide)
  have hint : interference j t = true := by
    have hw := hwc j t1 t2 t ha (by unfold job_cost_positive at hpos; exact of_decide_eq_true hpos) hbi.1
      ⟨ht.1, by omega'⟩
    by_contra hni
    have hr := hw.1 hni
    unfold receives_service_at at hr
    rw [hsj] at hr
    exact absurd hr (by decide)
  have hns := job_of_task_not_served arr_seq hva PState huni sched hfrom hmust (job_task (Task := Task) j) j' t
    hs (by rw [htj]; exact htsk') hserv
  rw [hsj]
  unfold task_interference cond_interference nonself
  rw [hns, hint]
  simp

/-- Inside a busy interval, interference and service of `j` sum to one. -/
theorem interference_and_service_eq_1 [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState) [Interference Job]
      [InterferingWorkload Job], work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ x : duration, t1 + x < t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t1 + x)) = true →
      (interference j t).toNat + service_at sched j t = 1 := by
  intro hus arr_seq sched _ _ hwc j ha hpos t1 t2 hbi x hx t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  have hw := hwc j t1 t2 t ha (by unfold job_cost_positive at hpos; exact of_decide_eq_true hpos) hbi.1
    ⟨ht.1, by omega'⟩
  rcases service_is_zero_or_one hus sched j t with h0 | h1
  · have hint : interference j t = true := by
      by_contra hni
      have hr := hw.1 hni
      unfold receives_service_at at hr
      rw [h0] at hr
      exact absurd hr (by decide)
    rw [h0, hint]; rfl
  · have hint : interference j t = false := by
      cases hi : interference j t
      · rfl
      · exfalso
        exact (hw.2 (by unfold receives_service_at; rw [h1]; decide)) hi
    rw [h1, hint]; rfl

/-- Case: a job of `tsk` is scheduled and receives service. -/
theorem interference_plus_sched_le_serv_of_task_plus_task_interference_j [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (tsk : Task) [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ x : duration, t1 + x < t2 → (!completed_by sched j (t1 + x)) = true →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t1 + x)) = true →
    ∀ j' : Job, scheduled_at sched j' t = true → job_of_task tsk j' = true → service_at sched j' t = 1 →
      (interference j t).toNat + service_at sched j t ≤
        service_of_jobs_at sched (job_of_task tsk)
            (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1)) t +
          (task_interference (Task := Task) arr_seq sched j t).toNat := by
  intro hus arr_seq hva sched hfrom hmust hcomp tsk _ _ hwc hseq hcons j ha htsk hpos t1 t2 hbi x hx hnc t
    ht j' hs htsk' hserv
  rw [interference_and_service_eq_1 hus arr_seq sched hwc j ha hpos t1 t2 hbi x hx t ht]
  have ht' := ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  have ha' := hfrom j' t hs
  have hstart := hbi.1.1.1
  have hge : t1 ≤ job_arrival j' := by
    by_contra hlt
    have hc := completed_before_beginning_of_busy_interval hus arr_seq hva sched hmust hcomp tsk hcons j j'
      ha ha' htsk htsk' hpos t1 t2 hbi (by omega')
    have hc' := completion_monotonic sched j' t1 t ht'.1 hc
    have hnc' := scheduled_implies_not_completed sched j' hcomp t hs
    rw [hc'] at hnc'
    exact absurd hnc' (by decide)
  have hle : job_arrival j' ≤ job_arrival j := by
    have hncj := incompletion_monotonic sched j t (t1 + x) (by omega') hnc
    exact scheduler_executes_job_with_earliest_arrival (Task := Task) arr_seq sched hseq j' j t ha' ha
      (by
        unfold job_of_task at htsk htsk'
        unfold same_task
        rw [of_decide_eq_true htsk', of_decide_eq_true htsk]
        simp)
      hncj hs
  have hin : j' ∈ arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1) :=
    of_decide_eq_true (arrived_between_implies_in_arrivals arr_seq hva.1 j' t1 _ ha'
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega'))
  have hle1 := le_sumFiltered' _ (job_of_task tsk) (fun x => service_at sched x t) j' hin htsk'
  unfold service_of_jobs_at
  have hle2 : 1 ≤ sumFiltered (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1))
      (job_of_task tsk) (fun x => service_at sched x t) := by
    have := hle1; simp only [hserv] at this; exact this
  omega'

/-- Hence, at every instant of `[t1, t1 + x)`, interference plus service of
`j` is at most the service of the jobs of `tsk` plus the task interference. -/
theorem interference_plus_sched_le_serv_of_task_plus_task_interference [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (tsk : Task) [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ x : duration, t1 + x < t2 → (!completed_by sched j (t1 + x)) = true →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t1 + x)) = true →
      (interference j t).toNat + service_at sched j t ≤
        service_of_jobs_at sched (job_of_task tsk)
            (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1)) t +
          (task_interference (Task := Task) arr_seq sched j t).toNat := by
  intro huni hus arr_seq hva sched hfrom hmust hcomp tsk _ _ hwc hseq hcons j ha htsk hpos t1 t2 hbi x hx
    hnc t ht
  cases hidle : is_idle arr_seq sched t
  · obtain ⟨s, hs⟩ := (is_nonidle_iff arr_seq hva sched hfrom hmust huni t).1 (by rw [hidle]; rfl)
    cases hts : job_of_task tsk s
    · exact interference_plus_sched_le_serv_of_task_plus_task_interference_task huni arr_seq hva sched hfrom
        hmust tsk j htsk t1 t s hs (by rw [hts]; rfl)
    · rcases service_is_zero_or_one hus sched s t with h0 | h1
      · exact interference_plus_sched_le_serv_of_task_plus_task_interference_job huni hus arr_seq hva sched
          hfrom hmust tsk hwc j ha htsk hpos t1 t2 hbi x hx t ht s hs hts h0
      · exact interference_plus_sched_le_serv_of_task_plus_task_interference_j hus arr_seq hva sched hfrom
          hmust hcomp tsk hwc hseq hcons j ha htsk hpos t1 t2 hbi x hx hnc t ht s hs hts h1
  · exact interference_plus_sched_le_serv_of_task_plus_task_interference_idle arr_seq hva sched hfrom hmust
      tsk j t1 t hidle

/-- The cumulative version of the previous bound. -/
theorem cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (tsk : Task) [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ x : duration, t1 + x < t2 → (!completed_by sched j (t1 + x)) = true →
      cumulative_interference j t1 (t1 + x) ≤
        task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1))
            t1 (t1 + x) - service_during sched j t1 (t1 + x) +
          cumul_task_interference (Task := Task) arr_seq sched j t1 (t1 + x) := by
  intro huni hus arr_seq hva sched hfrom hmust hcomp tsk _ _ hwc hseq hcons j ha htsk hpos t1 t2 hbi x hx
    hnc
  have hstart := hbi.1.1.1
  have hin : j ∈ arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1) :=
    of_decide_eq_true (arrived_between_implies_in_arrivals arr_seq hva.1 j t1 _ ha
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega'))
  have h2 : service_during sched j t1 (t1 + x) ≤
      task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1))
        t1 (t1 + x) := by
    unfold task_service_of_jobs_in service_of_jobs
    exact le_sumFiltered' _ (job_of_task tsk) (fun y => service_during sched y t1 (t1 + x)) j hin htsk
  have h1 : cumulative_interference j t1 (t1 + x) + service_during sched j t1 (t1 + x) ≤
      task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1))
        t1 (t1 + x) + cumul_task_interference (Task := Task) arr_seq sched j t1 (t1 + x) := by
    unfold task_service_of_jobs_in
    rw [service_of_jobs_sum_over_time_interval]
    unfold cumulative_interference cumul_task_interference cumul_cond_interference service_during
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_Ico] at ht
    have := interference_plus_sched_le_serv_of_task_plus_task_interference huni hus arr_seq hva sched hfrom
      hmust hcomp tsk hwc hseq hcons j ha htsk hpos t1 t2 hbi x hx hnc t
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    unfold task_interference at this
    simpa [cond_interference] using this
  omega'

/-- The service terms are bounded by the workload terms. -/
theorem serv_of_task_le_workload_of_task_plus [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, completed_jobs_dont_execute sched →
    ∀ (tsk : Task) [Interference Job] [InterferingWorkload Job] (j : Job),
      arrives_in arr_seq j → job_of_task tsk j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ x : duration,
      task_service_of_jobs_in sched tsk (arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1))
            t1 (t1 + x) - service_during sched j t1 (t1 + x) +
          cumul_task_interference (Task := Task) arr_seq sched j t1 (t1 + x) ≤
        task_workload_between arr_seq tsk t1 (t1 + (job_arrival j - t1) + 1) - job_cost j +
          cumul_task_interference (Task := Task) arr_seq sched j t1 (t1 + x) := by
  intro hus arr_seq hva sched hcomp tsk _ _ j ha htsk t1 t2 hbi x
  have hstart := hbi.1.1.1
  have hin : j ∈ arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1) :=
    of_decide_eq_true (arrived_between_implies_in_arrivals arr_seq hva.1 j t1 _ ha
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega'))
  apply Nat.add_le_add_right
  unfold task_service_of_jobs_in service_of_jobs task_workload_between task_workload workload_of_jobs
  rw [sumFiltered_erase _ _ _ j hin htsk, sumFiltered_erase _ _ (fun y => job_cost y) j hin htsk]
  have hle := service_of_jobs_le_workload hus sched hcomp (job_of_task tsk)
    ((arrivals_between arr_seq t1 (t1 + (job_arrival j - t1) + 1)).erase j) t1 (t1 + x)
  unfold service_of_jobs workload_of_jobs at hle
  omega'

/-- The cumulative interference is bounded by the task workload of
`[t1, t1 + A + ε)` without `j`, plus the task interference. -/
theorem cumulative_job_interference_le_task_interference_bound [JobTask Job Task] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
    ∀ (tsk : Task) [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ x : duration, t1 + x < t2 → (!completed_by sched j (t1 + x)) = true →
      cumulative_interference j t1 (t1 + x) ≤
        task_workload_between arr_seq tsk t1 (t1 + (job_arrival j - t1) + 1) - job_cost j +
          cumul_task_interference (Task := Task) arr_seq sched j t1 (t1 + x) := by
  intro huni hus arr_seq hva sched hfrom hmust hcomp tsk _ _ hwc hseq hcons j ha htsk hpos t1 t2 hbi x hx
    hnc
  exact Nat.le_trans
    (cumul_interference_plus_sched_le_serv_of_task_plus_cumul_task_interference huni hus arr_seq hva sched
      hfrom hmust hcomp tsk hwc hseq hcons j ha htsk hpos t1 t2 hbi x hx hnc)
    (serv_of_task_le_workload_of_task_plus hus arr_seq hva sched hcomp tsk j ha htsk t1 t2 hbi x)

/-- The cumulative interference is bounded by the task RBF of `A + ε`
without the job's cost, plus the task interference. -/
theorem cumulative_job_interference_bound [TaskCost Task] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ j : Job, arrives_in arr_seq j → job_of_task tsk j = true → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval sched j t1 t2 →
    ∀ x : duration, t1 + x < t2 → (!completed_by sched j (t1 + x)) = true →
      cumulative_interference j t1 (t1 + x) ≤
        task_request_bound_function tsk (job_arrival j - t1 + 1) - task_cost tsk +
          cumul_task_interference (Task := Task) arr_seq sched j t1 (t1 + x) := by
  intro huni hus arr_seq hva sched hfrom hmust hcomp hvalid ts tsk hin _ hresp _ _ hwc hseq hcons j ha
    htsk hpos t1 t2 hbi x hx hnc
  have hstart := hbi.1.1.1
  refine Nat.le_trans (cumulative_job_interference_le_task_interference_bound huni hus arr_seq hva sched
    hfrom hmust hcomp tsk hwc hseq hcons j ha htsk hpos t1 t2 hbi x hx hnc) ?_
  apply Nat.add_le_add_right
  have hrbf := task_rbf_without_job_under_analysis arr_seq hva.1 hvalid tsk (hresp tsk hin) j htsk ha t1
    (job_arrival j - t1 + 1) (by omega') hstart
  rw [show t1 + (job_arrival j - t1) + 1 = t1 + (job_arrival j - t1 + 1) by omega']
  exact hrbf

/-- A task interference bound yields a job interference bound. -/
theorem task_IBF_implies_job_IBF [TaskCost Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_service_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
    ∀ [MaxArrivals Task], taskset_respects_max_arrivals arr_seq ts →
    ∀ [Interference Job] [InterferingWorkload Job], work_conserving arr_seq sched →
      sequential_tasks (Task := Task) arr_seq sched →
      interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk →
    ∀ task_IBF : duration → duration → duration,
      task_interference_is_bounded_by arr_seq sched tsk task_IBF →
      job_interference_is_bounded_by arr_seq sched tsk
        (fun A R => task_request_bound_function tsk (A + 1) - task_cost tsk + task_IBF A R)
        (relative_arrival_time_of_job_is_A sched) := by
  intro huni hus arr_seq hva sched hfrom hmust hcomp hvalid ts tsk hin _ hresp _ _ hwc hseq hcons task_IBF
    htib t1 t2 R j ha htsk hbi hlt hnc A hA
  have hpos : job_cost_positive j = true := by
    unfold job_cost_positive
    apply decide_eq_true
    rcases Nat.eq_zero_or_pos (job_cost j) with h0 | h
    · exfalso
      unfold completed_by at hnc
      rw [h0] at hnc
      simp at hnc
    · exact h
  have hAeq := hA t1 t2 hbi
  have hb := cumulative_job_interference_bound huni hus arr_seq hva sched hfrom hmust hcomp hvalid ts tsk
    hin hresp hwc hseq hcons j ha htsk hpos t1 t2 hbi R hlt hnc
  have ht := htib t1 t2 R j ha htsk hbi hlt hnc A hA
  unfold cumulative_interference at hb
  unfold cumul_task_interference at hb
  rw [← hAeq] at hb
  simp only
  omega'

end TaskIBFtoJobIBF

end Prosa.Analysis.Abstract.IBF.Task
