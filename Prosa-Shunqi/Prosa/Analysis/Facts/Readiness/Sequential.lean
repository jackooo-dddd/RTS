-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/readiness/sequential.v

import Prosa.Analysis.Definitions.Readiness
import Prosa.Analysis.Definitions.WorkBearingReadiness
import Prosa.Analysis.Facts.Model.TaskArrivals
import Prosa.Model.Readiness.Sequential

namespace Prosa.Analysis.Facts.Readiness.Sequential

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Readiness.Sequential
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Definitions.Readiness
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.TaskArrivals

/-! Representation notes: the source's section-local
`#[local] Instance sequential_readiness_instance := sequential_ready_instance
arr_seq` is a plain definition (below) passed explicitly, as the elaborated
source types do; the JLFP policy of `work_bearing_readiness` is the accepted
`FP_to_JLFP` of the FP policy, as elaborated. Binder orders and hypothesis
sets follow the elaborated types. -/

/-- The source's section-local readiness instance. -/
@[reducible] noncomputable def sequential_readiness_instance {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) : JobReady Job PState :=
  sequential_ready_instance (Task := Task) arr_seq

/-- LEAN_HELPER: schedules with identical prefixes provide the same service
within the prefix. -/
private theorem service_of_identical_prefix {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched sched' : schedule PState) (h : instant)
    (hp : identical_prefix sched sched' h) (j : Job) (t : instant) (ht : t ≤ h) :
    service sched j t = service sched' j t := by
  unfold service service_during
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s < h := by
    simp only [Finset.mem_Ico] at hs
    try dsimp only [instant] at *
    omega
  unfold service_at
  rw [hp s hs']

/-- The sequential readiness model is sequential. -/
theorem sequential_readiness_is_sequential {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    sequential_readiness (sequential_readiness_instance (Task := Task) (PState := PState) arr_seq)
      (Task := Task) arr_seq := by
  intro sched j t h
  change (pending sched j t && prior_jobs_complete (Task := Task) arr_seq sched j t) = true at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- The sequential readiness model is nonclairvoyant. -/
theorem sequential_readiness_nonclairvoyance {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    nonclairvoyant_readiness (sequential_readiness_instance (Task := Task) (PState := PState) arr_seq) := by
  intro sched sched' j h hp t ht
  have hc : ∀ j', completed_by sched j' t = completed_by sched' j' t := by
    intro j'; unfold completed_by; rw [service_of_identical_prefix sched sched' h hp j' t ht]
  change (pending sched j t && prior_jobs_complete (Task := Task) arr_seq sched j t) =
    (pending sched' j t && prior_jobs_complete (Task := Task) arr_seq sched' j t)
  unfold pending prior_jobs_complete
  rw [hc j]
  congr 1
  apply List.all_congr rfl
  exact hc

/-- The sequential readiness model implies sequential tasks. -/
theorem sequential_readiness_implies_sequential_tasks {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ sched : schedule PState,
        @valid_schedule Job _ _ PState sched _ (sequential_readiness_instance (Task := Task) arr_seq) arr_seq →
          sequential_tasks (Task := Task) arr_seq sched := by
  intro hc sched hvalid j1 j2 t ha1 ha2 hsame hlt hs
  have hready := hvalid.2 j2 t hs
  change (pending sched j2 t && prior_jobs_complete (Task := Task) arr_seq sched j2 t) = true at hready
  simp only [Bool.and_eq_true] at hready
  have hall := hready.2
  unfold prior_jobs_complete at hall
  rw [List.all_eq_true] at hall
  apply hall
  have hbt : arrived_between j1 0 (job_arrival j2) = true := by
    simp [arrived_between, hlt]
  have hin := arrived_between_implies_in_arrivals arr_seq hc j1 0 (job_arrival j2) ha1 hbt
  unfold task_arrivals_before task_arrivals_between
  simp only [List.mem_filter]
  refine ⟨of_decide_eq_true hin, ?_⟩
  unfold job_of_task
  simp only [same_task, decide_eq_true_eq] at hsame
  simp [hsame]

/-- The sequential readiness model is work-bearing (for any reflexive FP
policy, through its JLFP conversion). -/
theorem sequential_readiness_implies_work_bearing_readiness {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (sched : schedule PState) (FP : FP_policy Task), reflexive_task_priorities FP →
        @work_bearing_readiness Job _ _ _ PState (sequential_readiness_instance (Task := Task) arr_seq)
          arr_seq sched (FP_to_JLFP FP) := by
  intro hc sched FP hrefl
  suffices H : ∀ (k : Nat) (j : Job), job_arrival j ≤ k → ∀ t, arrives_in arr_seq j →
      pending sched j t = true →
        ∃ j_hp : Job, arrives_in arr_seq j_hp ∧
          (sequential_readiness_instance (Task := Task) (PState := PState) arr_seq).job_ready sched j_hp t = true ∧
          job_task (Task := Task) j_hp = job_task (Task := Task) j by
    intro j t ha hp
    obtain ⟨j_hp, ha', hr, htask⟩ := H (job_arrival j) j (Nat.le_refl _) t ha hp
    refine ⟨j_hp, ha', hr, ?_⟩
    show FP.hep_task (job_task (Task := Task) j_hp) (job_task (Task := Task) j) = true
    rw [htask]; exact hrefl _
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j hk t ha hp
    by_cases hr : (sequential_readiness_instance (Task := Task) (PState := PState) arr_seq).job_ready sched j t = true
    · exact ⟨j, ha, hr, rfl⟩
    · change ¬ (pending sched j t && prior_jobs_complete (Task := Task) arr_seq sched j t) = true at hr
      rw [hp, Bool.true_and] at hr
      unfold prior_jobs_complete at hr
      rw [List.all_eq_true] at hr
      simp only [not_forall, exists_prop] at hr
      obtain ⟨j', hin, hnc⟩ := hr
      have hlt := arrives_in_task_arrivals_before_implies_arrives_before arr_seq hc
        (job_task (Task := Task) j) j' (job_arrival j) (decide_eq_true hin)
      have ha' := arrives_in_task_arrivals_implies_arrived arr_seq (job_task (Task := Task) j) 0
        (job_arrival j) j' (decide_eq_true hin)
      have htask' : job_task (Task := Task) j' = job_task (Task := Task) j := by
        unfold task_arrivals_before task_arrivals_between at hin
        simp only [List.mem_filter, job_of_task, decide_eq_true_eq] at hin
        exact hin.2
      have hp' : pending sched j' t = true := by
        simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hp ⊢
        simp only [Bool.not_eq_true] at hnc
        refine ⟨?_, hnc⟩
        have := hp.1
        try dsimp only [instant] at *
        omega
      obtain ⟨j_hp, ha'', hr', ht'⟩ := ih (job_arrival j') (Nat.lt_of_lt_of_le hlt hk) j' (Nat.le_refl _) t ha' hp'
      exact ⟨j_hp, ha'', hr', ht'.trans htask'⟩

end Prosa.Analysis.Facts.Readiness.Sequential
