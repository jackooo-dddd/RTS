-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/interference.v

import Prosa.Analysis.Facts.Priority.Classes
import Prosa.Analysis.Definitions.Interference
import Prosa.Analysis.Definitions.Priority.Classes
import Prosa.Analysis.Facts.Model.ServiceOfJobs

namespace Prosa.Analysis.Facts.Interference

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.Supply
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.Service
open Prosa.Analysis.Definitions.Interference
open Prosa.Analysis.Definitions.Priority.Classes
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Facts.Priority.Classes
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Supply
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open scoped BigOperators

/-! Auxiliary lemmas about interference. Binders follow the elaborated
source types (the unused `reflexive_task_priorities` hypothesis and unused
section context are absent, as in the elaborated source). Representation:
Booleans in `Prop` position are `= true`; `~~ b` is `!b`; the FP and JLFP
policies are explicit binders that act as local instances; `classical.quiet_time`
is the accepted `quiet_time`. -/

/-- A half-open `sumSeq` over `List.range'` is the corresponding `Finset.Ico`
sum (both compute the same right fold). -/
private theorem sumSeq_range'_eq (a b : Nat) (f : Nat → Nat) :
    sumSeq (List.range' a (b - a)) f = ∑ t ∈ (Finset.Ico a b : Finset Nat), f t := by
  unfold sumSeq
  rw [Finset.sum_Ico_eq_sum_range]
  have : ∀ n a, ((List.range' a n).map f).sum = ∑ k ∈ Finset.range n, f (a + k) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [List.range'_succ, List.map_cons, List.sum_cons, ih (a + 1), Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [Nat.add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      omega
  exact this (b - a) a

/-- Any higher-or-equal-priority job of another task comes from a strictly
higher-priority task or from another equal-priority task. -/
theorem another_task_hep_job_split_hp_ep {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] (FP : FP_policy Task)
    (JLFP : JLFP_policy Job) :
    JLFP_FP_compatible JLFP FP →
      ∀ j1 j2 : Job,
        another_task_hep_job (Task := Task) j1 j2 =
          (hp_task_hep_job (Task := Task) j1 j2 || other_ep_task_hep_job (Task := Task) j1 j2) := by
  intro hcompat j1 j2
  unfold another_task_hep_job hp_task_hep_job other_ep_task_hep_job ep_task_hep_job
  cases hj : hep_job j1 j2
  · simp
  · have hhep := hep_job_implies_hep_task JLFP FP hcompat j1 j2 hj
    rw [hep_hp_ep_task FP] at hhep
    by_cases ht : job_task (Task := Task) j1 = job_task (Task := Task) j2
    · rw [ht, hp_task_irrefl FP]
      simp
    · have hne : decide (job_task (Task := Task) j1 ≠ job_task (Task := Task) j2) = true :=
        decide_eq_true ht
      rw [hne]
      simp only [Bool.true_and, Bool.and_true]
      exact hhep.symm

/-- Interference from higher-or-equal-priority jobs of other tasks splits into
higher-priority-task and other-equal-priority-task interference. -/
theorem hep_interference_another_task_split {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (FP : FP_policy Task)
    (JLFP : JLFP_policy Job) :
    JLFP_FP_compatible JLFP FP →
      ∀ (j : Job) (t : instant),
        another_task_hep_job_interference (Task := Task) arr_seq sched j t =
          (hep_job_from_hp_task_interference (Task := Task) arr_seq sched j t ||
            hep_job_from_other_ep_task_interference (Task := Task) arr_seq sched j t) := by
  intro hcompat j t
  unfold another_task_hep_job_interference hep_job_from_hp_task_interference
    hep_job_from_other_ep_task_interference
  have hsplit := another_task_hep_job_split_hp_ep FP JLFP hcompat
  generalize served_jobs_at arr_seq sched t = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, hsplit a j, ih]
    cases hp_task_hep_job (Task := Task) a j <;> cases other_ep_task_hep_job (Task := Task) a j <;>
      simp

private theorem sumSeq_add {I : Type _} (r : List I) (f g : I → Nat) :
    sumSeq r (fun x => f x + g x) = sumSeq r f + sumSeq r g := by
  unfold sumSeq
  induction r with
  | nil => simp
  | cons a r ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sumSeq_congr {I : Type _} (r : List I) (f g : I → Nat)
    (h : ∀ x, x ∈ r → f x = g x) : sumSeq r f = sumSeq r g := by
  unfold sumSeq
  congr 1
  exact List.map_congr_left h

/-- On a uniprocessor, the cumulative interference from higher-or-equal-priority
jobs of other tasks is the sum of the higher-priority-task and the
other-equal-priority-task parts. -/
theorem cumulative_hep_interference_split_tasks_new {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (FP : FP_policy Task)
    (JLFP : JLFP_policy Job) :
    JLFP_FP_compatible JLFP FP → uniprocessor_model PState →
      ∀ (j : Job) (t1 : instant) (Δ : Nat),
        cumulative_another_task_hep_job_interference (Task := Task) arr_seq sched j t1 (t1 + Δ) =
          cumulative_interference_from_hep_jobs_from_hp_tasks (Task := Task) arr_seq sched j t1
              (t1 + Δ) +
            cumulative_interference_from_hep_jobs_from_other_ep_tasks (Task := Task) arr_seq sched j
              t1 (t1 + Δ) := by
  intro hcompat huni j t1 Δ
  unfold cumulative_another_task_hep_job_interference
    cumulative_interference_from_hep_jobs_from_hp_tasks
    cumulative_interference_from_hep_jobs_from_other_ep_tasks
  rw [← sumSeq_add]
  apply sumSeq_congr
  intro t _
  rw [hep_interference_another_task_split arr_seq sched FP JLFP hcompat j t]
  cases ha : hep_job_from_hp_task_interference (Task := Task) arr_seq sched j t <;>
    cases hb : hep_job_from_other_ep_task_interference (Task := Task) arr_seq sched j t
  · rfl
  · rfl
  · rfl
  · exfalso
    unfold hep_job_from_hp_task_interference at ha
    unfold hep_job_from_other_ep_task_interference at hb
    obtain ⟨x, hx, hpx⟩ := List.any_eq_true.mp ha
    obtain ⟨y, hy, hpy⟩ := List.any_eq_true.mp hb
    have rx := served_at_and_receives_service_consistent arr_seq sched x t (decide_eq_true hx)
    have ry := served_at_and_receives_service_consistent arr_seq sched y t (decide_eq_true hy)
    have hxy := only_one_job_receives_service_at_uni huni sched x y t rx ry
    subst hxy
    unfold hp_task_hep_job at hpx
    unfold other_ep_task_hep_job ep_task_hep_job at hpy
    simp only [Bool.and_eq_true] at hpx hpy
    have := ep_not_hp_task FP _ _ hpy.1.2
    rw [hpx.2] at this
    exact absurd this (by decide)

/-- Without supply there is no interference from another higher-or-equal-priority job. -/
theorem no_hep_job_interference_without_supply {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (JLFP : JLFP_policy Job) (t : instant) :
    (!has_supply sched t) = true →
      ∀ j : Job, (!another_hep_job_interference arr_seq sched j t) = true := by
  intro hns j
  unfold another_hep_job_interference
  simp only [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro x hx _
  have rx := served_at_and_receives_service_consistent arr_seq sched x t (decide_eq_true hx)
  have := receives_service_implies_has_supply sched x t rx
  rw [this] at hns
  exact absurd hns (by decide)

/-- Without supply there is no interference from higher-or-equal-priority jobs of
other tasks. -/
theorem no_hep_task_interference_without_supply {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (JLFP : JLFP_policy Job)
    (t : instant) :
    (!has_supply sched t) = true →
      ∀ j : Job, (!another_task_hep_job_interference (Task := Task) arr_seq sched j t) = true := by
  intro hns j
  unfold another_task_hep_job_interference
  simp only [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro x hx _
  have rx := served_at_and_receives_service_consistent arr_seq sched x t (decide_eq_true hx)
  have := receives_service_implies_has_supply sched x t rx
  rw [this] at hns
  exact absurd hns (by decide)

/-- When the schedule is idle there is no interference from another
higher-or-equal-priority job. -/
theorem no_hep_job_interference_when_idle {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
        jobs_must_arrive_to_execute sched →
      ∀ (JLFP : JLFP_policy Job) (t : instant), is_idle arr_seq sched t = true →
        ∀ j : Job, (!another_hep_job_interference arr_seq sched j t) = true := by
  intro hva sched hfrom hmust JLFP t hidle j
  unfold another_hep_job_interference
  simp only [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro x hx _
  have rx := served_at_and_receives_service_consistent arr_seq sched x t (decide_eq_true hx)
  have := no_service_received_when_idle arr_seq hva sched hfrom hmust x t hidle
  rw [rx] at this
  exact absurd this (by decide)

/-- When the schedule is idle there is no interference from higher-or-equal-priority
jobs of other tasks. -/
theorem no_hep_task_interference_when_idle {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
        jobs_must_arrive_to_execute sched →
      ∀ (JLFP : JLFP_policy Job) (t : instant), is_idle arr_seq sched t = true →
        ∀ j : Job, (!another_task_hep_job_interference (Task := Task) arr_seq sched j t) = true := by
  intro hva sched hfrom hmust JLFP t hidle j
  unfold another_task_hep_job_interference
  simp only [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro x hx _
  have rx := served_at_and_receives_service_consistent arr_seq sched x t (decide_eq_true hx)
  have := no_service_received_when_idle arr_seq hva sched hfrom hmust x t hidle
  rw [rx] at this
  exact absurd this (by decide)

/-- A served job is the scheduled job on a uniprocessor. -/
private theorem served_is_scheduled {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (huni : uniprocessor_model PState)
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (t : instant) (x j' : Job)
    (hx : x ∈ served_jobs_at arr_seq sched t) (hs : scheduled_at sched j' t = true) : x = j' := by
  have rx := served_at_and_receives_service_consistent arr_seq sched x t (decide_eq_true hx)
  have sx := service_at_implies_scheduled_at sched x t (of_decide_eq_true rx)
  exact huni x j' sched t sx hs

/-- With supply and a scheduled job `j'`, interference from another
higher-or-equal-priority job is `another_hep_job j' j`. -/
theorem interference_ahep_def {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
      ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
        jobs_must_arrive_to_execute sched →
      ∀ (JLFP : JLFP_policy Job) (j : Job) (t : instant), has_supply sched t = true →
      ∀ j' : Job, scheduled_at sched j' t = true →
        another_hep_job_interference arr_seq sched j t = another_hep_job j' j := by
  intro huni hcons arr_seq hva sched hfrom hmust JLFP j t hsup j' hs
  unfold another_hep_job_interference
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hp⟩
    rw [served_is_scheduled huni arr_seq sched t x j' hx hs] at hp
    exact hp
  · intro hp
    have rj := ideal_progress_inside_supplies hcons sched j' t hsup hs
    exact ⟨j', of_decide_eq_true
      (receives_service_and_served_at_consistent arr_seq hva sched hfrom hmust j' t rj), hp⟩

/-- With supply and a scheduled job `j'`, interference from a higher-or-equal-priority
job of another task is `another_task_hep_job j' j`. -/
theorem interference_athep_def {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
      ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
        jobs_must_arrive_to_execute sched →
      ∀ (JLFP : JLFP_policy Job) (j : Job) (t : instant), has_supply sched t = true →
      ∀ j' : Job, scheduled_at sched j' t = true →
        another_task_hep_job_interference (Task := Task) arr_seq sched j t =
          another_task_hep_job (Task := Task) j' j := by
  intro huni hcons arr_seq hva sched hfrom hmust JLFP j t hsup j' hs
  unfold another_task_hep_job_interference
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hp⟩
    rw [served_is_scheduled huni arr_seq sched t x j' hx hs] at hp
    exact hp
  · intro hp
    have rj := ideal_progress_inside_supplies hcons sched j' t hsup hs
    exact ⟨j', of_decide_eq_true
      (receives_service_and_served_at_consistent arr_seq hva sched hfrom hmust j' t rj), hp⟩

/-- If `j` is scheduled, there is no interference from another
higher-or-equal-priority job. -/
theorem no_ahep_interference_when_scheduled {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState →
      ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState) (JLFP : JLFP_policy Job)
        (j : Job) (t : instant), scheduled_at sched j t = true →
        (!another_hep_job_interference arr_seq sched j t) = true := by
  intro huni arr_seq sched JLFP j t hs
  unfold another_hep_job_interference
  simp only [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro x hx hp
  rw [served_is_scheduled huni arr_seq sched t x j hx hs] at hp
  exact another_hep_job_antireflexive j hp

/-- If `j` is served, there is no interference from another
higher-or-equal-priority job. -/
theorem no_ahep_interference_when_served {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
      ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
        jobs_must_arrive_to_execute sched →
      ∀ (JLFP : JLFP_policy Job) (j : Job) (t : instant), has_supply sched t = true →
        receives_service_at sched j t = true →
        (!another_hep_job_interference arr_seq sched j t) = true := by
  intro huni _ arr_seq _ sched _ _ JLFP j t _ hr
  exact no_ahep_interference_when_scheduled huni arr_seq sched JLFP j t
    (service_at_implies_scheduled_at sched j t (of_decide_eq_true hr))

/-- If a job of the same task is scheduled, there is no interference from
higher-or-equal-priority jobs of other tasks. -/
theorem no_athep_interference_when_scheduled {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job} :
    uniprocessor_model PState →
      ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState) (tsk : Task)
        (JLFP : JLFP_policy Job) (j : Job), job_of_task tsk j = true →
      ∀ (t : instant) (j' : Job), job_of_task tsk j' = true → scheduled_at sched j' t = true →
        (!another_task_hep_job_interference (Task := Task) arr_seq sched j t) = true := by
  intro huni arr_seq sched tsk JLFP j hj t j' hj' hs
  unfold another_task_hep_job_interference
  simp only [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro x hx hp
  rw [served_is_scheduled huni arr_seq sched t x j' hx hs] at hp
  exact another_task_hep_job_taskwise_antireflexive tsk j j' hj hj' hp

/-- If a job `j'` of another task is scheduled with supply, `j` incurs
higher-or-equal-priority interference from another task iff `j'` has
higher-or-equal priority. -/
theorem athep_interference_iff {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
      ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
        jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (JLFP : JLFP_policy Job) (j : Job), job_of_task tsk j = true →
      ∀ t : instant, has_supply sched t = true →
      ∀ j' : Job, (!job_of_task tsk j') = true → scheduled_at sched j' t = true →
        another_task_hep_job_interference (Task := Task) arr_seq sched j t = hep_job j' j := by
  intro huni hcons arr_seq hva sched hfrom hmust tsk JLFP j hj t hsup j' hj' hs
  rw [interference_athep_def huni hcons arr_seq hva sched hfrom hmust JLFP j t hsup j' hs]
  unfold another_task_hep_job
  unfold job_of_task at hj hj'
  have e := of_decide_eq_true hj
  have hne : job_task (Task := Task) j' ≠ job_task (Task := Task) j := by
    rw [e]; intro h; simp [h] at hj'
  simp [hne]

/-- If moreover `j'` has higher-or-equal priority, `j` incurs such interference. -/
theorem athep_interference_if {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobArrival Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
      ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_come_from_arrival_sequence sched arr_seq →
        jobs_must_arrive_to_execute sched →
      ∀ (tsk : Task) (JLFP : JLFP_policy Job) (j : Job), job_of_task tsk j = true →
      ∀ t : instant, has_supply sched t = true →
      ∀ j' : Job, (!job_of_task tsk j') = true → scheduled_at sched j' t = true →
        hep_job j' j = true →
        another_task_hep_job_interference (Task := Task) arr_seq sched j t = true := by
  intro huni hcons arr_seq hva sched hfrom hmust tsk JLFP j hj t hsup j' hj' hs hhep
  rw [athep_interference_iff huni hcons arr_seq hva sched hfrom hmust tsk JLFP j hj t hsup j'
    hj' hs]
  exact hhep

/-- If a lower-priority job is scheduled, there is no interference from another
higher-or-equal-priority job. -/
theorem no_ahep_interference_when_scheduled_lp {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState →
      ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState) (JLFP : JLFP_policy Job)
        (j : Job) (t : instant) (j' : Job), scheduled_at sched j' t = true →
        (!hep_job j' j) = true →
        (!another_hep_job_interference arr_seq sched j t) = true := by
  intro huni arr_seq sched JLFP j t j' hs hlp
  unfold another_hep_job_interference
  simp only [Bool.not_eq_true']
  apply List.any_eq_false.mpr
  intro x hx hp
  rw [served_is_scheduled huni arr_seq sched t x j' hx hs] at hp
  unfold another_hep_job at hp
  simp only [Bool.and_eq_true] at hp
  rw [hp.1] at hlp
  exact absurd hlp (by decide)

/-- The cumulative interference from other higher-or-equal-priority jobs is their
service, from a quiet time on. -/
theorem cumulative_i_ohep_eq_service_of_ohep {Job : JobType} [DecidableEq Job] [JobArrival Job]
    [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState →
      ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
        completed_jobs_dont_execute sched →
      ∀ JLFP : JLFP_policy Job, unit_service_proc_model PState →
      ∀ (j : Job) (t1 t : instant), quiet_time arr_seq sched j t1 →
        cumulative_another_hep_job_interference arr_seq sched j t1 t =
          service_of_other_hep_jobs arr_seq sched j t1 t := by
  intro huni arr_seq hva sched hmust hcd JLFP hu j t1 t hquiet
  unfold cumulative_another_hep_job_interference another_hep_job_interference
  rw [sumSeq_range'_eq]
  exact cumulative_pred_served_eq_service hu huni arr_seq hva.1 sched hmust hcd
    (fun x => another_hep_job x j) hva.2 JLFP j t1 t hquiet
    (fun j' h => by unfold another_hep_job at h; simp only [Bool.and_eq_true] at h; exact h.1)

/-- The cumulative interference from higher-or-equal-priority jobs of other tasks is
their service, from a quiet time on. -/
theorem cumulative_i_thep_eq_service_of_othep {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState →
      ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
        completed_jobs_dont_execute sched →
      ∀ JLFP : JLFP_policy Job, unit_service_proc_model PState →
      ∀ (j : Job) (t1 t : instant), quiet_time arr_seq sched j t1 →
        cumulative_another_task_hep_job_interference (Task := Task) arr_seq sched j t1 t =
          service_of_other_task_hep_jobs (Task := Task) arr_seq sched j t1 t := by
  intro huni arr_seq hva sched hmust hcd JLFP hu j t1 t hquiet
  unfold cumulative_another_task_hep_job_interference another_task_hep_job_interference
  rw [sumSeq_range'_eq]
  exact cumulative_pred_served_eq_service hu huni arr_seq hva.1 sched hmust hcd
    (fun x => another_task_hep_job (Task := Task) x j) hva.2 JLFP j t1 t hquiet
    (fun j' h => by unfold another_task_hep_job at h; simp only [Bool.and_eq_true] at h; exact h.1)

end Prosa.Analysis.Facts.Interference
