-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/basic/constrained_deadlines.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 42)

import Prosa.Classic.Util.Counting
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Basic.Platform

/-!
Absence of multiple pending jobs of the same task under constrained deadlines, in
global schedules (Rocq module `ConstrainedDeadlines`).

Representation notes: `count P ts` over a task set is `ts.val.countP P`; the
section-local `Let scheduled_task_other_than tsk tsk_other` is unfolded to
`task_is_scheduled job_task sched tsk_other t && !decide (tsk_other = tsk)` and
`Let is_hp_task` to `higher_priority_task higher_eq_priority tsk`.  Binder lists
follow the Rocq contract, which records exactly the section variables each
declaration abstracts (e.g. `platform_at_most_one_pending_job_of_each_task` takes
`H_valid_task` and `H_job_of_tsk`, and `scheduled_task_with_higher_eq_priority`
takes the section `tsk` and `t` followed by its own, unused, parameter `tsk`,
named `_tsk` here).
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Global.Basic.ConstrainedDeadlines.ConstrainedDeadlines

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Util.Counting

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: membership in the jobs scheduled at `t` is being scheduled at `t`. -/
private theorem mem_jobs_scheduled_iff {Job : Type v} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) :
    j ∈ jobs_scheduled_at sched t ↔ scheduled sched j t = true := by
  rw [← mem_scheduled_jobs_eq_scheduled, decide_eq_true_iff]

/-- LEAN_HELPER: a job is scheduled iff some processor runs it. -/
private theorem scheduled_iff_exists {Job : Type v} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) :
    scheduled sched j t = true ↔ ∃ cpu, sched cpu t = some j := by
  simp [scheduled, scheduled_on, List.any_eq_true]

/-- LEAN_HELPER: a pending job has arrived and is not completed. -/
private theorem pending_iff {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (t : time) :
    pending job_arrival job_cost sched j t = true ↔
      job_arrival j ≤ t ∧ completed job_cost sched j t = false := by
  simp [pending, has_arrived]

/-- LEAN_HELPER: the jobs scheduled at `t` belong to tasks that are scheduled at `t`. -/
private theorem task_is_scheduled_of_scheduled {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (t : time)
    (h : scheduled sched j t = true) :
    task_is_scheduled job_task sched (job_task j) t = true := by
  obtain ⟨cpu, hcpu⟩ := (scheduled_iff_exists sched j t).mp h
  simp only [task_is_scheduled, List.any_eq_true, List.mem_finRange, true_and]
  exact ⟨cpu, by simp [task_scheduled_on, hcpu]⟩

/-- LEAN_HELPER: at most `num_cpus` tasks of a task set are scheduled at `t`
(the first half of both counting lemmas). -/
private theorem count_task_is_scheduled_le {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (ts : taskset_of sporadic_task)
    (t : time) (P : sporadic_task → Bool)
    (hP : ∀ x, P x = true → task_is_scheduled job_task sched x t = true) :
    ts.val.countP P ≤ num_cpus := by
  apply Nat.le_trans (sub_in_count _ ts.val P (fun x => task_is_scheduled job_task sched x t)
    (fun x _ h => hP x h))
  apply count_exists _ ts.val num_cpus
    (fun x cpu => task_scheduled_on job_task sched x cpu t) ts.nodup
  intro cpu x1 x2 S1 S2
  unfold task_scheduled_on at S1 S2
  cases hs : sched cpu t with
  | none => simp [hs] at S1
  | some k =>
      simp only [hs, decide_eq_true_eq] at S1 S2
      rw [← S1, ← S2]

/-! ### Constrained deadlines: no multiple jobs -/

-- The contract abstracts `H_valid_task` and `H_job_of_tsk`, which this proof does not use.
set_option linter.unusedVariables false in
theorem platform_at_most_one_pending_job_of_each_task {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : sporadic_task)
    (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)
    (j : Job) (H_job_of_tsk : job_task j = tsk) (t : time)
    (H_all_previous_jobs_completed :
      ∀ (j_other : Job) (tsk_other : sporadic_task),
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        job_arrival j_other + task_period tsk_other ≤ t →
        completed job_cost sched j_other
          (job_arrival j_other + task_period (job_task j_other)) = true) :
    ∀ j1 j2 : Job,
      arrives_in arr_seq j1 →
      arrives_in arr_seq j2 →
      pending job_arrival job_cost sched j1 t = true →
      pending job_arrival job_cost sched j2 t = true →
      job_task j1 = job_task j2 →
      j1 = j2 := by
  intro j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk
  by_contra DIFF
  rw [pending_iff] at PENDING1 PENDING2
  obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
  obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
  rcases Nat.le_total (job_arrival j1) (job_arrival j2) with BEFORE1 | BEFORE2
  · have SPO := H_sporadic_tasks j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1
    have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARR1 rfl
      (Nat.le_trans SPO ARRIVED2)
    have := completion_monotonic job_cost sched j1 _ t (Nat.le_trans SPO ARRIVED2) COMP1
    rw [this] at NOTCOMP1
    exact Bool.noConfusion NOTCOMP1
  · have SPO := H_sporadic_tasks j2 j1 (Ne.symm DIFF) ARR2 ARR1 SAMEtsk.symm BEFORE2
    have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARR2 rfl
      (Nat.le_trans SPO ARRIVED1)
    have := completion_monotonic job_cost sched j2 _ t (Nat.le_trans SPO ARRIVED1) COMP2
    rw [this] at NOTCOMP2
    exact Bool.noConfusion NOTCOMP2

theorem platform_cpus_busy_with_interfering_tasks {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (ts : taskset_of sporadic_task)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (H_sequential_jobs : sequential_jobs sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : sporadic_task)
    (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (t : time)
    (H_j_backlogged : backlogged job_arrival job_cost sched j t = true)
    (H_all_previous_jobs_completed :
      ∀ (j_other : Job) (tsk_other : sporadic_task),
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        job_arrival j_other + task_period tsk_other ≤ t →
        completed job_cost sched j_other
          (job_arrival j_other + task_period (job_task j_other)) = true) :
    ts.val.countP (fun tsk_other =>
      task_is_scheduled job_task sched tsk_other t && !decide (tsk_other = tsk)) = num_cpus := by
  have UNIQ := platform_at_most_one_pending_job_of_each_task task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq sched H_sporadic_tasks tsk H_valid_task j H_job_of_tsk t
    H_all_previous_jobs_completed
  have WORK := (work_conserving_eq_work_conserving_count job_arrival job_cost arr_seq sched).mp
    H_work_conserving
  have hPEND : ∀ j', scheduled sched j' t = true → pending job_arrival job_cost sched j' t = true :=
    fun j' h => scheduled_implies_pending job_arrival job_cost sched j'
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t h
  have BACK := H_j_backlogged
  simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true'] at BACK
  obtain ⟨PENDj, NOTSCHEDj⟩ := BACK
  apply Nat.le_antisymm
  · apply count_task_is_scheduled_le job_task sched ts t
    intro x hx
    simp only [Bool.and_eq_true] at hx
    exact hx.1
  · apply Nat.le_trans (Nat.le_of_eq (WORK j t H_j_arrives H_j_backlogged).symm)
    rw [← List.countP_true]
    calc (jobs_scheduled_at sched t).countP (fun _ => true)
        ≤ (jobs_scheduled_at sched t).countP (fun j' =>
            task_is_scheduled job_task sched (job_task j') t &&
              !decide (job_task j' = tsk)) := by
          apply sub_in_count
          intro j' SCHED' _
          rw [mem_jobs_scheduled_iff] at SCHED'
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
          refine ⟨task_is_scheduled_of_scheduled job_task sched j' t SCHED', ?_⟩
          intro SAMEtsk
          have ARRin' := H_jobs_come_from_arrival_sequence j' t SCHED'
          have EQ := UNIQ j j' H_j_arrives ARRin' PENDj (hPEND j' SCHED')
            (by rw [SAMEtsk, H_job_of_tsk])
          subst EQ
          rw [SCHED'] at NOTSCHEDj
          exact Bool.noConfusion NOTSCHEDj
      _ = ((jobs_scheduled_at sched t).map job_task).countP (fun tsk_other =>
            task_is_scheduled job_task sched tsk_other t && !decide (tsk_other = tsk)) := by
          rw [List.countP_map]; rfl
      _ ≤ ts.val.countP (fun tsk_other =>
            task_is_scheduled job_task sched tsk_other t && !decide (tsk_other = tsk)) := by
          apply count_sub_uniqr
          · apply List.Nodup.map_on _ (scheduled_jobs_uniq sched H_sequential_jobs t)
            intro j1 SCHED1 j2 SCHED2 SAMEtsk
            rw [mem_jobs_scheduled_iff] at SCHED1 SCHED2
            exact UNIQ j1 j2 (H_jobs_come_from_arrival_sequence j1 t SCHED1)
              (H_jobs_come_from_arrival_sequence j2 t SCHED2) (hPEND j1 SCHED1)
              (hPEND j2 SCHED2) SAMEtsk
          · intro x hx
            obtain ⟨j', IN', rfl⟩ := List.mem_map.mp hx
            rw [mem_jobs_scheduled_iff] at IN'
            exact H_all_jobs_from_taskset j' (H_jobs_come_from_arrival_sequence j' t IN')

/-! ### Constrained deadlines under fixed-priority scheduling -/

def scheduled_task_with_higher_eq_priority {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task) (t : time)
    (_tsk tsk_other : sporadic_task) : Bool :=
  task_is_scheduled job_task sched tsk_other t &&
    higher_priority_task higher_eq_priority tsk tsk_other

theorem platform_fp_no_multiple_jobs_of_interfering_tasks {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_period : sporadic_task → time) {Job : Type v}
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : sporadic_task) (t : time)
    (H_all_previous_jobs_completed :
      ∀ (j_other : Job) (tsk_other : sporadic_task),
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        higher_priority_task higher_eq_priority tsk tsk_other = true →
        completed job_cost sched j_other (job_arrival j_other + task_period tsk_other) = true) :
    ∀ j1 j2 : Job,
      arrives_in arr_seq j1 →
      arrives_in arr_seq j2 →
      pending job_arrival job_cost sched j1 t = true →
      pending job_arrival job_cost sched j2 t = true →
      job_task j1 = job_task j2 →
      higher_priority_task higher_eq_priority tsk (job_task j1) = true →
      j1 = j2 := by
  intro j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk INTERF
  by_contra DIFF
  rw [pending_iff] at PENDING1 PENDING2
  obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
  obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
  rcases Nat.le_total (job_arrival j1) (job_arrival j2) with BEFORE1 | BEFORE2
  · have SPO := H_sporadic_tasks j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1
    have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARR1 rfl INTERF
    have := completion_monotonic job_cost sched j1 _ t (Nat.le_trans SPO ARRIVED2) COMP1
    rw [this] at NOTCOMP1
    exact Bool.noConfusion NOTCOMP1
  · have SPO := H_sporadic_tasks j2 j1 (Ne.symm DIFF) ARR2 ARR1 SAMEtsk.symm BEFORE2
    have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARR2 rfl (SAMEtsk ▸ INTERF)
    have := completion_monotonic job_cost sched j2 _ t (Nat.le_trans SPO ARRIVED1) COMP2
    rw [this] at NOTCOMP2
    exact Bool.noConfusion NOTCOMP2

theorem platform_fp_no_multiple_jobs_of_tsk {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : sporadic_task)
    (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (t : time)
    (H_j_backlogged : backlogged job_arrival job_cost sched j t = true)
    (H_t_before_period : t < job_arrival j + task_period tsk)
    (H_all_previous_jobs_of_tsk_completed :
      ∀ j0 : Job,
        arrives_in arr_seq j0 →
        job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + task_period tsk) = true) :
    ∀ j' : Job,
      arrives_in arr_seq j' →
      pending job_arrival job_cost sched j' t = true →
      job_task j' = tsk →
      j' = j := by
  intro j' ARR' PENDING' SAMEtsk
  by_contra DIFF
  have BACK := H_j_backlogged
  simp only [backlogged, Bool.and_eq_true] at BACK
  obtain ⟨PENDj, _⟩ := BACK
  rw [pending_iff] at PENDj PENDING'
  obtain ⟨ARRIVED, _⟩ := PENDj
  obtain ⟨ARRIVED', NOTCOMP'⟩ := PENDING'
  have PERIOD : 0 < task_period tsk := by
    have := H_valid_task.2.1
    simpa [task_period_positive] using this
  rcases Nat.le_total (job_arrival j') (job_arrival j) with BEFORE | BEFORE'
  · have SPO := H_sporadic_tasks j' j DIFF ARR' H_j_arrives (by rw [SAMEtsk, H_job_of_tsk])
      BEFORE
    rw [SAMEtsk] at SPO
    have COMP := H_all_previous_jobs_of_tsk_completed j' ARR' SAMEtsk (by omega')
    have := completion_monotonic job_cost sched j' _ t (Nat.le_trans SPO ARRIVED) COMP
    rw [this] at NOTCOMP'
    exact Bool.noConfusion NOTCOMP'
  · have SPO := H_sporadic_tasks j j' (Ne.symm DIFF) H_j_arrives ARR'
      (by rw [SAMEtsk, H_job_of_tsk]) BEFORE'
    rw [H_job_of_tsk] at SPO
    omega'

theorem platform_fp_cpus_busy_with_interfering_tasks {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_JLDP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (ts : taskset_of sporadic_task)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (H_sequential_jobs : sequential_jobs sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : sporadic_task)
    (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk) (t : time)
    (H_j_backlogged : backlogged job_arrival job_cost sched j t = true)
    (H_t_before_period : t < job_arrival j + task_period tsk)
    (H_all_previous_jobs_completed :
      ∀ (j_other : Job) (tsk_other : sporadic_task),
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        higher_priority_task higher_eq_priority tsk tsk_other = true →
        completed job_cost sched j_other (job_arrival j_other + task_period tsk_other) = true)
    (H_all_previous_jobs_of_tsk_completed :
      ∀ j0 : Job,
        arrives_in arr_seq j0 →
        job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + task_period tsk) = true) :
    ts.val.countP
      (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority tsk t tsk) =
      num_cpus := by
  have UNIQ := platform_fp_no_multiple_jobs_of_interfering_tasks task_period job_arrival job_cost
    job_task arr_seq sched higher_eq_priority H_sporadic_tasks tsk t H_all_previous_jobs_completed
  have UNIQ' := platform_fp_no_multiple_jobs_of_tsk task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq sched H_sporadic_tasks tsk H_valid_task j H_j_arrives
    H_job_of_tsk t H_j_backlogged H_t_before_period H_all_previous_jobs_of_tsk_completed
  have WORK := (work_conserving_eq_work_conserving_count job_arrival job_cost arr_seq sched).mp
    H_work_conserving
  have hPEND : ∀ j', scheduled sched j' t = true → pending job_arrival job_cost sched j' t = true :=
    fun j' h => scheduled_implies_pending job_arrival job_cost sched j'
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t h
  have BACK := H_j_backlogged
  simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true'] at BACK
  obtain ⟨_, NOTSCHEDj⟩ := BACK
  set P := scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority tsk t tsk
    with hP
  apply Nat.le_antisymm
  · apply count_task_is_scheduled_le job_task sched ts t
    intro x hx
    simp only [hP, scheduled_task_with_higher_eq_priority, Bool.and_eq_true] at hx
    exact hx.1
  · apply Nat.le_trans (Nat.le_of_eq (WORK j t H_j_arrives H_j_backlogged).symm)
    rw [← List.countP_true]
    calc (jobs_scheduled_at sched t).countP (fun _ => true)
        ≤ (jobs_scheduled_at sched t).countP (fun j' => P (job_task j')) := by
          apply sub_in_count
          intro j' SCHED' _
          rw [mem_jobs_scheduled_iff] at SCHED'
          simp only [hP, scheduled_task_with_higher_eq_priority, higher_priority_task,
            Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
          refine ⟨task_is_scheduled_of_scheduled job_task sched j' t SCHED', ?_, ?_⟩
          · rw [← H_job_of_tsk]
            exact H_respects_JLDP_policy j j' t H_j_arrives H_j_backlogged SCHED'
          · intro SAMEtsk
            have EQ := UNIQ' j' (H_jobs_come_from_arrival_sequence j' t SCHED')
              (hPEND j' SCHED') SAMEtsk
            subst EQ
            rw [SCHED'] at NOTSCHEDj
            exact Bool.noConfusion NOTSCHEDj
      _ = (((jobs_scheduled_at sched t).map job_task).filter P).length := by
          rw [List.countP_eq_length_filter, List.filter_map, List.length_map]; rfl
      _ = (((jobs_scheduled_at sched t).map job_task).filter P).countP P := by
          rw [List.countP_eq_length_filter, List.filter_filter]
          simp
      _ ≤ ts.val.countP P := by
          apply count_sub_uniqr
          · rw [List.filter_map]
            apply List.Nodup.map_on _
              ((scheduled_jobs_uniq sched H_sequential_jobs t).filter _)
            intro j1 IN1 j2 IN2 SAMEtsk
            rw [List.mem_filter] at IN1 IN2
            obtain ⟨SCHED1, HP1⟩ := IN1
            obtain ⟨SCHED2, _⟩ := IN2
            rw [mem_jobs_scheduled_iff] at SCHED1 SCHED2
            simp only [Function.comp, hP, scheduled_task_with_higher_eq_priority,
              Bool.and_eq_true] at HP1
            exact UNIQ j1 j2 (H_jobs_come_from_arrival_sequence j1 t SCHED1)
              (H_jobs_come_from_arrival_sequence j2 t SCHED2) (hPEND j1 SCHED1)
              (hPEND j2 SCHED2) SAMEtsk HP1.2
          · intro x hx
            obtain ⟨hx, _⟩ := List.mem_filter.mp hx
            obtain ⟨j', IN', rfl⟩ := List.mem_map.mp hx
            rw [mem_jobs_scheduled_iff] at IN'
            exact H_all_jobs_from_taskset j' (H_jobs_come_from_arrival_sequence j' t IN')

end Prosa.Classic.Model.Schedule.Global.Basic.ConstrainedDeadlines.ConstrainedDeadlines
