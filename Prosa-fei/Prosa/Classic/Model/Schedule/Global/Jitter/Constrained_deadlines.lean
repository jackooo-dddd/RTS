-- Translated from: ../rt-proofs/classic/model/schedule/global/jitter/constrained_deadlines.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Priority
import Prosa.Classic.Util.Counting
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule

namespace Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Job (valid_sporadic_job)
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence (arrival_sequence arrives_in)
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Model.Priority
open Schedule

def task_scheduled_on {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_task : Job → sporadic_task) {num_cpus : ℕ}
    (sched : schedule Job num_cpus) (tsk : sporadic_task)
    (cpu : processor num_cpus) (t : Time) : Bool :=
  match sched cpu t with
  | some j => decide (job_task j = tsk)
  | none => false

def task_is_scheduled {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_task : Job → sporadic_task) {num_cpus : ℕ}
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (t : Time) : Bool :=
  decide (∃ cpu : Fin num_cpus, task_scheduled_on job_task sched tsk cpu t = true)

def actual_arrival {Job : Type _}
    (job_arrival : Job → Time) (job_jitter : Job → Time) (j : Job) : Time :=
  job_arrival j + job_jitter j

def jitter_has_passed {Job : Type _}
    (job_arrival : Job → Time) (job_jitter : Job → Time)
    (j : Job) (t : Time) : Prop :=
  actual_arrival job_arrival job_jitter j ≤ t

def pending_jitter {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time) {num_cpus : ℕ}
    (sched : schedule Job num_cpus) (j : Job) (t : Time) : Prop :=
  jitter_has_passed job_arrival job_jitter j t ∧
  ¬ completed job_cost sched j t

def backlogged_jitter {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time) {num_cpus : ℕ}
    (sched : schedule Job num_cpus) (j : Job) (t : Time) : Prop :=
  pending_jitter job_arrival job_cost job_jitter sched j t ∧
  ¬ scheduled sched j t

def jobs_execute_after_jitter {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_jitter : Job → Time)
    {num_cpus : ℕ} (sched : schedule Job num_cpus) : Prop :=
  ∀ j t, scheduled sched j t → jitter_has_passed job_arrival job_jitter j t

def work_conserving
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time)
    (arr_seq : arrival_sequence Job)
    {num_cpus : ℕ} (sched : schedule Job num_cpus) : Prop :=
  ∀ j t,
    arrives_in arr_seq j →
    backlogged_jitter job_arrival job_cost job_jitter sched j t →
    ∀ cpu, ∃ j_other, scheduled_on sched j_other cpu t = true

def work_conserving_count
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time)
    (arr_seq : arrival_sequence Job)
    {num_cpus : ℕ} (sched : schedule Job num_cpus) : Prop :=
  ∀ j t,
    arrives_in arr_seq j →
    backlogged_jitter job_arrival job_cost job_jitter sched j t →
    (jobs_scheduled_at sched t).length = num_cpus

def respects_FP_policy_jitter {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_task : Job → sporadic_task)
    (job_jitter : Job → Time)
    (arr_seq : arrival_sequence Job)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (higher_eq_priority : FP_policy sporadic_task) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    backlogged_jitter job_arrival job_cost job_jitter sched j t →
    scheduled sched j_hp t →
    higher_eq_priority (job_task j_hp) (job_task j) = true

def respects_JLDP_policy_jitter
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time)
    (arr_seq : arrival_sequence Job)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (higher_eq_priority : JLDP_policy Job) : Prop :=
  ∀ j j_hp t,
    arrives_in arr_seq j →
    backlogged_jitter job_arrival job_cost job_jitter sched j t →
    scheduled sched j_hp t →
    higher_eq_priority t j_hp j = true

def sporadic_task_model {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (task_period : sporadic_task → Time)
    (job_arrival : Job → Time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ (j j' : Job),
    j ≠ j' →
    arrives_in arr_seq j →
    arrives_in arr_seq j' →
    job_task j = job_task j' →
    job_arrival j ≤ job_arrival j' →
    job_arrival j' ≥ job_arrival j + task_period (job_task j)

section Lemmas

  variable {sporadic_task : Type _} [DecidableEq sporadic_task]
  variable (task_cost : sporadic_task → Time)
  variable (task_period : sporadic_task → Time)
  variable (task_deadline : sporadic_task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_task : Job → sporadic_task)
  variable (job_jitter : Job → Time)

  variable (arr_seq : arrival_sequence Job)

  variable {num_cpus : ℕ}
  variable (sched : schedule Job num_cpus)
  variable (H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_valid_job_parameters :
    ∀ j,
      arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

  section NoMultipleJobs

    variable (higher_eq_priority : JLDP_policy Job)
    variable (H_work_conserving :
      work_conserving job_arrival job_cost job_jitter arr_seq sched)
    variable (H_respects_JLDP_policy :
      respects_JLDP_policy_jitter job_arrival job_cost job_jitter arr_seq sched higher_eq_priority)

    variable (ts : List sporadic_task)
    variable (H_ts_nodup : ts.Nodup)

    variable (H_all_jobs_from_taskset :
      ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

    variable (H_sequential_jobs : sequential_jobs sched)
    variable (H_jobs_execute_after_jitter :
      jobs_execute_after_jitter job_arrival job_jitter sched)
    variable (H_completed_jobs_dont_execute :
      completed_jobs_dont_execute job_cost sched)

    variable (H_sporadic_tasks :
      sporadic_task_model task_period job_arrival job_task arr_seq)

    variable (tsk : sporadic_task)
    variable (H_valid_task :
      SporadicTask.is_valid_sporadic_task task_cost task_period task_deadline tsk)

    variable (j : Job)
    variable (H_j_arrives : arrives_in arr_seq j)
    variable (H_job_of_tsk : job_task j = tsk)

    variable (t : Time)
    variable (H_j_backlogged :
      backlogged_jitter job_arrival job_cost job_jitter sched j t)

    variable (H_all_previous_jobs_completed :
      ∀ j_other tsk_other,
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        job_arrival j_other + task_period tsk_other ≤ t →
        completed job_cost sched j_other
          (job_arrival j_other + task_period (job_task j_other)))

    include H_jobs_come_from_arrival_sequence H_valid_job_parameters
    include H_work_conserving H_respects_JLDP_policy H_all_jobs_from_taskset
    include H_sequential_jobs H_jobs_execute_after_jitter H_completed_jobs_dont_execute
    include H_sporadic_tasks H_valid_task H_j_arrives H_job_of_tsk
    include H_j_backlogged H_all_previous_jobs_completed

    def scheduled_task_other_than (tsk_ref tsk_other : sporadic_task) : Bool :=
      task_is_scheduled job_task sched tsk_other t && decide (tsk_other ≠ tsk_ref)

    theorem platform_at_most_one_pending_job_of_each_task :
        ∀ j1 j2,
          arrives_in arr_seq j1 →
          arrives_in arr_seq j2 →
          pending_jitter job_arrival job_cost job_jitter sched j1 t →
          pending_jitter job_arrival job_cost job_jitter sched j2 t →
          job_task j1 = job_task j2 →
          j1 = j2 := by
      intro j1 j2 ARRin1 ARRin2 PENDING1 PENDING2 SAMEtsk
      by_contra DIFF
      obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
      obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
      unfold jitter_has_passed actual_arrival at ARRIVED1 ARRIVED2
      by_cases h : job_arrival j1 ≤ job_arrival j2
      · -- j1 arrives before or at j2
        have SPO' := H_sporadic_tasks j1 j2 DIFF ARRin1 ARRin2 SAMEtsk h
        have LEt : job_arrival j1 + task_period (job_task j1) ≤ t := by
          calc job_arrival j1 + task_period (job_task j1)
              ≤ job_arrival j2 := SPO'
            _ ≤ job_arrival j2 + job_jitter j2 := Nat.le_add_right _ _
            _ ≤ t := ARRIVED2
        have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARRin1 rfl LEt
        exact NOTCOMP1 (completion_monotonic job_cost sched j1 H_completed_jobs_dont_execute
          (job_arrival j1 + task_period (job_task j1)) t LEt COMP1)
      · -- j2 arrives before j1
        push_neg at h
        have h' : job_arrival j2 ≤ job_arrival j1 := Nat.le_of_lt h
        have DIFF' : j2 ≠ j1 := Ne.symm DIFF
        have SAMEtsk' : job_task j2 = job_task j1 := SAMEtsk.symm
        have SPO' := H_sporadic_tasks j2 j1 DIFF' ARRin2 ARRin1 SAMEtsk' h'
        have LEt : job_arrival j2 + task_period (job_task j2) ≤ t := by
          calc job_arrival j2 + task_period (job_task j2)
              ≤ job_arrival j1 := SPO'
            _ ≤ job_arrival j1 + job_jitter j1 := Nat.le_add_right _ _
            _ ≤ t := ARRIVED1
        have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARRin2 rfl LEt
        exact NOTCOMP2 (completion_monotonic job_cost sched j2 H_completed_jobs_dont_execute
          (job_arrival j2 + task_period (job_task j2)) t LEt COMP2)

    set_option maxHeartbeats 800000 in
    include H_ts_nodup H_jobs_come_from_arrival_sequence H_valid_job_parameters H_work_conserving H_respects_JLDP_policy H_all_jobs_from_taskset H_sequential_jobs H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sporadic_tasks H_valid_task H_j_arrives H_job_of_tsk H_j_backlogged H_all_previous_jobs_completed in
    theorem platform_cpus_busy_with_interfering_tasks :
        ts.countP (scheduled_task_other_than job_task sched t tsk) = num_cpus := by
      have UNIQ := platform_at_most_one_pending_job_of_each_task task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task job_jitter arr_seq sched
        H_jobs_come_from_arrival_sequence H_valid_job_parameters higher_eq_priority
        H_work_conserving H_respects_JLDP_policy ts H_all_jobs_from_taskset H_sequential_jobs
        H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sporadic_tasks tsk H_valid_task
        j H_j_arrives H_job_of_tsk t H_j_backlogged H_all_previous_jobs_completed
      have BACK := H_j_backlogged
      -- Derive work_conserving_count inline
      have WC_COUNT : (jobs_scheduled_at sched t).length = num_cpus := by
        have h_all := H_work_conserving j t H_j_arrives BACK
        have h_some : ∀ cpu : Fin num_cpus, ∃ j', sched cpu t = some j' := by
          intro cpu
          obtain ⟨j_other, h_on⟩ := h_all cpu
          unfold scheduled_on at h_on
          exact ⟨j_other, eq_of_beq h_on⟩
        unfold jobs_scheduled_at
        rw [Prosa.Classic.Util.Bigcat.size_bigcat_ord]
        calc ∑ i : Fin num_cpus, (match sched i t with | some j => [j] | none => []).length
            = ∑ _i : Fin num_cpus, 1 := by
              apply Finset.sum_congr rfl
              intro i _
              obtain ⟨j', hj'⟩ := h_some i
              rw [hj']; rfl
          _ = num_cpus := by rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
      apply Nat.le_antisymm
      · -- Upper bound: countP ≤ num_cpus
        calc ts.countP (scheduled_task_other_than job_task sched t tsk)
            ≤ ts.countP (fun x => task_is_scheduled job_task sched x t) := by
              apply Prosa.Classic.Util.Counting.sub_in_count
              intro x _ h
              unfold scheduled_task_other_than at h
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              exact h.1
          _ ≤ num_cpus := by
              have h_eq : (fun x => task_is_scheduled job_task sched x t)
                = (fun x => decide (∃ i : Fin num_cpus, task_scheduled_on job_task sched x i t = true)) := by
                ext x; rfl
              rw [h_eq]
              exact Prosa.Classic.Util.Counting.count_exists ts num_cpus
                (fun x cpu => task_scheduled_on job_task sched x cpu t)
                (by exact H_ts_nodup)
                (fun cpu x1 x2 h1 h2 => by
                  unfold task_scheduled_on at h1 h2
                  cases h_sched : sched cpu t with
                  | none => simp [h_sched] at h1
                  | some j0 =>
                    simp [h_sched] at h1 h2
                    rw [← h1, ← h2])
      · -- Lower bound: num_cpus ≤ countP
        suffices h : (jobs_scheduled_at sched t).length ≤ ts.countP (scheduled_task_other_than job_task sched t tsk) by omega
        have h_all_pred : ∀ j', j' ∈ jobs_scheduled_at sched t →
            scheduled_task_other_than job_task sched t tsk (job_task j') = true := by
          intro j' h_mem
          have h_sched : scheduled sched j' t := (mem_scheduled_jobs_eq_scheduled sched j' t).mp h_mem
          unfold scheduled_task_other_than
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · obtain ⟨cpu, h_on⟩ := h_sched
            unfold task_is_scheduled
            simp only [decide_eq_true_eq]
            refine ⟨cpu, ?_⟩
            unfold task_scheduled_on; unfold scheduled_on at h_on
            cases h_eq : sched cpu t with
            | none => simp [h_eq] at h_on
            | some j0 => simp [h_eq] at h_on; simp [h_eq, h_on]
          · intro SAMEtsk
            have ARRin' : arrives_in arr_seq j' := H_jobs_come_from_arrival_sequence j' t h_sched
            have PENDING' : pending_jitter job_arrival job_cost job_jitter sched j' t :=
              Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.scheduled_implies_pending
                job_arrival job_cost job_jitter sched H_jobs_execute_after_jitter H_completed_jobs_dont_execute
                j' t h_sched
            have SAMEtsk' : job_task j' = job_task j := by rw [SAMEtsk, H_job_of_tsk]
            have EQ := UNIQ j j' H_j_arrives ARRin' BACK.1 PENDING' SAMEtsk'.symm
            subst EQ
            exact BACK.2 h_sched
        have h_inj_on : ∀ j1 j2, j1 ∈ jobs_scheduled_at sched t →
            j2 ∈ jobs_scheduled_at sched t → job_task j1 = job_task j2 → j1 = j2 := by
          intro j1 j2 h1 h2 h_eq
          have hs1 := (mem_scheduled_jobs_eq_scheduled sched j1 t).mp h1
          have hs2 := (mem_scheduled_jobs_eq_scheduled sched j2 t).mp h2
          exact UNIQ j1 j2
            (H_jobs_come_from_arrival_sequence j1 t hs1)
            (H_jobs_come_from_arrival_sequence j2 t hs2)
            (Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.scheduled_implies_pending
              job_arrival job_cost job_jitter sched H_jobs_execute_after_jitter H_completed_jobs_dont_execute j1 t hs1)
            (Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.scheduled_implies_pending
              job_arrival job_cost job_jitter sched H_jobs_execute_after_jitter H_completed_jobs_dont_execute j2 t hs2)
            h_eq
        have h_map_nodup : (List.map job_task (jobs_scheduled_at sched t)).Nodup :=
          List.Nodup.map_on (fun x hx y hy h_eq => h_inj_on x y hx hy h_eq) (scheduled_jobs_uniq sched H_sequential_jobs t)
        have h_map_sub : ∀ x, x ∈ List.map job_task (jobs_scheduled_at sched t) → x ∈ ts := by
          intro x hx
          obtain ⟨j', hj'_mem, hj'_eq⟩ := List.mem_map.mp hx
          rw [← hj'_eq]
          exact H_all_jobs_from_taskset j'
            (H_jobs_come_from_arrival_sequence j' t
              ((mem_scheduled_jobs_eq_scheduled sched j' t).mp hj'_mem))
        calc (jobs_scheduled_at sched t).length
            = (List.map job_task (jobs_scheduled_at sched t)).length := (List.length_map ..).symm
          _ = (List.map job_task (jobs_scheduled_at sched t)).countP (fun _ => true) := by
              rw [List.countP_true]
          _ ≤ (List.map job_task (jobs_scheduled_at sched t)).countP
              (scheduled_task_other_than job_task sched t tsk) := by
              apply Prosa.Classic.Util.Counting.sub_in_count
              intro x hx _
              obtain ⟨j', hj'_mem, hj'_eq⟩ := List.mem_map.mp hx
              rw [← hj'_eq]
              exact h_all_pred j' hj'_mem
          _ ≤ ts.countP (scheduled_task_other_than job_task sched t tsk) :=
              Prosa.Classic.Util.Counting.count_sub_uniqr _ _ _ h_map_nodup h_map_sub

  end NoMultipleJobs

  section NoMultipleJobsFP

    variable (higher_eq_priority : FP_policy sporadic_task)
    variable (H_work_conserving :
      work_conserving job_arrival job_cost job_jitter arr_seq sched)
    variable (H_respects_FP_policy :
      respects_FP_policy_jitter job_arrival job_cost job_task job_jitter arr_seq sched higher_eq_priority)

    variable (ts : List sporadic_task)
    variable (H_ts_nodup : ts.Nodup)

    variable (H_all_jobs_from_taskset :
      ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

    variable (H_sequential_jobs : sequential_jobs sched)
    variable (H_jobs_execute_after_jitter :
      jobs_execute_after_jitter job_arrival job_jitter sched)
    variable (H_completed_jobs_dont_execute :
      completed_jobs_dont_execute job_cost sched)

    variable (H_sporadic_tasks :
      sporadic_task_model task_period job_arrival job_task arr_seq)

    variable (tsk : sporadic_task)
    variable (H_valid_task :
      SporadicTask.is_valid_sporadic_task task_cost task_period task_deadline tsk)

    variable (j : Job)
    variable (H_j_arrives : arrives_in arr_seq j)
    variable (H_job_of_tsk : job_task j = tsk)

    variable (t : Time)
    variable (H_j_backlogged :
      backlogged_jitter job_arrival job_cost job_jitter sched j t)
    variable (H_t_before_period : t < job_arrival j + task_period tsk)

    def is_hp_task (tsk_other : sporadic_task) : Bool :=
      higher_priority_task higher_eq_priority tsk tsk_other

    variable (H_all_previous_jobs_completed_fp :
      ∀ j_other tsk_other,
        arrives_in arr_seq j_other →
        job_task j_other = tsk_other →
        is_hp_task higher_eq_priority tsk tsk_other = true →
        completed job_cost sched j_other
          (job_arrival j_other + task_period tsk_other))

    variable (H_all_previous_jobs_of_tsk_completed :
      ∀ j0,
        arrives_in arr_seq j0 →
        job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + task_period tsk))

    include H_jobs_come_from_arrival_sequence H_valid_job_parameters
    include H_work_conserving H_respects_FP_policy H_all_jobs_from_taskset
    include H_sequential_jobs H_jobs_execute_after_jitter H_completed_jobs_dont_execute
    include H_sporadic_tasks H_valid_task H_j_arrives H_job_of_tsk
    include H_j_backlogged H_t_before_period
    include H_all_previous_jobs_completed_fp H_all_previous_jobs_of_tsk_completed

    def scheduled_task_with_higher_eq_priority (tsk_other : sporadic_task) : Bool :=
      task_is_scheduled job_task sched tsk_other t &&
      is_hp_task higher_eq_priority tsk tsk_other

    theorem platform_fp_no_multiple_jobs_of_interfering_tasks :
        ∀ j1 j2,
          arrives_in arr_seq j1 →
          arrives_in arr_seq j2 →
          pending_jitter job_arrival job_cost job_jitter sched j1 t →
          pending_jitter job_arrival job_cost job_jitter sched j2 t →
          job_task j1 = job_task j2 →
          is_hp_task higher_eq_priority tsk (job_task j1) = true →
          j1 = j2 := by
      intro j1 j2 ARRin1 ARRin2 PENDING1 PENDING2 SAMEtsk INTERF
      by_contra DIFF
      obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
      obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
      unfold jitter_has_passed actual_arrival at ARRIVED1 ARRIVED2
      by_cases h : job_arrival j1 ≤ job_arrival j2
      · have SPO' := H_sporadic_tasks j1 j2 DIFF ARRin1 ARRin2 SAMEtsk h
        have LEt : job_arrival j1 + task_period (job_task j1) ≤ t := by
          calc job_arrival j1 + task_period (job_task j1)
              ≤ job_arrival j2 := SPO'
            _ ≤ job_arrival j2 + job_jitter j2 := Nat.le_add_right _ _
            _ ≤ t := ARRIVED2
        have COMP1 := H_all_previous_jobs_completed_fp j1 (job_task j1) ARRin1 rfl INTERF
        exact NOTCOMP1 (completion_monotonic job_cost sched j1 H_completed_jobs_dont_execute
          (job_arrival j1 + task_period (job_task j1)) t LEt COMP1)
      · push_neg at h
        have h' : job_arrival j2 ≤ job_arrival j1 := Nat.le_of_lt h
        have DIFF' : j2 ≠ j1 := Ne.symm DIFF
        have SAMEtsk' : job_task j2 = job_task j1 := SAMEtsk.symm
        have SPO' := H_sporadic_tasks j2 j1 DIFF' ARRin2 ARRin1 SAMEtsk' h'
        have LEt : job_arrival j2 + task_period (job_task j2) ≤ t := by
          calc job_arrival j2 + task_period (job_task j2)
              ≤ job_arrival j1 := SPO'
            _ ≤ job_arrival j1 + job_jitter j1 := Nat.le_add_right _ _
            _ ≤ t := ARRIVED1
        have INTERF2 : is_hp_task higher_eq_priority tsk (job_task j2) = true := by
          rw [SAMEtsk']; exact INTERF
        have COMP2 := H_all_previous_jobs_completed_fp j2 (job_task j2) ARRin2 rfl INTERF2
        exact NOTCOMP2 (completion_monotonic job_cost sched j2 H_completed_jobs_dont_execute
          (job_arrival j2 + task_period (job_task j2)) t LEt COMP2)

    theorem platform_fp_no_multiple_jobs_of_tsk :
        ∀ j',
          arrives_in arr_seq j' →
          pending_jitter job_arrival job_cost job_jitter sched j' t →
          job_task j' = tsk →
          j' = j := by
      intro j' ARRin' PENDING' SAMEtsk
      by_contra DIFF
      obtain ⟨ARRIVED', NOTCOMP'⟩ := PENDING'
      obtain ⟨⟨ARRIVED, NOTCOMP⟩, NOTSCHED⟩ := H_j_backlogged
      unfold jitter_has_passed actual_arrival at ARRIVED ARRIVED'
      by_cases h : job_arrival j' ≤ job_arrival j
      · -- j' arrives before or at j
        have DIFF' : j' ≠ j := DIFF
        have SAMEtsk' : job_task j' = job_task j := SAMEtsk ▸ H_job_of_tsk.symm
        have SPO' := H_sporadic_tasks j' j DIFF' ARRin' H_j_arrives SAMEtsk' h
        have LEt : job_arrival j' + task_period tsk ≤ t := by
          calc job_arrival j' + task_period tsk
              ≤ job_arrival j := by rw [← SAMEtsk]; exact SPO'
            _ ≤ job_arrival j + job_jitter j := Nat.le_add_right _ _
            _ ≤ t := ARRIVED
        have h_arr_lt : job_arrival j' < job_arrival j := by
          unfold SporadicTask.is_valid_sporadic_task SporadicTask.task_period_positive at H_valid_task
          have h_period_pos : task_period tsk > 0 := H_valid_task.2.1
          have hSPO : job_arrival j' + task_period (job_task j') ≤ job_arrival j := SPO'
          rw [SAMEtsk] at hSPO
          exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right h_period_pos) hSPO
        have COMP' := H_all_previous_jobs_of_tsk_completed j' ARRin' SAMEtsk h_arr_lt
        exact NOTCOMP' (completion_monotonic job_cost sched j' H_completed_jobs_dont_execute
          (job_arrival j' + task_period tsk) t LEt COMP')
      · -- j arrives before j'
        push_neg at h
        have h' : job_arrival j ≤ job_arrival j' := Nat.le_of_lt h
        have DIFF'' : j ≠ j' := Ne.symm DIFF
        have SAMEtsk'' : job_task j = job_task j' := by rw [H_job_of_tsk, SAMEtsk]
        have SPO' := H_sporadic_tasks j j' DIFF'' H_j_arrives ARRin' SAMEtsk'' h'
        -- SPO' : job_arrival j' ≥ job_arrival j + task_period (job_task j)
        -- H_t_before_period : t < job_arrival j + task_period tsk
        -- ARRIVED' : job_arrival j' + job_jitter j' ≤ t
        have hle1 : job_arrival j + task_period tsk ≤ job_arrival j' := by
          rw [← H_job_of_tsk]; exact SPO'
        have hle2 : job_arrival j' ≤ t := Nat.le_trans (Nat.le_add_right _ _) ARRIVED'
        exact absurd (Nat.lt_of_lt_of_le H_t_before_period (Nat.le_trans hle1 hle2)) (Nat.lt_irrefl t)

    set_option maxHeartbeats 1600000 in
    include H_ts_nodup in
    theorem platform_fp_cpus_busy_with_interfering_tasks :
        ts.countP (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority tsk t) = num_cpus := by
      have UNIQ := platform_fp_no_multiple_jobs_of_interfering_tasks task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task job_jitter arr_seq sched
        H_jobs_come_from_arrival_sequence H_valid_job_parameters higher_eq_priority
        H_work_conserving H_respects_FP_policy ts H_all_jobs_from_taskset H_sequential_jobs
        H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sporadic_tasks tsk H_valid_task
        j H_j_arrives H_job_of_tsk t H_j_backlogged H_t_before_period
        H_all_previous_jobs_completed_fp H_all_previous_jobs_of_tsk_completed
      have UNIQ' := platform_fp_no_multiple_jobs_of_tsk task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task job_jitter arr_seq sched
        H_jobs_come_from_arrival_sequence H_valid_job_parameters higher_eq_priority
        H_work_conserving H_respects_FP_policy ts H_all_jobs_from_taskset H_sequential_jobs
        H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sporadic_tasks tsk H_valid_task
        j H_j_arrives H_job_of_tsk t H_j_backlogged H_t_before_period
        H_all_previous_jobs_completed_fp H_all_previous_jobs_of_tsk_completed
      have BACK := H_j_backlogged
      -- Derive work_conserving_count inline
      have WC_COUNT : (jobs_scheduled_at sched t).length = num_cpus := by
        have h_all := H_work_conserving j t H_j_arrives BACK
        have h_some : ∀ cpu : Fin num_cpus, ∃ j', sched cpu t = some j' := by
          intro cpu
          obtain ⟨j_other, h_on⟩ := h_all cpu
          unfold scheduled_on at h_on
          exact ⟨j_other, eq_of_beq h_on⟩
        unfold jobs_scheduled_at
        rw [Prosa.Classic.Util.Bigcat.size_bigcat_ord]
        calc ∑ i : Fin num_cpus, (match sched i t with | some j => [j] | none => []).length
            = ∑ _i : Fin num_cpus, 1 := by
              apply Finset.sum_congr rfl
              intro i _
              obtain ⟨j', hj'⟩ := h_some i
              rw [hj']; rfl
          _ = num_cpus := by rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin]
      apply Nat.le_antisymm
      · -- Upper bound: countP ≤ num_cpus
        calc ts.countP (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority tsk t)
            ≤ ts.countP (fun x => task_is_scheduled job_task sched x t) := by
              apply Prosa.Classic.Util.Counting.sub_in_count
              intro x _ h
              unfold scheduled_task_with_higher_eq_priority at h
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              exact h.1
          _ ≤ num_cpus := by
              have h_eq : (fun x => task_is_scheduled job_task sched x t)
                = (fun x => decide (∃ i : Fin num_cpus, task_scheduled_on job_task sched x i t = true)) := by
                ext x; rfl
              rw [h_eq]
              exact Prosa.Classic.Util.Counting.count_exists ts num_cpus
                (fun x cpu => task_scheduled_on job_task sched x cpu t)
                (by exact H_ts_nodup)
                (fun cpu x1 x2 h1 h2 => by
                  unfold task_scheduled_on at h1 h2
                  cases h_sched : sched cpu t with
                  | none => simp [h_sched] at h1
                  | some j0 =>
                    simp [h_sched] at h1 h2
                    rw [← h1, ← h2])
      · -- Lower bound: num_cpus ≤ countP
        suffices h : (jobs_scheduled_at sched t).length ≤ ts.countP (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority tsk t) by omega
        have h_all_pred : ∀ j', j' ∈ jobs_scheduled_at sched t →
            scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority tsk t (job_task j') = true := by
          intro j' h_mem
          have h_sched : scheduled sched j' t := (mem_scheduled_jobs_eq_scheduled sched j' t).mp h_mem
          unfold scheduled_task_with_higher_eq_priority
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          constructor
          · -- task_is_scheduled
            obtain ⟨cpu, h_on⟩ := h_sched
            unfold task_is_scheduled
            simp only [decide_eq_true_eq]
            refine ⟨cpu, ?_⟩
            unfold task_scheduled_on; unfold scheduled_on at h_on
            cases h_eq : sched cpu t with
            | none => simp [h_eq] at h_on
            | some j0 => simp [h_eq] at h_on; simp [h_eq, h_on]
          · -- is_hp_task
            unfold is_hp_task higher_priority_task
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · -- higher_eq_priority (job_task j') (job_task j) = true
              -- From H_respects_FP_policy: j is backlogged, j' is scheduled → priority holds
              have := H_respects_FP_policy j j' t H_j_arrives BACK h_sched
              rw [H_job_of_tsk] at this
              exact this
            · -- job_task j' ≠ tsk
              intro SAMEtsk
              have ARRin' : arrives_in arr_seq j' := H_jobs_come_from_arrival_sequence j' t h_sched
              have PENDING' : pending_jitter job_arrival job_cost job_jitter sched j' t :=
                Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.scheduled_implies_pending
                  job_arrival job_cost job_jitter sched H_jobs_execute_after_jitter H_completed_jobs_dont_execute
                  j' t h_sched
              have EQ := UNIQ' j' ARRin' PENDING' SAMEtsk
              subst EQ
              exact BACK.2 h_sched
        have h_inj_on : ∀ j1 j2, j1 ∈ jobs_scheduled_at sched t →
            j2 ∈ jobs_scheduled_at sched t → job_task j1 = job_task j2 → j1 = j2 := by
          intro j1 j2 h1 h2 h_eq
          have hs1 := (mem_scheduled_jobs_eq_scheduled sched j1 t).mp h1
          have hs2 := (mem_scheduled_jobs_eq_scheduled sched j2 t).mp h2
          -- Both are scheduled, have higher-or-equal priority, and same task
          -- Need to use UNIQ which requires is_hp_task
          have hp1 := h_all_pred j1 h1
          unfold scheduled_task_with_higher_eq_priority at hp1
          simp only [Bool.and_eq_true] at hp1
          have hp1_hp : is_hp_task higher_eq_priority tsk (job_task j1) = true := hp1.2
          exact UNIQ j1 j2
            (H_jobs_come_from_arrival_sequence j1 t hs1)
            (H_jobs_come_from_arrival_sequence j2 t hs2)
            (Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.scheduled_implies_pending
              job_arrival job_cost job_jitter sched H_jobs_execute_after_jitter H_completed_jobs_dont_execute j1 t hs1)
            (Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.scheduled_implies_pending
              job_arrival job_cost job_jitter sched H_jobs_execute_after_jitter H_completed_jobs_dont_execute j2 t hs2)
            h_eq hp1_hp
        have h_map_nodup : (List.map job_task (jobs_scheduled_at sched t)).Nodup :=
          List.Nodup.map_on (fun x hx y hy h_eq => h_inj_on x y hx hy h_eq) (scheduled_jobs_uniq sched H_sequential_jobs t)
        have h_map_sub : ∀ x, x ∈ List.map job_task (jobs_scheduled_at sched t) → x ∈ ts := by
          intro x hx
          obtain ⟨j', hj'_mem, hj'_eq⟩ := List.mem_map.mp hx
          rw [← hj'_eq]
          exact H_all_jobs_from_taskset j'
            (H_jobs_come_from_arrival_sequence j' t
              ((mem_scheduled_jobs_eq_scheduled sched j' t).mp hj'_mem))
        calc (jobs_scheduled_at sched t).length
            = (List.map job_task (jobs_scheduled_at sched t)).length := (List.length_map ..).symm
          _ = (List.map job_task (jobs_scheduled_at sched t)).countP (fun _ => true) := by
              rw [List.countP_true]
          _ ≤ (List.map job_task (jobs_scheduled_at sched t)).countP
              (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority tsk t) := by
              apply Prosa.Classic.Util.Counting.sub_in_count
              intro x hx _
              obtain ⟨j', hj'_mem, hj'_eq⟩ := List.mem_map.mp hx
              rw [← hj'_eq]
              exact h_all_pred j' hj'_mem
          _ ≤ ts.countP (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority tsk t) :=
              Prosa.Classic.Util.Counting.count_sub_uniqr _ _ _ h_map_nodup h_map_sub

  end NoMultipleJobsFP

end Lemmas

end Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
