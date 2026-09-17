-- Translated from: ../rt-proofs/classic/model/schedule/global/basic/constrained_deadlines.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Interference
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform

namespace ConstrainedDeadlines

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
      variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
      variable (H_respects_JLDP_policy :
        respects_JLDP_policy job_arrival job_cost arr_seq sched higher_eq_priority)

      variable (ts : List sporadic_task)
      variable (H_ts_nodup : ts.Nodup)

      variable (H_all_jobs_from_taskset :
        ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

      variable (H_sequential_jobs : sequential_jobs sched)
      variable (H_completed_jobs_dont_execute :
        completed_jobs_dont_execute job_cost sched)
      variable (H_jobs_must_arrive_to_execute :
        jobs_must_arrive_to_execute job_arrival sched)

      variable (H_sporadic_tasks :
        sporadic_task_model task_period job_arrival job_task arr_seq)

      variable (tsk : sporadic_task)
      variable (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)

      variable (j : Job)
      variable (H_j_arrives : arrives_in arr_seq j)
      variable (H_job_of_tsk : job_task j = tsk)

      variable (t : Time)
      variable (H_j_backlogged : backlogged job_arrival job_cost sched j t)

      variable (H_all_previous_jobs_completed :
        ∀ j_other tsk_other,
          arrives_in arr_seq j_other →
          job_task j_other = tsk_other →
          job_arrival j_other + task_period tsk_other ≤ t →
          completed job_cost sched j_other
            (job_arrival j_other + task_period (job_task j_other)))

      def scheduled_task_other_than (tsk tsk_other : sporadic_task) : Bool :=
        decide (∃ cpu : Fin num_cpus, task_scheduled_on job_task sched tsk_other cpu t = true) &&
        decide (tsk_other ≠ tsk)

      include H_ts_nodup H_jobs_come_from_arrival_sequence H_valid_job_parameters H_work_conserving H_respects_JLDP_policy H_all_jobs_from_taskset H_sequential_jobs H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sporadic_tasks H_valid_task H_j_arrives H_job_of_tsk H_j_backlogged H_all_previous_jobs_completed in
      theorem platform_at_most_one_pending_job_of_each_task :
          ∀ j1 j2,
            arrives_in arr_seq j1 →
            arrives_in arr_seq j2 →
            pending job_arrival job_cost sched j1 t →
            pending job_arrival job_cost sched j2 t →
            job_task j1 = job_task j2 →
            j1 = j2 := by
        intro j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk
        by_contra DIFF
        obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
        obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
        rcases le_or_gt (job_arrival j1) (job_arrival j2) with BEFORE1 | BEFORE2
        · have SPO := H_sporadic_tasks j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1
          have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARR1 rfl
            (Nat.le_trans SPO ARRIVED2)
          exact NOTCOMP1 (completion_monotonic job_cost sched j1 H_completed_jobs_dont_execute
            (job_arrival j1 + task_period (job_task j1)) t
            (Nat.le_trans SPO ARRIVED2) COMP1)
        · have BEFORE2' := Nat.le_of_lt BEFORE2
          have DIFF' : j2 ≠ j1 := fun h => DIFF h.symm
          have SAMEtsk' : job_task j2 = job_task j1 := SAMEtsk.symm
          have SPO := H_sporadic_tasks j2 j1 DIFF' ARR2 ARR1 SAMEtsk' BEFORE2'
          have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARR2 rfl
            (Nat.le_trans SPO ARRIVED1)
          exact NOTCOMP2 (completion_monotonic job_cost sched j2 H_completed_jobs_dont_execute
            (job_arrival j2 + task_period (job_task j2)) t
            (Nat.le_trans SPO ARRIVED1) COMP2)

      include H_ts_nodup H_jobs_come_from_arrival_sequence H_valid_job_parameters H_work_conserving H_respects_JLDP_policy H_all_jobs_from_taskset H_sequential_jobs H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sporadic_tasks H_valid_task H_j_arrives H_job_of_tsk H_j_backlogged H_all_previous_jobs_completed in
      theorem platform_cpus_busy_with_interfering_tasks :
          (ts.filter (scheduled_task_other_than job_task sched t tsk)).length = num_cpus := by
        rw [← List.countP_eq_length_filter]
        have UNIQ := platform_at_most_one_pending_job_of_each_task task_cost task_period task_deadline
            job_arrival job_cost job_deadline job_task arr_seq sched
            H_jobs_come_from_arrival_sequence H_valid_job_parameters
            higher_eq_priority H_work_conserving H_respects_JLDP_policy
            ts H_ts_nodup H_all_jobs_from_taskset
            H_sequential_jobs H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
            H_sporadic_tasks tsk H_valid_task
            j H_j_arrives H_job_of_tsk
            t H_j_backlogged H_all_previous_jobs_completed
        have BACK := H_j_backlogged
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
        · calc ts.countP (scheduled_task_other_than job_task sched t tsk)
              ≤ ts.countP (fun x => decide (∃ i : Fin num_cpus, task_scheduled_on job_task sched x i t = true)) := by
                apply Prosa.Classic.Util.Counting.sub_in_count
                intro x _ h
                unfold scheduled_task_other_than at h
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                simp only [decide_eq_true_eq]
                exact h.1
            _ ≤ num_cpus := by
                exact Prosa.Classic.Util.Counting.count_exists ts num_cpus
                  (fun x cpu => task_scheduled_on job_task sched x cpu t)
                  H_ts_nodup
                  (fun cpu x1 x2 h1 h2 => by
                    unfold task_scheduled_on at h1 h2
                    cases h_sched : sched cpu t with
                    | none => simp [h_sched] at h1
                    | some j0 =>
                      simp [h_sched] at h1 h2
                      rw [← h1, ← h2])
        · suffices h : (jobs_scheduled_at sched t).length ≤ ts.countP (scheduled_task_other_than job_task sched t tsk) by omega
          have h_all_pred : ∀ j', j' ∈ jobs_scheduled_at sched t →
              scheduled_task_other_than job_task sched t tsk (job_task j') = true := by
            intro j' h_mem
            have h_sched : scheduled sched j' t := (mem_scheduled_jobs_eq_scheduled sched j' t).mp h_mem
            unfold scheduled_task_other_than
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · obtain ⟨cpu, h_on⟩ := h_sched
              refine ⟨cpu, ?_⟩
              unfold task_scheduled_on; unfold scheduled_on at h_on
              cases h_eq : sched cpu t with
              | none => simp [h_eq] at h_on
              | some j0 => simp [h_eq] at h_on; simp [h_eq, h_on]
            · intro SAMEtsk
              have ARRin' : arrives_in arr_seq j' := H_jobs_come_from_arrival_sequence j' t h_sched
              have PENDING' : pending job_arrival job_cost sched j' t :=
                scheduled_implies_pending job_arrival job_cost sched j'
                  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t h_sched
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
              (scheduled_implies_pending job_arrival job_cost sched j1
                H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hs1)
              (scheduled_implies_pending job_arrival job_cost sched j2
                H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hs2)
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
      variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
      variable (H_respects_FP_policy :
        respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)

      variable (ts : List sporadic_task)
      variable (H_ts_nodup : ts.Nodup)

      variable (H_all_jobs_from_taskset :
        ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

      variable (H_sequential_jobs : sequential_jobs sched)
      variable (H_completed_jobs_dont_execute :
        completed_jobs_dont_execute job_cost sched)
      variable (H_jobs_must_arrive_to_execute :
        jobs_must_arrive_to_execute job_arrival sched)

      variable (H_sporadic_tasks :
        sporadic_task_model task_period job_arrival job_task arr_seq)

      variable (tsk : sporadic_task)
      variable (H_valid_task : is_valid_sporadic_task task_cost task_period task_deadline tsk)

      variable (j : Job)
      variable (H_j_arrives : arrives_in arr_seq j)
      variable (H_job_of_tsk : job_task j = tsk)

      variable (t : Time)
      variable (H_j_backlogged : backlogged job_arrival job_cost sched j t)
      variable (H_t_before_period : t < job_arrival j + task_period tsk)

      variable (H_all_previous_jobs_completed :
        ∀ j_other tsk_other,
          arrives_in arr_seq j_other →
          job_task j_other = tsk_other →
          higher_priority_task higher_eq_priority tsk tsk_other = true →
          completed job_cost sched j_other
            (job_arrival j_other + task_period tsk_other))

      variable (H_all_previous_jobs_of_tsk_completed :
        ∀ j0,
          arrives_in arr_seq j0 →
          job_task j0 = tsk →
          job_arrival j0 < job_arrival j →
          completed job_cost sched j0 (job_arrival j0 + task_period tsk))

      def scheduled_task_with_higher_eq_priority
          (tsk tsk_other : sporadic_task) : Bool :=
        decide (∃ cpu : Fin num_cpus, task_scheduled_on job_task sched tsk_other cpu t = true) &&
        higher_priority_task higher_eq_priority tsk tsk_other

      include H_jobs_come_from_arrival_sequence H_valid_job_parameters H_work_conserving H_respects_FP_policy H_all_jobs_from_taskset H_sequential_jobs H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sporadic_tasks H_valid_task H_j_arrives H_job_of_tsk H_j_backlogged H_t_before_period H_all_previous_jobs_completed H_all_previous_jobs_of_tsk_completed in
      theorem platform_fp_no_multiple_jobs_of_interfering_tasks :
          ∀ j1 j2,
            arrives_in arr_seq j1 →
            arrives_in arr_seq j2 →
            pending job_arrival job_cost sched j1 t →
            pending job_arrival job_cost sched j2 t →
            job_task j1 = job_task j2 →
            higher_priority_task higher_eq_priority tsk (job_task j1) = true →
            j1 = j2 := by
        intro j1 j2 ARR1 ARR2 PENDING1 PENDING2 SAMEtsk INTERF
        by_contra DIFF
        obtain ⟨ARRIVED1, NOTCOMP1⟩ := PENDING1
        obtain ⟨ARRIVED2, NOTCOMP2⟩ := PENDING2
        rcases le_or_gt (job_arrival j1) (job_arrival j2) with BEFORE1 | BEFORE2
        · have SPO := H_sporadic_tasks j1 j2 DIFF ARR1 ARR2 SAMEtsk BEFORE1
          have COMP1 := H_all_previous_jobs_completed j1 (job_task j1) ARR1 rfl INTERF
          exact NOTCOMP1 (completion_monotonic job_cost sched j1 H_completed_jobs_dont_execute
            (job_arrival j1 + task_period (job_task j1)) t
            (Nat.le_trans SPO ARRIVED2) COMP1)
        · have BEFORE2' := Nat.le_of_lt BEFORE2
          have DIFF' : j2 ≠ j1 := fun h => DIFF h.symm
          have SAMEtsk' : job_task j2 = job_task j1 := SAMEtsk.symm
          have SPO := H_sporadic_tasks j2 j1 DIFF' ARR2 ARR1 SAMEtsk' BEFORE2'
          have COMP2 := H_all_previous_jobs_completed j2 (job_task j2) ARR2 rfl (SAMEtsk ▸ INTERF)
          exact NOTCOMP2 (completion_monotonic job_cost sched j2 H_completed_jobs_dont_execute
            (job_arrival j2 + task_period (job_task j2)) t
            (Nat.le_trans SPO ARRIVED1) COMP2)

      include H_jobs_come_from_arrival_sequence H_valid_job_parameters H_work_conserving H_respects_FP_policy H_all_jobs_from_taskset H_sequential_jobs H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sporadic_tasks H_valid_task H_j_arrives H_job_of_tsk H_j_backlogged H_t_before_period H_all_previous_jobs_completed H_all_previous_jobs_of_tsk_completed in
      theorem platform_fp_no_multiple_jobs_of_tsk :
          ∀ j',
            arrives_in arr_seq j' →
            pending job_arrival job_cost sched j' t →
            job_task j' = tsk →
            j' = j := by
        intro j' ARR' PENDING' SAMEtsk
        by_contra DIFF
        obtain ⟨ARRIVED', NOTCOMP'⟩ := PENDING'
        obtain ⟨⟨ARRIVED_j, NOTCOMP_j⟩, NOTSCHED_j⟩ := H_j_backlogged
        have h_arr_j : job_arrival j ≤ t := by
          unfold has_arrived at ARRIVED_j; exact ARRIVED_j
        have h_arr_j' : job_arrival j' ≤ t := by
          unfold has_arrived at ARRIVED'; exact ARRIVED'
        rcases le_or_gt (job_arrival j') (job_arrival j) with BEFORE | BEFORE'
        · -- j' arrived ≤ j
          have DIFF' : j' ≠ j := fun h => DIFF (by exact h)
          have SPO := H_sporadic_tasks j' j DIFF' ARR' H_j_arrives (by rw [SAMEtsk, H_job_of_tsk]) BEFORE
          -- SPO : job_arrival j ≥ job_arrival j' + task_period (job_task j')
          simp only [SAMEtsk] at SPO
          -- Now SPO : job_arrival j' + task_period tsk ≤ job_arrival j
          have h_per : task_period tsk > 0 := H_valid_task.2.1
          have h_lt : job_arrival j' < job_arrival j := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right h_per) SPO
          have COMP' := H_all_previous_jobs_of_tsk_completed j' ARR' SAMEtsk h_lt
          have h_le_t : job_arrival j' + task_period tsk ≤ t := Nat.le_trans SPO h_arr_j
          exact NOTCOMP' (completion_monotonic job_cost sched j' H_completed_jobs_dont_execute
            (job_arrival j' + task_period tsk) t h_le_t COMP')
        · -- j arrived < j'
          have DIFF' : j ≠ j' := fun h => DIFF h.symm
          have SAMEtsk' : job_task j = job_task j' := by rw [H_job_of_tsk, SAMEtsk.symm]
          have SPO := H_sporadic_tasks j j' DIFF' H_j_arrives ARR' SAMEtsk' (Nat.le_of_lt BEFORE')
          simp only [H_job_of_tsk] at SPO
          -- Now SPO : job_arrival j + task_period tsk ≤ job_arrival j'
          -- But t < job_arrival j + task_period tsk, so job_arrival j' > t, contradicting h_arr_j'
          -- h_arr_j' : job_arrival j' ≤ t, SPO : j + per ≤ j', H_t_before_period : t < j + per
          have : job_arrival j' > t := Nat.lt_of_lt_of_le H_t_before_period SPO
          exact absurd h_arr_j' (Nat.not_le.mpr this)

      include H_ts_nodup H_jobs_come_from_arrival_sequence H_valid_job_parameters H_work_conserving H_respects_FP_policy H_all_jobs_from_taskset H_sequential_jobs H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_sporadic_tasks H_valid_task H_j_arrives H_job_of_tsk H_j_backlogged H_t_before_period H_all_previous_jobs_completed H_all_previous_jobs_of_tsk_completed in
      theorem platform_fp_cpus_busy_with_interfering_tasks :
          (ts.filter (scheduled_task_with_higher_eq_priority job_task sched
            higher_eq_priority t tsk)).length = num_cpus := by
        rw [← List.countP_eq_length_filter]
        have UNIQ := platform_fp_no_multiple_jobs_of_interfering_tasks task_cost task_period task_deadline
            job_arrival job_cost job_deadline job_task arr_seq sched
            H_jobs_come_from_arrival_sequence H_valid_job_parameters
            higher_eq_priority H_work_conserving H_respects_FP_policy
            ts H_all_jobs_from_taskset
            H_sequential_jobs H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
            H_sporadic_tasks tsk H_valid_task
            j H_j_arrives H_job_of_tsk
            t H_j_backlogged H_t_before_period
            H_all_previous_jobs_completed H_all_previous_jobs_of_tsk_completed
        have UNIQ' := platform_fp_no_multiple_jobs_of_tsk task_cost task_period task_deadline
            job_arrival job_cost job_deadline job_task arr_seq sched
            H_jobs_come_from_arrival_sequence H_valid_job_parameters
            higher_eq_priority H_work_conserving H_respects_FP_policy
            ts H_all_jobs_from_taskset
            H_sequential_jobs H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
            H_sporadic_tasks tsk H_valid_task
            j H_j_arrives H_job_of_tsk
            t H_j_backlogged H_t_before_period
            H_all_previous_jobs_completed H_all_previous_jobs_of_tsk_completed
        have BACK := H_j_backlogged
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
        · calc ts.countP (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority t tsk)
              ≤ ts.countP (fun x => decide (∃ i : Fin num_cpus, task_scheduled_on job_task sched x i t = true)) := by
                apply Prosa.Classic.Util.Counting.sub_in_count
                intro x _ h
                unfold scheduled_task_with_higher_eq_priority at h
                simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                simp only [decide_eq_true_eq]
                exact h.1
            _ ≤ num_cpus := by
                exact Prosa.Classic.Util.Counting.count_exists ts num_cpus
                  (fun x cpu => task_scheduled_on job_task sched x cpu t)
                  H_ts_nodup
                  (fun cpu x1 x2 h1 h2 => by
                    unfold task_scheduled_on at h1 h2
                    cases h_sched : sched cpu t with
                    | none => simp [h_sched] at h1
                    | some j0 =>
                      simp [h_sched] at h1 h2
                      rw [← h1, ← h2])
        · suffices h : (jobs_scheduled_at sched t).length ≤ ts.countP (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority t tsk) by omega
          have h_all_pred : ∀ j', j' ∈ jobs_scheduled_at sched t →
              scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority t tsk (job_task j') = true := by
            intro j' h_mem
            have h_sched : scheduled sched j' t := (mem_scheduled_jobs_eq_scheduled sched j' t).mp h_mem
            unfold scheduled_task_with_higher_eq_priority
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · obtain ⟨cpu, h_on⟩ := h_sched
              refine ⟨cpu, ?_⟩
              unfold task_scheduled_on; unfold scheduled_on at h_on
              cases h_eq : sched cpu t with
              | none => simp [h_eq] at h_on
              | some j0 => simp [h_eq] at h_on; simp [h_eq, h_on]
            · unfold higher_priority_task
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              constructor
              · have := H_respects_FP_policy j j' t H_j_arrives BACK h_sched
                rw [H_job_of_tsk] at this
                exact this
              · intro SAMEtsk
                have ARRin' : arrives_in arr_seq j' := H_jobs_come_from_arrival_sequence j' t h_sched
                have PENDING' : pending job_arrival job_cost sched j' t :=
                  scheduled_implies_pending job_arrival job_cost sched j'
                    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t h_sched
                have EQ := UNIQ' j' ARRin' PENDING' SAMEtsk
                subst EQ
                exact BACK.2 h_sched
          have h_inj_on : ∀ j1 j2, j1 ∈ jobs_scheduled_at sched t →
              j2 ∈ jobs_scheduled_at sched t → job_task j1 = job_task j2 → j1 = j2 := by
            intro j1 j2 h1 h2 h_eq
            have hs1 := (mem_scheduled_jobs_eq_scheduled sched j1 t).mp h1
            have hs2 := (mem_scheduled_jobs_eq_scheduled sched j2 t).mp h2
            have hp1 := h_all_pred j1 h1
            unfold scheduled_task_with_higher_eq_priority at hp1
            simp only [Bool.and_eq_true] at hp1
            have hp1_hp : higher_priority_task higher_eq_priority tsk (job_task j1) = true := hp1.2
            exact UNIQ j1 j2
              (H_jobs_come_from_arrival_sequence j1 t hs1)
              (H_jobs_come_from_arrival_sequence j2 t hs2)
              (scheduled_implies_pending job_arrival job_cost sched j1
                H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hs1)
              (scheduled_implies_pending job_arrival job_cost sched j2
                H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t hs2)
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
                (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority t tsk) := by
                apply Prosa.Classic.Util.Counting.sub_in_count
                intro x hx _
                obtain ⟨j', hj'_mem, hj'_eq⟩ := List.mem_map.mp hx
                rw [← hj'_eq]
                exact h_all_pred j' hj'_mem
            _ ≤ ts.countP (scheduled_task_with_higher_eq_priority job_task sched higher_eq_priority t tsk) :=
                Prosa.Classic.Util.Counting.count_sub_uniqr _ _ _ h_map_nodup h_map_sub

    end NoMultipleJobsFP

  end Lemmas

end ConstrainedDeadlines

end Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines
