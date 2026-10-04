import Solutions.Support.Common
import Prosa.Classic.Model.Schedule.Global.Workload

/-!
The busy-window core of the carry-in analyses of Guan et al. (RTSS 2009), proved from the classic
Lean Prosa model of global fixed-priority scheduling: from the start `t0` of an hp-busy window
preceding the arrival of a job `j` of `tsk`, every instant before `j` completes at which `j` does not
run has all processors busy with distinct higher-priority tasks; hence, if `j` is incomplete at
`t0 + t`, the higher-priority workloads in `[t0, t0 + t)`, truncated at `t - e_tsk + 1`, add up to at
least `m (t - e_tsk + 1)`.
-/

set_option linter.unusedVariables false

namespace Solutions.Support.BusyWindow

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Util.Counting
open Solutions.Support.Common
open Prosa.Util.Sum (sumSeq)

universe u v

/-- If a job `j` of `tsk` is backlogged and the earlier jobs of `tsk` are complete, all processors run
jobs of distinct higher-priority tasks. -/
theorem hp_count_of_backlogged {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (ts : taskset_of sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (tsk : sporadic_task) (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (s : time) (hback : backlogged job_arrival job_cost sched j s = true)
    (hprev : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk → job_arrival j0 < job_arrival j →
      completed job_cost sched j0 s = true) :
    ts.val.countP (fun k => task_is_scheduled job_task sched k s &&
      higher_priority_task higher_eq_priority tsk k) = num_cpus := by
  set P := fun k => task_is_scheduled job_task sched k s &&
    higher_priority_task higher_eq_priority tsk k with hP
  have hback' := hback
  simp only [backlogged, Bool.and_eq_true, Bool.not_eq_true'] at hback'
  obtain ⟨hpendj, hnsj⟩ := hback'
  have hncj : completed job_cost sched j s = false := by
    simp only [pending, Bool.and_eq_true, Bool.not_eq_true'] at hpendj; exact hpendj.2
  apply Nat.le_antisymm
  · apply count_task_is_scheduled_le job_task sched ts s
    intro x hx
    simp only [hP, Bool.and_eq_true] at hx
    exact hx.1
  · have hlen := (work_conserving_eq_work_conserving_count job_arrival job_cost arr_seq sched).mp
      H_work_conserving j s H_j_arrives hback
    have hmem : ∀ j', j' ∈ jobs_scheduled_at sched s ↔ scheduled sched j' s = true := by
      intro j'; rw [← mem_scheduled_jobs_eq_scheduled, decide_eq_true_iff]
    rw [← hlen, ← List.length_map (f := job_task)]
    have hnd : ((jobs_scheduled_at sched s).map job_task).Nodup := by
      apply List.Nodup.map_on _ (scheduled_jobs_uniq sched H_sequential_jobs s)
      intro j1 S1 j2 S2 hs
      exact same_task_scheduled_eq task_cost task_period task_deadline job_arrival job_cost job_task
        arr_seq ts sched H_sporadic_tasks H_valid_task_parameters H_all_jobs_from_taskset
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
        H_completed_jobs_dont_execute H_sequential_tasks s j1 j2 ((hmem j1).mp S1)
        ((hmem j2).mp S2) hs
    have hall : ∀ k ∈ (jobs_scheduled_at sched s).map job_task, P k = true ∧ k ∈ ts.val := by
      intro k hk
      obtain ⟨j', S', rfl⟩ := List.mem_map.mp hk
      rw [hmem] at S'
      have A' := H_jobs_come_from_arrival_sequence j' s S'
      have hep' := H_respects_FP_policy j j' s H_j_arrives hback S'
      rw [H_job_of_tsk] at hep'
      obtain ⟨cpu, hcpu⟩ : ∃ cpu, sched cpu s = some j' := by
        simpa [scheduled, scheduled_on, List.any_eq_true] using S'
      have hts : task_is_scheduled job_task sched (job_task j') s = true := by
        simp only [task_is_scheduled, List.any_eq_true, List.mem_finRange, true_and]
        exact ⟨cpu, by simp [task_scheduled_on, hcpu]⟩
      have hne : job_task j' ≠ tsk := by
        intro hsame
        have hpend' := scheduled_implies_pending job_arrival job_cost sched j'
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute s S'
        have hjj : j' ≠ j := by rintro rfl; rw [S'] at hnsj; exact Bool.noConfusion hnsj
        rcases lt_trichotomy (job_arrival j') (job_arrival j) with h | h | h
        · have hc := hprev j' A' hsame h
          simp [pending, hc] at hpend'
        · have hp : 0 < task_period (job_task j') := by
            have := (H_valid_task_parameters _ (H_all_jobs_from_taskset j' A')).2.1
            simpa [task_period_positive] using this
          have := H_sporadic_tasks j' j hjj A' H_j_arrives (hsame.trans H_job_of_tsk.symm) (le_of_eq h)
          tomega
        · have hon : scheduled_on sched j' cpu s = true := by simp [scheduled_on, hcpu]
          have hc := H_sequential_tasks j j' s cpu H_j_arrives A' (H_job_of_tsk.trans hsame.symm) h hon
          rw [hc] at hncj; exact Bool.noConfusion hncj
      exact ⟨by simp [hP, higher_priority_task, hts, hep', hne], H_all_jobs_from_taskset j' A'⟩
    calc ((jobs_scheduled_at sched s).map job_task).length
        = ((jobs_scheduled_at sched s).map job_task).countP P := by
          rw [List.countP_eq_length_filter, List.filter_eq_self.mpr (fun k hk => (hall k hk).1)]
      _ ≤ ts.val.countP P := count_sub_uniqr _ _ _ P hnd (fun k hk => (hall k hk).2)

/-- The busy-window inequality. -/
theorem busy_window_sum_min_ge {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) (ts : taskset_of sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (higher_eq_priority : FP_policy sporadic_task)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (tsk : sporadic_task) (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (hcost : job_cost j ≤ task_cost tsk)
    (t0 : time) (ht0 : t0 ≤ job_arrival j)
    (hbusy : ∀ s, t0 ≤ s → s < job_arrival j →
      ts.val.countP (fun k => task_is_scheduled job_task sched k s &&
        higher_priority_task higher_eq_priority tsk k) = num_cpus)
    (hprev : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk → job_arrival j0 < job_arrival j →
      completed job_cost sched j0 (job_arrival j) = true)
    (t : time) (he : task_cost tsk ≤ t) (hnc : completed job_cost sched j (t0 + t) = false) :
    num_cpus * (t - task_cost tsk + 1) ≤
      sumSeq (ts.val.filter (fun k => higher_priority_task higher_eq_priority tsk k))
        (fun k => min (workload job_task sched k t0 (t0 + t)) (t - task_cost tsk + 1)) := by
  classical
  set H := ts.val.filter (fun k => higher_priority_task higher_eq_priority tsk k) with hH
  have hHnd : H.Nodup := ts.nodup.filter _
  set B := (Finset.Ico t0 (t0 + t)).filter (fun s => scheduled sched j s = false) with hB
  -- at every instant of `B` all processors run distinct higher-priority tasks
  have hall : ∀ s ∈ B, H.countP (fun k => task_is_scheduled job_task sched k s) = num_cpus := by
    intro s hs
    rw [hB, Finset.mem_filter, Finset.mem_Ico] at hs
    rw [hH, List.countP_filter]
    rcases Nat.lt_or_ge s (job_arrival j) with hlt | hge
    · exact hbusy s hs.1.1 hlt
    · have hncs : completed job_cost sched j s = false := by
        cases hc : completed job_cost sched j s
        · rfl
        · have := completion_monotonic job_cost sched j s (t0 + t) (le_of_lt hs.1.2) hc
          rw [this] at hnc; exact Bool.noConfusion hnc
      have hback : backlogged job_arrival job_cost sched j s = true := by
        simp [backlogged, pending, has_arrived, hncs, hs.2]; tomega
      exact hp_count_of_backlogged task_cost task_period task_deadline job_arrival job_cost job_task
        arr_seq ts sched higher_eq_priority H_sporadic_tasks H_valid_task_parameters
        H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
        H_respects_FP_policy H_sequential_tasks tsk j H_j_arrives H_job_of_tsk s hback
        (fun j0 a0 t0' lt => completion_monotonic job_cost sched j0 _ s hge (hprev j0 a0 t0' lt))
  -- the per-task counts of instants of `B`
  let y := fun k => ∑ s ∈ B, (task_is_scheduled job_task sched k s).toNat
  have hysum : sumSeq H y = num_cpus * B.card := by
    unfold sumSeq
    rw [← List.sum_toFinset _ hHnd]
    simp only [y]
    rw [Finset.sum_comm]
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [List.sum_toFinset _ hHnd]
    have := sumSeq_toNat_eq_countP H (fun k => task_is_scheduled job_task sched k s)
    unfold sumSeq at this
    rw [this, hall s hs, Nat.mul_one]
  have hyle : ∀ k ∈ H, y k ≤ B.card := by
    intro k _
    calc y k ≤ ∑ _s ∈ B, 1 := Finset.sum_le_sum (fun s _ => by
            cases task_is_scheduled job_task sched k s <;> simp)
      _ = B.card := by simp
  -- `j` runs at fewer than `e_tsk` instants of the window
  have hBcard : t - task_cost tsk + 1 ≤ B.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.Ico t0 (t0 + t)) (fun s => scheduled sched j s = true)
    have hS : ((Finset.Ico t0 (t0 + t)).filter (fun s => scheduled sched j s = true)).card ≤
        service sched j (t0 + t) := by
      unfold service
      calc ((Finset.Ico t0 (t0 + t)).filter (fun s => scheduled sched j s = true)).card
          = ∑ s ∈ (Finset.Ico t0 (t0 + t)).filter (fun s => scheduled sched j s = true), 1 := by simp
        _ ≤ ∑ s ∈ (Finset.Ico t0 (t0 + t)).filter (fun s => scheduled sched j s = true),
              service_at sched j s := by
            apply Finset.sum_le_sum
            intro s hs
            rw [Finset.mem_filter] at hs
            have h0 := not_scheduled_no_service sched j s
            rw [hs.2] at h0
            have : service_at sched j s ≠ 0 := by simpa using h0.symm
            tomega
        _ ≤ ∑ s ∈ Finset.Ico t0 (t0 + t), service_at sched j s :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Nat.zero_le _)
        _ ≤ ∑ s ∈ Finset.Ico 0 (t0 + t), service_at sched j s :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Ico_subset_Ico (Nat.zero_le _) (le_refl _)) (fun _ _ _ => Nat.zero_le _)
    have hnc' := hnc
    simp only [completed, decide_eq_false_iff_not, Nat.not_le] at hnc'
    have hBeq : B = (Finset.Ico t0 (t0 + t)).filter (fun s => ¬ scheduled sched j s = true) := by
      rw [hB]; congr 1; funext s; simp
    rw [hBeq]
    simp only [Nat.card_Ico] at hsplit
    tomega
  -- combine
  have hmin := sum_min_ge H y num_cpus B.card (t - task_cost tsk + 1) hysum hyle hBcard
  refine le_trans hmin (sumSeq_le_sumSeq H _ _ ?_)
  intro k _
  apply min_le_min_right
  -- an instant at which `k` is scheduled contributes to its workload
  simp only [y]
  unfold workload
  calc ∑ s ∈ B, (task_is_scheduled job_task sched k s).toNat
      ≤ ∑ s ∈ Finset.Ico t0 (t0 + t), (task_is_scheduled job_task sched k s).toNat :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s _
        cases hts : task_is_scheduled job_task sched k s
        · simp
        · simp only [task_is_scheduled, List.any_eq_true, List.mem_finRange, true_and] at hts
          obtain ⟨cpu, hcpu⟩ := hts
          simp only [Bool.toNat_true]
          calc 1 = service_of_task job_task k cpu (sched cpu s) := by
                unfold task_scheduled_on at hcpu
                unfold service_of_task
                cases hs : sched cpu s with
                | none => rw [hs] at hcpu; exact absurd hcpu (by simp)
                | some j' => rw [hs] at hcpu; simp at hcpu; simp [hcpu]
            _ ≤ _ := Finset.single_le_sum (f := fun c => service_of_task job_task k c (sched c s))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ cpu)

end Solutions.Support.BusyWindow
