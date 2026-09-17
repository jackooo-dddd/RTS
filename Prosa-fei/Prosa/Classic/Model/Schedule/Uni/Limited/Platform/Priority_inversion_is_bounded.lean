-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/platform/priority_inversion_is_bounded.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Util.Epsilon
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Priority_inversion_is_bounded

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
open Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Priority
open LimitedPreemptionPlatform
open BusyIntervalJLFP
open Prosa.Util.Epsilon

namespace PriorityInversionIsBounded

section PriorityInversionIsBounded

  variable {Task : Type _} [DecidableEq Task]
  variable (task_max_nps task_cost : Task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_max_nps job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
  variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

  variable (higher_eq_priority : JLFP_policy Job)
  variable (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
  variable (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority)

  variable (can_be_preempted : Job → Time → Bool)
  private abbrev preemption_time' := LimitedPreemptionPlatform.preemption_time sched can_be_preempted
  variable (H_correct_preemption_model :
    correct_preemption_model arr_seq sched can_be_preempted)
  variable (H_model_with_bounded_nonpreemptive_segments :
    model_with_bounded_nonpreemptive_segments
      job_cost job_task arr_seq can_be_preempted job_max_nps task_max_nps)

  variable (H_work_conserving : Platform.work_conserving job_arrival job_cost arr_seq sched)

  variable (H_respects_policy :
    respects_JLFP_policy_at_preemption_point job_arrival job_cost arr_seq sched can_be_preempted higher_eq_priority)

  private abbrev job_scheduled_at' := scheduled_at sched
  private abbrev job_completed_by' := completed_by job_cost sched

  def max_length_of_priority_inversion (j : Job) (t : Time) : Nat :=
    ((jobs_arrived_before arr_seq t).filter (fun j_lp => !(higher_eq_priority j_lp j))).map
      (fun j_lp => job_max_nps j_lp - ε) |>.foldl max 0

  section PreemptionTimeAndPriorityInversion

    variable (j : Job)
    variable (H_j_arrives : arrives_in arr_seq j)
    variable (H_job_cost_positive : job_cost j > 0)

    variable (t1 t2 : Time)
    variable (H_busy_interval_prefix :
      busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2)

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy H_j_arrives H_job_cost_positive H_busy_interval_prefix in
    theorem not_quiet_implies_exists_scheduled_hp_job_at_preemption_point :
        ∀ t,
          t1 ≤ t ∧ t < t2 →
          preemption_time' sched can_be_preempted t = true →
          ∃ j_hp,
            arrived_between job_arrival j_hp t1 t2 ∧
            higher_eq_priority j_hp j = true ∧
            scheduled_at sched j_hp t = true := by
      intro t ⟨hGE, hLT⟩ hPREEMPT
      have hBI := H_busy_interval_prefix
      obtain ⟨hT1_LT_T2, hQT, hNQT, hARR_le, hARR_lt⟩ := hBI
      -- Step 1: Processor is not idle at time t
      have hNOTIDLE := not_quiet_implies_not_idle
        job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent
        sched H_jobs_come_from_arrival_sequence higher_eq_priority
        (job_task j) j H_j_arrives rfl H_job_cost_positive
        H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
        H_priority_is_reflexive H_priority_is_transitive
        t1 t2 H_busy_interval_prefix t ⟨hGE, hLT⟩
      -- Step 2: Get the scheduled job j_hp
      cases hOPT : sched t with
      | none => exfalso; apply hNOTIDLE; simp [is_idle, hOPT]
      | some j_hp =>
        clear hNOTIDLE
        have hSCHED : scheduled_at sched j_hp t = true := by
          simp [scheduled_at, hOPT]
        -- Step 3: Show hep j_hp j by contradiction
        suffices hHP : higher_eq_priority j_hp j = true by
          -- Step 4: Show arrived_between j_hp t1 t2
          have hPEND := scheduled_implies_pending job_arrival job_cost sched
            H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute j_hp t hSCHED
          have hARR_hp_le_t : has_arrived job_arrival j_hp t := hPEND.1
          have hARR_hp_lt_t2 : job_arrival j_hp < t2 := by
            simp only [has_arrived, Time] at *; omega
          have hARR_hp_ge_t1 : t1 ≤ job_arrival j_hp := by
            by_contra hLT_t1
            push_neg at hLT_t1
            have hCOMP_t1 := hQT j_hp
              (H_jobs_come_from_arrival_sequence j_hp t hSCHED) hHP hLT_t1
            have hCOMP_t := completion_monotonic job_cost sched j_hp t1 t
              (by simp only [Time] at *; omega) hCOMP_t1
            exact (completed_implies_not_scheduled job_cost sched j_hp
              H_completed_jobs_dont_execute t hCOMP_t) hSCHED
          exact ⟨j_hp, ⟨hARR_hp_ge_t1, hARR_hp_lt_t2⟩, hHP, hSCHED⟩
        -- Prove hep j_hp j by contradiction
        by_contra hNOTHP
        -- Find a pending hep-over-j job at time t to derive a contradiction
        -- Case analysis: is there a ¬quiet_time between t1 and t2 that we can exploit?
        have hPENDING_HP : ∃ j', arrives_in arr_seq j' ∧ higher_eq_priority j' j = true ∧
            has_arrived job_arrival j' t ∧ ¬ completed_by job_cost sched j' t := by
          rcases Nat.lt_or_ge t1 t with hT1_LT_T | hT_LE_T1
          · -- Case: t1 < t, so t ∈ (t1, t2) and ¬quiet_time(t)
            have hNQ := hNQT t ⟨hT1_LT_T, hLT⟩
            -- ¬quiet_time t means ∃ j' with hep, arrived before t, not completed at t
            simp only [quiet_time] at hNQ
            push_neg at hNQ
            obtain ⟨j', hARR_j', hHP_j', hBEF_j', hNC_j'⟩ := hNQ
            exact ⟨j', hARR_j', hHP_j', by
              simp only [has_arrived, arrived_before, Time] at *; omega, hNC_j'⟩
          · -- Case: t ≤ t1, so t = t1 (since t ≥ t1)
            have hEQ : t = t1 := by simp only [Time] at *; omega
            rcases Nat.lt_or_ge (t1 + 1) t2 with hT2_GT | hT2_LE
            · -- Sub-case: t1 + 1 < t2, so ¬quiet_time(t1 + 1)
              have hNQ := hNQT (t1 + 1) ⟨by simp only [Time] at *; omega, hT2_GT⟩
              simp only [quiet_time] at hNQ
              push_neg at hNQ
              obtain ⟨j', hARR_j', hHP_j', hBEF_j', hNC_j'⟩ := hNQ
              have hNC_t : ¬ completed_by job_cost sched j' t := by
                rw [hEQ]; intro hC; exact hNC_j' (completion_monotonic job_cost sched j' t1 (t1 + 1)
                  (by simp only [Time] at *; omega) hC)
              exact ⟨j', hARR_j', hHP_j', by
                simp only [has_arrived, arrived_before, Time] at *; omega, hNC_t⟩
            · -- Sub-case: t2 ≤ t1 + 1, i.e. t2 = t1 + 1 (since t1 < t2)
              have hARR_j_eq : job_arrival j = t1 := by simp only [Time] at *; omega
              have hPEND_j := job_pending_at_arrival job_arrival job_cost sched
                H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute j arr_seq
                H_j_arrives H_job_cost_positive
              rw [hARR_j_eq] at hPEND_j
              exact ⟨j, H_j_arrives, H_priority_is_reflexive j,
                by rw [hEQ]; exact hPEND_j.1,
                by rw [hEQ]; exact hPEND_j.2⟩
        -- Now use the pending job to derive the contradiction
        obtain ⟨j', hARR_j', hHP_j', hHAS_j', hNC_j'⟩ := hPENDING_HP
        -- j' is either scheduled or not at t
        by_cases hSCHED_j' : scheduled_at sched j' t = true
        · -- j' is scheduled at t: j' = j_hp
          have hEQ := only_one_job_scheduled sched j' j_hp t hSCHED_j' hSCHED
          subst hEQ; exact hNOTHP hHP_j'
        · -- j' is not scheduled at t: j' is backlogged
          have hBACK : backlogged job_arrival job_cost sched j' t :=
            ⟨⟨hHAS_j', hNC_j'⟩, hSCHED_j'⟩
          -- By respects_policy: hep j_hp j'
          have hHP_jhp_j' := H_respects_policy j' j_hp t hPREEMPT hARR_j' hBACK hSCHED
          -- By transitivity: hep j_hp j
          exact hNOTHP (H_priority_is_transitive j' j_hp j hHP_jhp_j' hHP_j')

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy H_j_arrives H_job_cost_positive H_busy_interval_prefix in
    theorem scheduling_of_any_segment_starts_with_preemption_time :
        ∀ j' t,
          scheduled_at sched j' t = true →
          ∃ pt,
            job_arrival j' ≤ pt ∧ pt ≤ t ∧
            preemption_time' sched can_be_preempted pt = true ∧
            (∀ t', pt ≤ t' ∧ t' ≤ t → scheduled_at sched j' t' = true) := by
      intro s t
      induction t with
      | zero =>
        intro hSCHED
        refine ⟨0, ?_, Nat.le_refl 0, ?_, ?_⟩
        · exact H_jobs_must_arrive_to_execute s 0 hSCHED
        · -- preemption_time' sched can_be_preempted 0 = true
          simp only [preemption_time', LimitedPreemptionPlatform.preemption_time]
          cases h : sched 0 with
          | none => rfl
          | some j0 =>
            simp only []
            have harr : arrives_in arr_seq j0 :=
              H_jobs_come_from_arrival_sequence j0 0 (by simp [scheduled_at, h])
            have hserv : service sched j0 0 = 0 := by
              simp [service, service_during, Finset.Ico_self]
            rw [hserv]
            exact (H_model_with_bounded_nonpreemptive_segments j0 harr).1
        · intro t' ⟨h1, h2⟩
          have : t' = 0 := Nat.le_antisymm h2 (Nat.zero_le _)
          subst this; exact hSCHED
      | succ n ih =>
        intro hSCHED
        by_cases hPREV : (scheduled_at sched s n = true)
        · -- s also scheduled at n. Use IH.
          obtain ⟨pt, hARR, hLE, hPT, hCONT⟩ := ih hPREV
          exact ⟨pt, hARR, Nat.le_succ_of_le hLE, hPT,
            fun t' ⟨h1, h2⟩ => by
              rcases Nat.lt_or_ge t' (n + 1) with hLT | hGE
              · exact hCONT t' ⟨h1, by simp only [Time] at *; omega⟩
              · have : t' = n + 1 := by simp only [Time] at *; omega
                subst this; exact hSCHED⟩
        · -- s NOT scheduled at n. So n+1 is a preemption time.
          have hARRIVES : arrives_in arr_seq s :=
            H_jobs_come_from_arrival_sequence s (n + 1) hSCHED
          have hPT : preemption_time' sched can_be_preempted (n + 1) = true := by
            simp only [preemption_time']
            exact first_moment_is_pt job_cost job_task arr_seq sched can_be_preempted
              job_max_nps task_max_nps H_correct_preemption_model
              H_model_with_bounded_nonpreemptive_segments
              H_jobs_come_from_arrival_sequence s n hARRIVES hPREV hSCHED
          exact ⟨n + 1, H_jobs_must_arrive_to_execute s (n + 1) hSCHED, Nat.le_refl _,
            hPT, fun t' ⟨h1, h2⟩ => by
              have : t' = n + 1 := by simp only [Time] at *; omega
              subst this; exact hSCHED⟩

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy H_j_arrives H_job_cost_positive H_busy_interval_prefix in
    theorem not_quiet_implies_exists_scheduled_hp_job_after_preemption_point :
        ∀ tp t,
          preemption_time' sched can_be_preempted tp = true →
          t1 ≤ tp ∧ tp < t2 →
          tp ≤ t ∧ t < t2 →
          ∃ j_hp,
            arrived_between job_arrival j_hp t1 (t + 1) ∧
            higher_eq_priority j_hp j = true ∧
            scheduled_at sched j_hp t = true := by
      intro tp t hPR ⟨hGEtp, hLTtp⟩ ⟨hLEtp, hLTt⟩
      have hBI := H_busy_interval_prefix
      obtain ⟨hT1_LT_T2, hQT, hNQT, hARR_le, hARR_lt⟩ := hBI
      -- Step 1: Processor not idle at t
      have hNOTIDLE := not_quiet_implies_not_idle
        job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent
        sched H_jobs_come_from_arrival_sequence higher_eq_priority
        (job_task j) j H_j_arrives rfl H_job_cost_positive
        H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
        H_priority_is_reflexive H_priority_is_transitive
        t1 t2 H_busy_interval_prefix t ⟨by simp only [Time] at *; omega, hLTt⟩
      -- Step 2: Get scheduled job
      cases hOPT : sched t with
      | none => exfalso; apply hNOTIDLE; simp [is_idle, hOPT]
      | some j_hp =>
        clear hNOTIDLE
        have hSCHED : scheduled_at sched j_hp t = true := by simp [scheduled_at, hOPT]
        -- Step 3: Show hep j_hp j
        have hHP : higher_eq_priority j_hp j = true := by
          -- Use scheduling_of_any_segment to find the start of j_hp's segment
          have hSEG := scheduling_of_any_segment_starts_with_preemption_time
            task_max_nps job_arrival job_max_nps job_cost job_task
            arr_seq H_arrival_times_are_consistent
            sched H_jobs_come_from_arrival_sequence
            H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
            can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
            H_work_conserving H_respects_policy
            j H_j_arrives H_job_cost_positive
            t1 t2 H_busy_interval_prefix
            j_hp t hSCHED
          obtain ⟨prt, hARR_prt, hLE_prt, hPT_prt, hCONT⟩ := hSEG
          -- Case: prt ≥ t1 or prt < t1
          rcases Nat.lt_or_ge prt t1 with hPRT_LT | hPRT_GE
          · -- prt < t1: j_hp's segment covers [prt, t], and tp ∈ [prt, t] (since prt < t1 ≤ tp ≤ t)
            -- Use hp_at_preemption_point at tp to get an hp job scheduled at tp
            have hHP_exists := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
              task_max_nps job_arrival job_max_nps job_cost job_task
              arr_seq H_arrival_times_are_consistent
              sched H_jobs_come_from_arrival_sequence
              H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
              higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
              can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
              H_work_conserving H_respects_policy
              j H_j_arrives H_job_cost_positive
              t1 t2 H_busy_interval_prefix
              tp ⟨hGEtp, hLTtp⟩ hPR
            obtain ⟨jhp2, _, hHP2, hSCHED2⟩ := hHP_exists
            -- j_hp is scheduled at tp (from continuous segment: prt ≤ tp ≤ t)
            have hSCHED_hp_tp : scheduled_at sched j_hp tp = true :=
              hCONT tp ⟨by simp only [Time] at *; omega, hLEtp⟩
            -- j_hp = jhp2
            have hEQ := only_one_job_scheduled sched j_hp jhp2 tp hSCHED_hp_tp hSCHED2
            rw [hEQ]; exact hHP2
          · -- prt ≥ t1: use hp_at_preemption_point at prt
            have hHP_exists := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
              task_max_nps job_arrival job_max_nps job_cost job_task
              arr_seq H_arrival_times_are_consistent
              sched H_jobs_come_from_arrival_sequence
              H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
              higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
              can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
              H_work_conserving H_respects_policy
              j H_j_arrives H_job_cost_positive
              t1 t2 H_busy_interval_prefix
              prt ⟨hPRT_GE, by simp only [Time] at *; omega⟩ hPT_prt
            obtain ⟨jhp2, _, hHP2, hSCHED2⟩ := hHP_exists
            -- j_hp is scheduled at prt (from continuous segment)
            have hSCHED_hp_prt : scheduled_at sched j_hp prt = true :=
              hCONT prt ⟨le_refl prt, hLE_prt⟩
            have hEQ := only_one_job_scheduled sched j_hp jhp2 prt hSCHED_hp_prt hSCHED2
            rw [hEQ]; exact hHP2
        -- Step 4: Show arrived_between j_hp t1 (t+1)
        have hPEND := scheduled_implies_pending job_arrival job_cost sched
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute j_hp t hSCHED
        refine ⟨j_hp, ⟨?_, ?_⟩, hHP, hSCHED⟩
        · -- t1 ≤ arrival j_hp
          by_contra hLT_t1
          push_neg at hLT_t1
          have hCOMP := hQT j_hp (H_jobs_come_from_arrival_sequence j_hp t hSCHED) hHP hLT_t1
          have hCOMP_t := completion_monotonic job_cost sched j_hp t1 t
            (by simp only [Time] at *; omega) hCOMP
          exact (completed_implies_not_scheduled job_cost sched j_hp
            H_completed_jobs_dont_execute t hCOMP_t) hSCHED
        · -- arrival j_hp < t + 1
          have := hPEND.1; simp only [has_arrived] at this; simp only [Time] at *; omega

    variable (K : Time)
    variable (H_preemption_time_exists :
      ∃ pr_t, preemption_time' sched can_be_preempted pr_t = true ∧ t1 ≤ pr_t ∧ pr_t ≤ t1 + K)

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy H_j_arrives H_job_cost_positive H_busy_interval_prefix H_preemption_time_exists in
    theorem not_quiet_implies_exists_scheduled_hp_job :
        ∀ t,
          t1 + K ≤ t ∧ t < t2 →
          ∃ j_hp,
            arrived_between job_arrival j_hp t1 (t + 1) ∧
            higher_eq_priority j_hp j = true ∧
            scheduled_at sched j_hp t = true := by
      intro t ⟨hGE, hLT⟩
      obtain ⟨prt, hPR, hGEprt, hLEprt⟩ := H_preemption_time_exists
      have h1 : t1 ≤ prt ∧ prt < t2 := by constructor <;> (simp only [Time] at *; omega)
      have h2 : prt ≤ t ∧ t < t2 := by constructor <;> (simp only [Time] at *; omega)
      exact not_quiet_implies_exists_scheduled_hp_job_after_preemption_point
        task_max_nps job_arrival job_max_nps job_cost job_task
        arr_seq H_arrival_times_are_consistent
        sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
        can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
        H_work_conserving H_respects_policy
        j H_j_arrives H_job_cost_positive
        t1 t2 H_busy_interval_prefix
        prt t hPR h1 h2

  end PreemptionTimeAndPriorityInversion

  section PreemprionTimeExists

    variable (j : Job)
    variable (H_j_arrives : arrives_in arr_seq j)
    variable (H_job_cost_positive : job_cost j > 0)

    variable (t1 t2 : Time)
    variable (H_busy_interval_prefix :
      busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2)

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy H_j_arrives H_job_cost_positive H_busy_interval_prefix in
    theorem hp_job_not_scheduled_before_quiet_time :
        ∀ jhp t,
          quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (t + 1) →
          scheduled_at sched jhp (t + 1) = true →
          higher_eq_priority jhp j = true →
          ¬ (scheduled_at sched jhp t = true) := by
      intro jhp t hQUIET hSCHED_t1 hHP hSCHED_t
      -- jhp is scheduled at t+1, so it arrives at or before t+1
      have hARR_le : has_arrived job_arrival jhp (t + 1) :=
        H_jobs_must_arrive_to_execute jhp (t + 1) hSCHED_t1
      -- Case split: arrives before or at t+1
      rcases Nat.lt_or_ge (job_arrival jhp) (t + 1) with hLT | hGE
      · -- Case 1: job_arrival jhp < t + 1 (arrived by time t)
        -- By quiet time, jhp is completed by t+1
        have hARR_in := H_jobs_come_from_arrival_sequence jhp (t + 1) hSCHED_t1
        have hCOMPL := hQUIET jhp hARR_in hHP hLT
        -- But jhp is scheduled at t+1, contradicting completed_jobs_dont_execute
        exact absurd hSCHED_t1 (completed_implies_not_scheduled job_cost sched jhp
          H_completed_jobs_dont_execute (t + 1) hCOMPL)
      · -- Case 2: job_arrival jhp ≥ t + 1 (arrives at t+1 or later)
        -- jhp hasn't arrived at time t, so can't be scheduled at t
        have hNOT_ARR : ¬ has_arrived job_arrival jhp t := by
          simp only [has_arrived, Time] at *; omega
        exact absurd hSCHED_t (fun h => hNOT_ARR (H_jobs_must_arrive_to_execute jhp t h))

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy H_j_arrives H_job_cost_positive H_busy_interval_prefix in
    theorem low_priority_job_arrives_before_busy_interval_prefix :
        ∀ jlp t,
          t1 ≤ t ∧ t < t2 →
          scheduled_at sched jlp t = true →
          ¬ (higher_eq_priority jlp j = true) →
          job_arrival jlp < t1 := by
      intro jlp t ⟨hGE, hLT⟩ hSCHED hNHP
      -- By contradiction: assume jlp arrives at or after t1
      by_contra hARR_GE
      push_neg at hARR_GE
      -- Use scheduling_of_any_segment_starts_with_preemption_time to find the start of jlp's segment
      have hSEG := scheduling_of_any_segment_starts_with_preemption_time
        task_max_nps job_arrival job_max_nps job_cost job_task
        arr_seq H_arrival_times_are_consistent
        sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
        can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
        H_work_conserving H_respects_policy
        j H_j_arrives H_job_cost_positive
        t1 t2 H_busy_interval_prefix
        jlp t hSCHED
      obtain ⟨pt, hARR_pt, hLE_pt, hPT, hCONT⟩ := hSEG
      -- pt ≥ t1 (since pt ≥ arrival jlp ≥ t1)
      have hPT_ge_t1 : t1 ≤ pt := by simp only [Time] at *; omega
      -- pt < t2 (since pt ≤ t < t2)
      have hPT_lt_t2 : pt < t2 := by simp only [Time] at *; omega
      -- Use not_quiet_implies_exists_scheduled_hp_job_at_preemption_point at pt
      have hHP_exists := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
        task_max_nps job_arrival job_max_nps job_cost job_task
        arr_seq H_arrival_times_are_consistent
        sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
        can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
        H_work_conserving H_respects_policy
        j H_j_arrives H_job_cost_positive
        t1 t2 H_busy_interval_prefix
        pt ⟨hPT_ge_t1, hPT_lt_t2⟩ hPT
      obtain ⟨jhp, _, hHP_jhp, hSCHED_jhp⟩ := hHP_exists
      -- jlp is also scheduled at pt (from continuous segment)
      have hSCHED_jlp_pt : scheduled_at sched jlp pt = true :=
        hCONT pt ⟨le_refl pt, hLE_pt⟩
      -- So jlp = jhp
      have hEQ := only_one_job_scheduled sched jlp jhp pt hSCHED_jlp_pt hSCHED_jhp
      -- But jhp has hep over j while jlp doesn't
      subst hEQ
      exact hNHP hHP_jhp

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments H_work_conserving H_respects_policy H_j_arrives H_job_cost_positive H_busy_interval_prefix in
    theorem preemption_time_exists :
        ∃ pr_t,
          preemption_time' sched can_be_preempted pr_t = true ∧
          t1 ≤ pr_t ∧ pr_t ≤ t1 + max_length_of_priority_inversion job_max_nps arr_seq higher_eq_priority j t1 := by
      have hBI := H_busy_interval_prefix
      obtain ⟨hT1_LT_T2, hQT, hNQT, hARR_le, hARR_lt⟩ := hBI
      -- Case split on sched t1
      cases hOPT : sched t1 with
      | none =>
        -- Processor idle at t1 → t1 is a preemption time
        exact ⟨t1, by simp [preemption_time', LimitedPreemptionPlatform.preemption_time, hOPT],
          le_refl _, Nat.le_add_right _ _⟩
      | some s =>
        have hSCHED_s : scheduled_at sched s t1 = true := by simp [scheduled_at, hOPT]
        by_cases hHP : higher_eq_priority s j = true
        · -- s has hep over j → t1 is a preemption time
          refine ⟨t1, ?_, le_refl _, Nat.le_add_right _ _⟩
          -- Show preemption_time' t1 = true
          by_cases ht1_zero : t1 = 0
          · -- t1 = 0: use zero_is_pt
            rw [ht1_zero]
            exact zero_is_pt job_cost job_task arr_seq sched can_be_preempted
              job_max_nps task_max_nps H_correct_preemption_model
              H_model_with_bounded_nonpreemptive_segments H_jobs_come_from_arrival_sequence
          · -- t1 > 0: t1 = k + 1 for some k. Use hp_job_not_scheduled_before_quiet_time.
            have ⟨k, hk⟩ : ∃ k, t1 = k + 1 := ⟨t1 - 1, (Nat.succ_pred_eq_of_ne_zero ht1_zero).symm⟩
            have hNSCHED : ¬ (scheduled_at sched s k = true) := by
              rw [hk] at hQT hSCHED_s
              exact hp_job_not_scheduled_before_quiet_time
                task_max_nps job_arrival job_max_nps job_cost job_task
                arr_seq H_arrival_times_are_consistent
                sched H_jobs_come_from_arrival_sequence
                H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
                higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
                can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
                H_work_conserving H_respects_policy
                j H_j_arrives H_job_cost_positive
                t1 t2 H_busy_interval_prefix
                s k hQT hSCHED_s hHP
            have hARR_s := H_jobs_come_from_arrival_sequence s t1 hSCHED_s
            rw [hk]
            exact first_moment_is_pt job_cost job_task arr_seq sched can_be_preempted
              job_max_nps task_max_nps H_correct_preemption_model
              H_model_with_bounded_nonpreemptive_segments
              H_jobs_come_from_arrival_sequence s k hARR_s hNSCHED (by rw [hk] at hSCHED_s; exact hSCHED_s)
        · -- s has ¬hep over j → find preemption time within bounded NPS
          have hARR_s := H_jobs_come_from_arrival_sequence s t1 hSCHED_s
          obtain ⟨_, _, _, hBOUND⟩ := H_model_with_bounded_nonpreemptive_segments s hARR_s
          -- Get preemption point from bounded NPS
          obtain ⟨pp, hPP_ge, hPP_le, hCAN_pp⟩ :=
            hBOUND (service sched s t1) ⟨Nat.zero_le _, H_completed_jobs_dont_execute s t1⟩
          -- Minimum δ with can_be_preempted s (service sched s t1 + δ) = true
          have hEX : ∃ δ, can_be_preempted s (service sched s t1 + δ) = true :=
            ⟨pp - service sched s t1, by rwa [Nat.add_sub_cancel' hPP_ge]⟩
          set Δ := Nat.find hEX with hΔ_def
          have hΔ_can : can_be_preempted s (service sched s t1 + Δ) = true := Nat.find_spec hEX
          have hΔ_min : ∀ δ, δ < Δ → can_be_preempted s (service sched s t1 + δ) ≠ true :=
            fun δ hlt => Nat.find_min hEX hlt
          have hΔ_bound : Δ ≤ job_max_nps s - ε := by
            by_contra hContra; push_neg at hContra
            have hle_pp : pp - service sched s t1 ≤ job_max_nps s - ε :=
              Nat.sub_le_sub_right hPP_le (service sched s t1) |>.trans
                (by rw [Nat.add_sub_cancel_left])
            exact Nat.find_min hEX (lt_of_le_of_lt hle_pp hContra)
              (by rwa [Nat.add_sub_cancel' hPP_ge])
          -- Service accumulation: for δ ≤ Δ, service increases by exactly δ
          have hSERV : ∀ δ, δ ≤ Δ → service sched s (t1 + δ) = service sched s t1 + δ := by
            intro δ hδ
            induction δ with
            | zero => simp
            | succ n ih =>
              have ih_n := ih (by omega)
              have hn_lt : n < Δ := by omega
              have hNP : can_be_preempted s (service sched s (t1 + n)) = false := by
                rw [ih_n]
                have hne := hΔ_min n hn_lt
                cases h : can_be_preempted s (service sched s t1 + n) with
                | false => rfl
                | true => exact absurd h hne
              have hS := (H_correct_preemption_model s hARR_s).1 (t1 + n) hNP
              have hSA : service_at sched s (t1 + n) = 1 := by
                simp [service_at, hS]
              simp only [service, service_during]
              rw [show t1 + (n + 1) = (t1 + n) + 1 from by ring,
                  Finset.sum_Ico_succ_top (Nat.zero_le (t1 + n))]
              have hIH : ∑ i ∈ Finset.Ico 0 (t1 + n), service_at sched s i =
                ∑ i ∈ Finset.Ico 0 t1, service_at sched s i + n := by
                have := ih_n; simp only [service, service_during] at this; exact this
              rw [hIH, hSA]; ring
          -- s is scheduled at each time in [t1, t1 + Δ)
          have hSCHED_all : ∀ δ, δ < Δ → scheduled_at sched s (t1 + δ) = true := by
            intro δ hδ
            have hNP : can_be_preempted s (service sched s (t1 + δ)) = false := by
              rw [hSERV δ (le_of_lt hδ)]
              have hne := hΔ_min δ hδ
              cases h : can_be_preempted s (service sched s t1 + δ) with
              | false => rfl
              | true => exact absurd h hne
            exact (H_correct_preemption_model s hARR_s).1 (t1 + δ) hNP
          -- Witness: t1 + Δ
          refine ⟨t1 + Δ, ?_, Nat.le_add_right t1 Δ, ?_⟩
          · -- preemption_time' (t1 + Δ) = true
            simp only [preemption_time', LimitedPreemptionPlatform.preemption_time]
            cases hSPT : sched (t1 + Δ) with
            | none => rfl
            | some s0 =>
              show can_be_preempted s0 (service sched s0 (t1 + Δ)) = true
              by_cases hEQ : s0 = s
              · rw [hEQ, hSERV Δ le_rfl]
                exact hΔ_can
              · -- s0 ≠ s, Δ must be > 0
                have hΔ_pos : 0 < Δ := by
                  by_contra h; push_neg at h; interval_cases Δ
                  simp at hSPT; rw [hOPT] at hSPT
                  exact hEQ (Option.some_injective _ hSPT).symm
                have hS_prev := hSCHED_all (Δ - 1) (by omega)
                have hNS_s0 : ¬ (scheduled_at sched s0 (t1 + (Δ - 1)) = true) := by
                  intro h
                  have := only_one_job_scheduled sched s s0 (t1 + (Δ - 1)) hS_prev h
                  exact hEQ this.symm
                have hS_s0 : scheduled_at sched s0 (t1 + Δ) = true := by simp [scheduled_at, hSPT]
                have hARR_s0 := H_jobs_come_from_arrival_sequence s0 (t1 + Δ) hS_s0
                have h_succ_pred : Δ - 1 + 1 = Δ := Nat.succ_pred_eq_of_pos hΔ_pos
                have hS_s0_shifted : scheduled_at sched s0 ((t1 + (Δ - 1)) + 1) = true := by
                  rw [Nat.add_assoc, h_succ_pred]; exact hS_s0
                have hResult := (H_correct_preemption_model s0 hARR_s0).2
                  (t1 + (Δ - 1)) hNS_s0 hS_s0_shifted
                rw [show t1 + Δ = (t1 + (Δ - 1)) + 1 from by rw [Nat.add_assoc, h_succ_pred]]
                exact hResult
          · -- t1 + Δ ≤ t1 + max_length_of_priority_inversion j t1
            apply Nat.add_le_add_left
            apply le_trans hΔ_bound
            -- job_max_nps s - ε ≤ max_length_of_priority_inversion j t1
            have hLP_arr : job_arrival s < t1 :=
              low_priority_job_arrives_before_busy_interval_prefix
                task_max_nps job_arrival job_max_nps job_cost job_task
                arr_seq H_arrival_times_are_consistent
                sched H_jobs_come_from_arrival_sequence
                H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
                higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
                can_be_preempted H_correct_preemption_model H_model_with_bounded_nonpreemptive_segments
                H_work_conserving H_respects_policy
                j H_j_arrives H_job_cost_positive
                t1 t2 H_busy_interval_prefix
                s t1 ⟨le_refl _, hT1_LT_T2⟩ hSCHED_s (by exact hHP)
            have hIN := arrived_between_implies_in_arrivals job_arrival arr_seq
              H_arrival_times_are_consistent s 0 t1 hARR_s ⟨Nat.zero_le _, hLP_arr⟩
            -- job_max_nps s - ε is in the foldl max list
            have hFILT : s ∈ (jobs_arrived_before arr_seq t1).filter
                (fun j_lp => !(higher_eq_priority j_lp j)) := by
              apply List.mem_filter.mpr
              refine ⟨hIN, ?_⟩
              have : higher_eq_priority s j = false := by
                cases h : higher_eq_priority s j with
                | false => rfl
                | true => exact absurd h hHP
              simp [this]
            have hMAP : (job_max_nps s - ε) ∈
                ((jobs_arrived_before arr_seq t1).filter
                  (fun j_lp => !(higher_eq_priority j_lp j))).map
                  (fun j_lp => job_max_nps j_lp - ε) :=
              List.mem_map_of_mem hFILT
            -- member of list ≤ foldl max 0 of list
            have h_mem_le : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldl max 0 := by
              intro l
              induction l with
              | nil => intro a ha; simp at ha
              | cons y ys ih =>
                intro a ha
                simp only [List.foldl_cons]
                rcases List.mem_cons.mp ha with rfl | h
                · have h_le_foldl : ∀ (acc : ℕ) (l : List ℕ), acc ≤ l.foldl max acc := by
                    intro acc l
                    induction l generalizing acc with
                    | nil => exact le_refl acc
                    | cons z zs ihz =>
                      simp only [List.foldl_cons]
                      exact le_trans (le_max_left acc z) (ihz _)
                  exact le_trans (le_max_right 0 a) (h_le_foldl _ ys)
                · have h_mono : ∀ (acc1 acc2 : ℕ) (l : List ℕ),
                      acc1 ≤ acc2 → l.foldl max acc1 ≤ l.foldl max acc2 := by
                    intro acc1 acc2 l
                    induction l generalizing acc1 acc2 with
                    | nil => exact id
                    | cons z zs ihz =>
                      intro hle; simp only [List.foldl_cons]
                      apply ihz; exact max_le_max_right z hle
                  exact le_trans (ih a h) (h_mono 0 (max 0 y) ys (Nat.zero_le _))
            simp only [max_length_of_priority_inversion]
            exact h_mem_le _ _ hMAP

  end PreemprionTimeExists

end PriorityInversionIsBounded

end PriorityInversionIsBounded

end Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Priority_inversion_is_bounded
