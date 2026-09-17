-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/busy_interval.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Job
open LimitedPreemptionPlatform

namespace BusyIntervalJLFP

section Definitions

  variable {Task : Type _} [DecidableEq Task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq)

  variable (higher_eq_priority : JLFP_policy Job)

  private abbrev job_pending_at := pending job_arrival job_cost sched
  private abbrev job_scheduled_at := scheduled_at sched
  private abbrev job_completed_by := completed_by job_cost sched
  private abbrev job_remaining_cost := remaining_cost job_cost sched
  private abbrev arrivals_between := jobs_arrived_between arr_seq

  section BusyInterval

    variable (tsk : Task)

    variable (j : Job)
    variable (H_from_arrival_sequence : arrives_in arr_seq j)
    variable (H_job_task : job_task j = tsk)

    def quiet_time (t : Time) :=
      ∀ j_hp,
        arrives_in arr_seq j_hp →
        higher_eq_priority j_hp j = true →
        arrived_before job_arrival j_hp t →
        completed_by job_cost sched j_hp t

    def busy_interval_prefix (t1 t_busy : Time) :=
      t1 < t_busy ∧
      quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1 ∧
      (∀ t, t1 < t ∧ t < t_busy → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) ∧
      t1 ≤ job_arrival j ∧ job_arrival j < t_busy

    def busy_interval (t1 t2 : Time) :=
      busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 ∧
      quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2

  end BusyInterval

  section JobPriorityInversionBound

    variable (tsk : Task)

    variable (j : Job)
    variable (H_from_arrival_sequence : arrives_in arr_seq j)
    variable (H_job_task : job_task j = tsk)

    def is_priority_inversion (t : Time) : Nat :=
      match sched t with
      | some jlp => if higher_eq_priority jlp j = true then 0 else 1
      | none => 0

    def cumulative_priority_inversion (t1 t2 : Time) : Nat :=
      ∑ t ∈ Finset.Ico t1 t2, is_priority_inversion sched higher_eq_priority j t

    def priority_inversion_of_job_is_bounded_by (B : Time) :=
      ∀ (t1 t2 : Time),
        busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 →
        cumulative_priority_inversion sched higher_eq_priority j t1 t2 ≤ B

  end JobPriorityInversionBound

  section TaskPriorityInversionBound

    variable (tsk : Task)

    def priority_inversion_is_bounded_by (B : Time) :=
      ∀ (j : Job),
        arrives_in arr_seq j →
        job_task j = tsk →
        job_cost j > 0 →
        priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j B

  end TaskPriorityInversionBound

  section DecidableQuietTime

    def quiet_time_dec (j : Job) (t : Time) : Bool :=
      (jobs_arrived_before arr_seq t).all
        (fun j_hp => !(higher_eq_priority j_hp j) || decide (job_cost j_hp ≤ service sched j_hp t))

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence in
    theorem quiet_time_P :
        ∀ j t, quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true ↔
          quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t := by
      intro j t
      constructor
      · -- quiet_time_dec = true → quiet_time
        intro hDEC s hARR hHP hBEF
        simp only [quiet_time_dec, List.all_eq_true] at hDEC
        have hIN : s ∈ jobs_arrived_before arr_seq t :=
          arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent s 0 t
            hARR ⟨Nat.zero_le _, hBEF⟩
        have hQ := hDEC s hIN
        simp [hHP, completed_by] at hQ
        exact hQ
      · -- quiet_time → quiet_time_dec = true
        intro hQT
        simp only [quiet_time_dec, List.all_eq_true]
        intro s hIN
        have hARR := in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent s 0 t hIN
        have hBEF := in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent s t hIN
        by_cases hHP : higher_eq_priority s j = true
        · simp [hHP]
          exact hQT s hARR hHP hBEF
        · simp [Bool.not_eq_true'] at hHP
          simp [hHP]

  end DecidableQuietTime

  section Lemmas

    variable (tsk : Task)

    variable (j : Job)
    variable (H_from_arrival_sequence : arrives_in arr_seq j)
    variable (H_job_task : job_task j = tsk)
    variable (H_job_cost_positive : job_cost j > 0)

    section BasicLemma

      variable (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)

      variable (t1 t2 : Time)
      variable (H_busy_interval : busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2)

      include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_priority_is_reflexive H_busy_interval in
      theorem job_completes_within_busy_interval :
          completed_by job_cost sched j t2 := by
        obtain ⟨⟨_, _, _, hARR⟩, hQUIET⟩ := H_busy_interval
        exact hQUIET j H_from_arrival_sequence (H_priority_is_reflexive j) hARR.2

    end BasicLemma

    section ExistsPendingJob

      variable (H_completed_jobs_dont_execute :
        completed_jobs_dont_execute job_cost sched)

      variable (t1 t2 : Time)
      variable (H_interval : t1 ≤ t2)
      variable (H_quiet : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1)
      variable (H_not_quiet : ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2)

      include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_completed_jobs_dont_execute H_interval H_quiet H_not_quiet in
      theorem not_quiet_implies_exists_pending_job :
          ∃ j_hp,
            arrives_in arr_seq j_hp ∧
            arrived_between job_arrival j_hp t1 t2 ∧
            higher_eq_priority j_hp j = true ∧
            ¬ completed_by job_cost sched j_hp t2 := by
        -- Case split on whether there exists a job in arrivals_between t1 t2
        -- that is not completed at t2 and has higher_eq_priority
        by_cases hHAS : ∃ j_hp ∈ jobs_arrived_between arr_seq t1 t2,
            ¬ completed_by job_cost sched j_hp t2 ∧ higher_eq_priority j_hp j = true
        · -- Positive case: there exists such a job
          obtain ⟨j_hp, hMEM, hNCOMP, hHP⟩ := hHAS
          have hARR := in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j_hp t1 t2 hMEM
          have hBET := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j_hp t1 t2 hMEM
          exact ⟨j_hp, hARR, hBET, hHP, hNCOMP⟩
        · -- Negative case: all such jobs are completed → t2 is quiet → contradiction
          push_neg at hHAS
          -- hHAS : ∀ j_hp ∈ arrivals_between t1 t2, ¬completed_by → ¬(higher_eq_priority ...)
          exfalso; apply H_not_quiet
          intro j_hp hIN hHP hBEF
          by_cases hBEFORE : job_arrival j_hp < t1
          · exact completion_monotonic job_cost sched j_hp t1 t2 H_interval
              (H_quiet j_hp hIN hHP hBEFORE)
          · push_neg at hBEFORE
            have hBET : arrived_between job_arrival j_hp t1 t2 := ⟨hBEFORE, hBEF⟩
            have hMEM := arrived_between_implies_in_arrivals job_arrival arr_seq
              H_arrival_times_are_consistent j_hp t1 t2 hIN hBET
            -- From hHAS: ¬completed_by → ¬higher_eq_priority, contraposition: higher_eq_priority → completed_by
            by_contra hNCOMP
            exact absurd hHP (hHAS j_hp hMEM hNCOMP)

    end ExistsPendingJob

    section ProcessorAlwaysBusy

      variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
      variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
      variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)

      variable (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
      variable (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority)

      variable (t1 t2 : Time)
      variable (H_busy_interval_prefix :
        busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2)

      include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive H_priority_is_transitive H_busy_interval_prefix in
      theorem idle_time_implies_quiet_time_at_the_next_time_instant :
          ∀ t,
            is_idle sched t = true →
            quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (t + 1) := by
        intro t hIDLE jhp hARR hHP hAB
        -- hAB : arrived_before job_arrival jhp (t + 1), i.e., job_arrival jhp < t + 1
        -- So job_arrival jhp ≤ t, i.e., has_arrived job_arrival jhp t
        by_contra hNCOMP
        -- jhp is not completed at t+1. We want to show it's not completed at t either,
        -- so jhp is pending at t, and since idle, jhp is backlogged → contradiction with work_conserving
        have hARRIVED : has_arrived job_arrival jhp t := by
          simp only [arrived_before] at hAB; simp only [has_arrived]; simp only [Time] at *; omega
        -- jhp is not completed at t+1
        -- If jhp were completed at t, then by completion_monotonic it would be completed at t+1
        have hNCOMP_t : ¬ completed_by job_cost sched jhp t := by
          intro hCOMP
          exact hNCOMP (completion_monotonic job_cost sched jhp t (t + 1) (by simp only [Time] at *; omega) hCOMP)
        -- jhp is pending at t
        have hPEND : pending job_arrival job_cost sched jhp t := ⟨hARRIVED, hNCOMP_t⟩
        -- jhp is not scheduled at t (because idle)
        have hNSCHED : ¬ (scheduled_at sched jhp t = true) := by
          simp only [is_idle, beq_iff_eq] at hIDLE
          simp only [scheduled_at, beq_iff_eq]
          rw [hIDLE]; simp
        -- jhp is backlogged at t
        have hBACK : backlogged job_arrival job_cost sched jhp t := ⟨hPEND, hNSCHED⟩
        -- By work_conserving, there exists a scheduled job
        have hWC := H_work_conserving jhp t hARR hBACK
        obtain ⟨jo, hSCHED⟩ := hWC
        -- But the processor is idle at t
        simp only [is_idle, beq_iff_eq] at hIDLE
        simp only [scheduled_at, beq_iff_eq] at hSCHED
        rw [hIDLE] at hSCHED; simp at hSCHED

      include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive H_priority_is_transitive H_busy_interval_prefix in
      theorem pending_hp_job_exists :
          ∀ t,
            t1 ≤ t ∧ t < t2 →
            ∃ jhp,
              arrives_in arr_seq jhp ∧
              pending job_arrival job_cost sched jhp t ∧
              higher_eq_priority jhp j = true := by
        intro t ⟨hGE, hLT⟩
        obtain ⟨hLT1, hQT, hNQT, hARRle, hARRlt⟩ := H_busy_interval_prefix
        by_cases hGT : t1 + 1 < t2
        · -- Case 1: t1 + 1 < t2
          by_cases hEQ : t1 = t
          · -- t = t1: t1+1 is not quiet
            have hNQ : ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (t1 + 1) :=
              hNQT (t1 + 1) ⟨by simp only [Time] at *; omega, hGT⟩
            have hLE : t1 ≤ t1 + 1 := by simp only [Time] at *; omega
            obtain ⟨jhp, hARR, hBET, hHP, hNCOMP⟩ :=
              @not_quiet_implies_exists_pending_job _ _ _ _ job_arrival job_cost job_task
                arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
                H_completed_jobs_dont_execute t1 (t1 + 1) hLE hQT hNQ
            -- jhp arrived between t1 and t1+1, so job_arrival jhp = t1 = t
            refine ⟨jhp, hARR, ?_, hHP⟩
            constructor
            · simp only [has_arrived, arrived_between] at *
              simp only [Time] at *; omega
            · intro hC
              exact hNCOMP (completion_monotonic job_cost sched jhp t (t1 + 1) (by subst hEQ; omega) hC)
          · -- t > t1: t is not quiet
            have hGE' : t1 < t := by simp only [Time] at *; omega
            have hNQ : ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t :=
              hNQT t ⟨hGE', hLT⟩
            have hLE : t1 ≤ t := by simp only [Time] at *; omega
            obtain ⟨jhp, hARR, hBET, hHP, hNCOMP⟩ :=
              @not_quiet_implies_exists_pending_job _ _ _ _ job_arrival job_cost job_task
                arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
                H_completed_jobs_dont_execute t1 t hLE hQT hNQ
            refine ⟨jhp, hARR, ?_, hHP⟩
            constructor
            · simp only [has_arrived, arrived_between] at *
              simp only [Time] at *; omega
            · exact hNCOMP
        · -- Case 2: t1 + 1 ≥ t2
          push_neg at hGT
          have hTeq : t1 = t := by simp only [Time] at *; omega
          have hARReq : job_arrival j = t := by simp only [Time] at *; omega
          exists j
          refine ⟨H_from_arrival_sequence, ?_, H_priority_is_reflexive j⟩
          rw [← hARReq]
          exact job_pending_at_arrival job_arrival job_cost sched H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute j arr_seq H_from_arrival_sequence H_job_cost_positive

      include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive H_priority_is_transitive H_busy_interval_prefix in
      theorem not_quiet_implies_not_idle :
          ∀ t,
            t1 ≤ t ∧ t < t2 →
            ¬ (is_idle sched t = true) := by
        intro t hNEQ hIDLE
        obtain ⟨jhp, hARR, hPEND, _hHP⟩ := pending_hp_job_exists job_arrival job_cost job_task
          arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
          higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
          H_work_conserving H_completed_jobs_dont_execute
          H_jobs_must_arrive_to_execute H_priority_is_reflexive H_priority_is_transitive t1 t2
          H_busy_interval_prefix t hNEQ
        -- jhp is pending, so it's backlogged (since not scheduled — processor idle)
        have hNSCHED : ¬ (scheduled_at sched jhp t = true) := by
          simp only [is_idle, beq_iff_eq] at hIDLE
          simp only [scheduled_at, beq_iff_eq]
          rw [hIDLE]; simp
        have hBACK : backlogged job_arrival job_cost sched jhp t := ⟨hPEND, hNSCHED⟩
        -- By work_conserving, there exists a scheduled job
        obtain ⟨jo, hSCHED⟩ := H_work_conserving jhp t hARR hBACK
        -- But the processor is idle
        simp only [is_idle, beq_iff_eq] at hIDLE
        simp only [scheduled_at, beq_iff_eq] at hSCHED
        rw [hIDLE] at hSCHED; simp at hSCHED

    end ProcessorAlwaysBusy

    section QuietTimeAndServiceOfJobs

      variable (H_arrival_sequence_is_a_set :
        arrival_sequence_is_a_set arr_seq)

      variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
      variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

      variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)

      variable (t1 : Time)
      variable (H_quiet_time : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1)

      variable (Δ : Time)
      variable (H_no_quiet_time : ∀ t, t1 < t ∧ t ≤ t1 + Δ →
        ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t)

      include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_quiet_time H_no_quiet_time in
      theorem hep_jobs_receive_no_service_before_quiet_time :
          service_of_higher_or_equal_priority_jobs sched
            (jobs_arrived_between arr_seq t1 (t1 + Δ)) higher_eq_priority j t1 (t1 + Δ) =
          service_of_higher_or_equal_priority_jobs sched
            (jobs_arrived_between arr_seq 0 (t1 + Δ)) higher_eq_priority j t1 (t1 + Δ) := by
        -- Unfold to service_of_jobs
        simp only [service_of_higher_or_equal_priority_jobs]
        -- Split [0, t1+Δ) = [0, t1) ++ [t1, t1+Δ)
        conv_rhs =>
          rw [show jobs_arrived_between arr_seq 0 (t1 + Δ) =
            jobs_arrived_between arr_seq 0 t1 ++ jobs_arrived_between arr_seq t1 (t1 + Δ) from
            job_arrived_between_cat arr_seq 0 t1 (t1 + Δ) (Nat.zero_le _) (Nat.le_add_right _ _)]
        simp only [service_of_jobs]
        rw [List.filter_append, List.map_append, List.sum_append]
        -- Show the service from [0, t1) jobs is 0
        suffices h_zero : ((jobs_arrived_between arr_seq 0 t1).filter
            (fun j_hp => higher_eq_priority j_hp j) |>.map
            (fun j' => service_during sched j' t1 (t1 + Δ))).sum = 0 by
          omega
        apply List.sum_eq_zero
        intro x hx
        rw [List.mem_map] at hx
        obtain ⟨jhp, hjhp_mem, rfl⟩ := hx
        rw [List.mem_filter] at hjhp_mem
        obtain ⟨hjhp_arr, hjhp_hp⟩ := hjhp_mem
        -- jhp arrived in [0, t1) and has higher_eq_priority
        have hARR := in_arrivals_implies_arrived job_arrival arr_seq
          H_arrival_times_are_consistent jhp 0 t1 hjhp_arr
        have hBEF := in_arrivals_implies_arrived_before job_arrival arr_seq
          H_arrival_times_are_consistent jhp t1 hjhp_arr
        -- jhp is completed at t1 by quiet time
        have hCOMP := H_quiet_time jhp hARR hjhp_hp hBEF
        -- service_during sched jhp t1 (t1 + Δ) = 0
        -- Because jhp is completed at every t ≥ t1, hence not scheduled at any t ≥ t1
        simp only [service_during]
        apply Finset.sum_eq_zero
        intro t ht
        rw [Finset.mem_Ico] at ht
        have hCOMPt := completion_monotonic job_cost sched jhp t1 t (by simp only [Time] at *; omega) hCOMP
        have hNSCHED := completed_implies_not_scheduled job_cost sched jhp H_completed_jobs_dont_execute t hCOMPt
        simp only [service_at, scheduled_at]
        cases heq : (sched t == some jhp)
        · simp [Bool.toNat]
        · exfalso; exact hNSCHED (by simp [scheduled_at, beq_iff_eq.mp heq])

      include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_quiet_time H_no_quiet_time in
       theorem no_idle_time_within_non_quiet_time_interval :
          service_of_jobs sched (jobs_arrived_between arr_seq 0 (t1 + Δ)) (fun _ => true) t1 (t1 + Δ) = Δ := by
        apply le_antisymm
        · -- ≤ Δ : service bounded by interval length
          have h_nodup := arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent
            H_arrival_sequence_is_a_set 0 (t1 + Δ)
          have h := service_of_jobs_le_delta job_cost sched (jobs_arrived_between arr_seq 0 (t1 + Δ))
            (fun _ => true) H_completed_jobs_dont_execute h_nodup t1 (t1 + Δ)
          simp only [Time] at *; omega
        · -- ≥ Δ : at each time t' in [t1, t1+Δ), processor is not idle
          -- Sufficient to show: ∀ t' ∈ Ico t1 (t1+Δ), service_at contribution ≥ 1
          suffices h_each : ∀ t', t' ∈ Finset.Ico t1 (t1 + Δ) →
              1 ≤ ((jobs_arrived_between arr_seq 0 (t1 + Δ)).filter (fun _ => true) |>.map
                (fun j' => service_at sched j' t')).sum by
            unfold service_of_jobs service_during
            have h_swap : ∀ (l : List Job),
                (l.map (fun j' => ∑ t' ∈ Finset.Ico t1 (t1 + Δ), service_at sched j' t')).sum =
                ∑ t' ∈ Finset.Ico t1 (t1 + Δ), (l.map (fun j' => service_at sched j' t')).sum := by
              intro l; induction l with
              | nil => simp
              | cons a l ih =>
                simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
            rw [h_swap]
            calc Δ = ∑ _t' ∈ Finset.Ico t1 (t1 + Δ), 1 := by
                    simp [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
                 _ ≤ ∑ t' ∈ Finset.Ico t1 (t1 + Δ),
                    ((jobs_arrived_between arr_seq 0 (t1 + Δ)).filter (fun _ => true) |>.map
                      (fun j' => service_at sched j' t')).sum :=
                    Finset.sum_le_sum h_each
          intro t' ht'
          rw [Finset.mem_Ico] at ht'
          -- At time t', the processor is not idle
          have h_not_idle : ¬ (is_idle sched t' = true) := by
            intro hIDLE
            -- Helper: idle at t' implies quiet at t'+1
            have idle_implies_quiet : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (t' + 1) := by
              intro jhp hARR hHP hAB
              by_contra hNCOMP
              have hARRIVED : has_arrived job_arrival jhp t' := by
                simp only [arrived_before] at hAB; simp only [has_arrived]; simp only [Time] at *; omega
              have hNCOMP_t : ¬ completed_by job_cost sched jhp t' := by
                intro hCOMP
                exact hNCOMP (completion_monotonic job_cost sched jhp t' (t' + 1) (by simp only [Time] at *; omega) hCOMP)
              have hPEND : pending job_arrival job_cost sched jhp t' := ⟨hARRIVED, hNCOMP_t⟩
              have hNSCHED : ¬ (scheduled_at sched jhp t' = true) := by
                simp only [is_idle, beq_iff_eq] at hIDLE
                simp only [scheduled_at, beq_iff_eq]; rw [hIDLE]; simp
              have hBACK : backlogged job_arrival job_cost sched jhp t' := ⟨hPEND, hNSCHED⟩
              obtain ⟨jo, hSCHED⟩ := H_work_conserving jhp t' hARR hBACK
              simp only [is_idle, beq_iff_eq] at hIDLE
              simp only [scheduled_at, beq_iff_eq] at hSCHED
              rw [hIDLE] at hSCHED; simp at hSCHED
            by_cases hEQ : t1 = t'
            · rw [← hEQ] at idle_implies_quiet
              exact H_no_quiet_time (t1 + 1) ⟨by simp only [Time] at *; omega, by simp only [Time] at *; omega⟩ idle_implies_quiet
            · -- t' > t1, so t' ∈ (t1, t1+Δ], hence ¬ quiet_time t'
              -- But we can also show quiet at t'+1 which is in (t1, t1+Δ]
              -- We know t1 < t' < t1 + Δ, so t'+1 ≤ t1 + Δ
              exact H_no_quiet_time (t' + 1) ⟨by simp only [Time] at *; omega, by simp only [Time] at *; omega⟩ idle_implies_quiet
          -- sched t' = some j1 for some j1
          simp only [is_idle, beq_iff_eq] at h_not_idle
          push_neg at h_not_idle
          obtain ⟨j1, hj1⟩ : ∃ j1, sched t' = some j1 := by
            cases heq : sched t' with
            | none => exact absurd heq h_not_idle
            | some j1 => exact ⟨j1, rfl⟩
          have hSCHED_j1 : scheduled_at sched j1 t' = true := by
            simp [scheduled_at, hj1]
          have hARR_j1 := H_jobs_come_from_arrival_sequence j1 t' hSCHED_j1
          have hARRIVED_j1 := H_jobs_must_arrive_to_execute j1 t' hSCHED_j1
          have hIN_j1 : j1 ∈ jobs_arrived_between arr_seq 0 (t1 + Δ) :=
            arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
              j1 0 (t1 + Δ) hARR_j1
              ⟨Nat.zero_le _, by simp only [has_arrived] at hARRIVED_j1; simp only [Time] at *; omega⟩
          have hIN_filtered : j1 ∈ (jobs_arrived_between arr_seq 0 (t1 + Δ)).filter (fun _ => true) := by
            rw [List.mem_filter]; exact ⟨hIN_j1, rfl⟩
          have hSA : service_at sched j1 t' = 1 := by
            simp only [service_at, scheduled_at, hj1]; simp [Bool.toNat]
          have hSA_in : service_at sched j1 t' ∈
              ((jobs_arrived_between arr_seq 0 (t1 + Δ)).filter (fun _ => true) |>.map
                (fun j' => service_at sched j' t')) :=
            List.mem_map.mpr ⟨j1, hIN_filtered, rfl⟩
          have hSA_le := List.le_sum_of_mem hSA_in
          simp only [Time] at *; omega

    end QuietTimeAndServiceOfJobs

    section BoundingBusyInterval

      variable (H_arrival_sequence_is_a_set :
        arrival_sequence_is_a_set arr_seq)

      variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
      variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

      variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)

      variable (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
      variable (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority)

      private abbrev hp_workload (t1' t2' : Time) :=
        workload_of_higher_or_equal_priority_jobs
          job_cost (jobs_arrived_between arr_seq t1' t2') higher_eq_priority j

      private abbrev hp_service (t1' t2' : Time) :=
        service_of_higher_or_equal_priority_jobs
          sched (jobs_arrived_between arr_seq t1' t2') higher_eq_priority j t1' t2'

      section BoundingBusyInterval'

        variable (t_busy : Time)
        variable (H_j_is_pending : pending job_arrival job_cost sched j t_busy)

        section LowerBound

          include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_j_is_pending in
          theorem exists_busy_interval_prefix :
              ∃ t1,
                busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 (t_busy + 1) ∧
                t1 ≤ job_arrival j ∧ job_arrival j ≤ t_busy := by
            by_cases hEX : ∃ t, t ≤ t_busy ∧ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t
            · -- Case 1: there exists a quiet time ≤ t_busy
              have hDP : DecidablePred (fun t => quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true) :=
                fun t => inferInstanceAs (Decidable (quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true))
              set last0 := @Nat.findGreatest (fun t => quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true) hDP t_busy with hlast0_def
              obtain ⟨t, htb, hq⟩ := hEX
              have hPRED : quiet_time_dec job_cost arr_seq sched higher_eq_priority j last0 = true := by
                exact @Nat.findGreatest_spec t (fun t => quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true) hDP t_busy
                  htb ((quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j t).mpr hq)
              have hQUIET : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j last0 :=
                (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j last0).mp hPRED
              have hlast0_le : last0 ≤ t_busy := @Nat.findGreatest_le _ hDP t_busy
              have hJA_ge : last0 ≤ job_arrival j := by
                by_contra hBEFORE
                push_neg at hBEFORE
                have hHP := H_priority_is_reflexive j
                have hAB : arrived_before job_arrival j last0 := hBEFORE
                have hCOMP := hQUIET j H_from_arrival_sequence hHP hAB
                have hCOMP_busy := completion_monotonic job_cost sched j last0 t_busy hlast0_le hCOMP
                exact H_j_is_pending.2 hCOMP_busy
              have hJA_le : job_arrival j ≤ t_busy := H_j_is_pending.1
              have hLT : last0 < t_busy + 1 := Nat.lt_succ_of_le hlast0_le
              have hNQT : ∀ t0, last0 < t0 ∧ t0 < t_busy + 1 → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t0 := by
                intro t0 ⟨hGT, hLTbusy⟩ hQ
                have ht0_le : t0 ≤ t_busy := Nat.lt_succ_iff.mp hLTbusy
                have hDEC : quiet_time_dec job_cost arr_seq sched higher_eq_priority j t0 = true :=
                  (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j t0).mpr hQ
                exact @Nat.findGreatest_is_greatest t0 (fun t => quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true) hDP t_busy hGT ht0_le hDEC
              exact ⟨last0, ⟨hLT, hQUIET, hNQT, hJA_ge, Nat.lt_succ_of_le hJA_le⟩, hJA_ge, hJA_le⟩
            · -- Case 2: no quiet time in [0, t_busy]
              push_neg at hEX
              refine ⟨0, ⟨Nat.succ_pos _, ?_, ?_, Nat.zero_le _, Nat.lt_succ_of_le H_j_is_pending.1⟩,
                Nat.zero_le _, H_j_is_pending.1⟩
              · intro jhp _ _ hAB
                exact absurd hAB (Nat.not_lt_zero _)
              · intro t0 ⟨hGT, hLT⟩ hQ
                exact hEX t0 (Nat.lt_succ_iff.mp hLT) hQ

        end LowerBound

        section UpperBound

          variable (t1 : Time)
          variable (H_is_busy_prefix :
            busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 (t_busy + 1))

          variable (priority_inversion_bound : Time)
          variable (H_priority_inversion_is_bounded :
            priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j priority_inversion_bound)

          variable (delta : Time)
          variable (H_delta_positive : delta > 0)
          variable (H_workload_is_bounded :
            priority_inversion_bound +
              hp_workload job_cost arr_seq higher_eq_priority j t1 (t1 + delta) ≤ delta)

          section CannotBeBusyForSoLong

            variable (H_no_quiet_time :
              ∀ t, t1 < t ∧ t ≤ t1 + delta →
                ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t)

            include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_j_is_pending H_is_busy_prefix H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded H_no_quiet_time in
            theorem busy_interval_has_uninterrupted_service :
                delta ≤ priority_inversion_bound +
                  service_of_higher_or_equal_priority_jobs
                    sched (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j t1 (t1 + delta) := by
              have hPREFIX := H_is_busy_prefix
              obtain ⟨_, hQT, _, hEXj⟩ := H_is_busy_prefix
              -- Case split
              by_cases hKLE : delta ≤ priority_inversion_bound
              · exact Nat.le_trans hKLE (Nat.le_add_right _ _)
              · push_neg at hKLE
                -- total service = delta
                have hTOTAL := no_idle_time_within_non_quiet_time_interval job_arrival job_cost
                  job_task arr_seq H_arrival_times_are_consistent sched
                  H_jobs_come_from_arrival_sequence higher_eq_priority tsk j
                  H_from_arrival_sequence H_job_task H_job_cost_positive
                  H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute
                  H_completed_jobs_dont_execute H_work_conserving t1 hQT delta H_no_quiet_time
                -- hep service from [t1,t1+d) arrivals = from [0,t1+d) arrivals
                have hHEP := hep_jobs_receive_no_service_before_quiet_time job_arrival job_cost
                  job_task arr_seq H_arrival_times_are_consistent sched
                  H_jobs_come_from_arrival_sequence higher_eq_priority tsk j
                  H_from_arrival_sequence H_job_task H_job_cost_positive
                  H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute
                  H_completed_jobs_dont_execute H_work_conserving t1 hQT delta H_no_quiet_time
                -- cum_prio_inv ≤ PIB
                have hCPI_le : cumulative_priority_inversion sched higher_eq_priority j t1 (t1 + delta) ≤ priority_inversion_bound := by
                  by_cases hLE : t1 + delta ≤ t_busy + 1
                  · have hBND := H_priority_inversion_is_bounded t1 (t_busy + 1) hPREFIX
                    calc cumulative_priority_inversion sched higher_eq_priority j t1 (t1 + delta)
                        ≤ cumulative_priority_inversion sched higher_eq_priority j t1 (t_busy + 1) := by
                          unfold cumulative_priority_inversion
                          apply Finset.sum_le_sum_of_subset_of_nonneg
                          · exact Finset.Ico_subset_Ico le_rfl hLE
                          · intros; exact Nat.zero_le _
                      _ ≤ priority_inversion_bound := hBND
                  · push_neg at hLE
                    have hPREFIX' : busy_interval_prefix job_arrival job_cost arr_seq sched
                        higher_eq_priority j t1 (t1 + delta) := by
                      refine ⟨Nat.lt_add_of_pos_right H_delta_positive, hQT, ?_, ?_, ?_⟩
                      · intro t ⟨hgt, hlt⟩
                        exact H_no_quiet_time t ⟨hgt, Nat.le_of_lt hlt⟩
                      · exact hPREFIX.2.2.2.1
                      · simp only [Time] at *; omega
                    exact H_priority_inversion_is_bounded t1 (t1 + delta) hPREFIX'
                -- Decomposition: total ≤ cum_prio_inv + hep_service_from_all
                set all_jobs := jobs_arrived_between arr_seq 0 (t1 + delta)
                have hDECOMP : service_of_jobs sched all_jobs (fun _ => true) t1 (t1 + delta) ≤
                    cumulative_priority_inversion sched higher_eq_priority j t1 (t1 + delta) +
                    service_of_higher_or_equal_priority_jobs sched all_jobs higher_eq_priority j t1 (t1 + delta) := by
                  unfold service_of_jobs service_of_higher_or_equal_priority_jobs service_of_jobs
                    cumulative_priority_inversion is_priority_inversion
                  simp only [service_during]
                  -- Swap sums
                  have h_swap : ∀ (l : List Job),
                      (l.map (fun jk => ∑ t' ∈ Finset.Ico t1 (t1 + delta), service_at sched jk t')).sum =
                      ∑ t' ∈ Finset.Ico t1 (t1 + delta), (l.map (fun jk => service_at sched jk t')).sum := by
                    intro l; induction l with
                    | nil => simp
                    | cons a l ih => simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
                  rw [h_swap, h_swap, ← Finset.sum_add_distrib]
                  apply Finset.sum_le_sum
                  intro t ht
                  rw [Finset.mem_Ico] at ht
                  cases hsched_t : sched t with
                  | none =>
                    have : ((all_jobs.filter fun _ => true).map fun jk => service_at sched jk t).sum = 0 := by
                      apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
                      obtain ⟨j', _, rfl⟩ := hx
                      simp only [service_at, scheduled_at, hsched_t]; simp
                    simp only [hsched_t] at *; omega
                  | some j1 =>
                    by_cases hHEP_j1 : higher_eq_priority j1 j = true
                    · -- hep job: prio_inv = 0, hep_service ≥ 1
                      have hPI : (if higher_eq_priority j1 j = true then 0 else 1) = 0 := by simp [hHEP_j1]
                      have hARR_j1 := H_jobs_come_from_arrival_sequence j1 t (by simp [scheduled_at, hsched_t])
                      have hHA_j1 := H_jobs_must_arrive_to_execute j1 t (by simp [scheduled_at, hsched_t])
                      have hIN_j1 : j1 ∈ all_jobs :=
                        arrived_between_implies_in_arrivals job_arrival arr_seq
                          H_arrival_times_are_consistent j1 0 (t1 + delta) hARR_j1
                          ⟨Nat.zero_le _, by simp only [has_arrived] at hHA_j1; simp only [Time] at *; omega⟩
                      have hIN_f : j1 ∈ all_jobs.filter (fun j_hp => higher_eq_priority j_hp j) := by
                        rw [List.mem_filter]; exact ⟨hIN_j1, hHEP_j1⟩
                      have hSA_j1 : service_at sched j1 t = 1 := by
                        simp [service_at, scheduled_at, hsched_t]
                      have hHEP_sum : 1 ≤ ((all_jobs.filter fun j_hp => higher_eq_priority j_hp j).map fun jk => service_at sched jk t).sum :=
                        le_trans (by omega : 1 ≤ service_at sched j1 t) (List.le_sum_of_mem (List.mem_map.mpr ⟨j1, hIN_f, rfl⟩))
                      have hTOTAL_le : ((all_jobs.filter (fun (_ : Job) => true)).map (fun jk => service_at sched jk t)).sum ≤ 1 :=
                        service_of_jobs_le_1 job_arrival arr_seq
                          H_arrival_times_are_consistent H_arrival_sequence_is_a_set sched
                          H_jobs_come_from_arrival_sequence 0 (t1 + delta) t (fun _ => true)
                      simp only [hsched_t, hPI] at *; omega
                    · -- non-hep job: prio_inv = 1
                      have hPI : (if higher_eq_priority j1 j = true then 0 else 1) = 1 := by simp [hHEP_j1]
                      have hTOTAL_le : ((all_jobs.filter (fun (_ : Job) => true)).map (fun jk => service_at sched jk t)).sum ≤ 1 :=
                        service_of_jobs_le_1 job_arrival arr_seq
                          H_arrival_times_are_consistent H_arrival_sequence_is_a_set sched
                          H_jobs_come_from_arrival_sequence 0 (t1 + delta) t (fun _ => true)
                      simp only [hsched_t, hPI] at *; omega
                -- Combine
                calc delta
                    = service_of_jobs sched all_jobs (fun _ => true) t1 (t1 + delta) := hTOTAL.symm
                  _ ≤ cumulative_priority_inversion sched higher_eq_priority j t1 (t1 + delta) +
                      service_of_higher_or_equal_priority_jobs sched all_jobs higher_eq_priority j t1 (t1 + delta) := hDECOMP
                  _ = cumulative_priority_inversion sched higher_eq_priority j t1 (t1 + delta) +
                      service_of_higher_or_equal_priority_jobs sched (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j t1 (t1 + delta) := by
                      rw [← hHEP]
                  _ ≤ priority_inversion_bound +
                      service_of_higher_or_equal_priority_jobs sched (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j t1 (t1 + delta) :=
                      Nat.add_le_add_right hCPI_le _

            include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_j_is_pending H_is_busy_prefix H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded H_no_quiet_time in
            theorem busy_interval_too_much_workload :
                workload_of_higher_or_equal_priority_jobs
                  job_cost (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j >
                service_of_higher_or_equal_priority_jobs
                    sched (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j t1 (t1 + delta) := by
              -- Get quiet time at t1 from busy_interval_prefix
              obtain ⟨_, hQT, _, _⟩ := H_is_busy_prefix
              -- t1 + delta is not quiet
              have hNQ : ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (t1 + delta) :=
                H_no_quiet_time (t1 + delta) ⟨Nat.lt_add_of_pos_right H_delta_positive, le_rfl⟩
              -- Get a pending hep job j0 in [t1, t1+delta) that is not completed
              have hPEND := not_quiet_implies_exists_pending_job job_arrival job_cost job_task arr_seq
                H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority
                tsk j H_from_arrival_sequence H_job_task H_job_cost_positive H_completed_jobs_dont_execute
                t1 (t1 + delta) (Nat.le_add_right _ _) hQT hNQ
              obtain ⟨j0, hARR0, hBTW0, hHP0, hNCOMP0⟩ := hPEND
              set l := jobs_arrived_between arr_seq t1 (t1 + delta) with hl_def
              have hIN0 : j0 ∈ l :=
                arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent
                  j0 t1 (t1 + delta) hARR0 hBTW0
              -- For all hep jobs: service ≤ cost
              have hSLE : ∀ j', j' ∈ l → higher_eq_priority j' j = true →
                  service_during sched j' t1 (t1 + delta) ≤ job_cost j' :=
                fun j' _ _ => cumulative_service_le_job_cost job_cost sched j'
                  H_completed_jobs_dont_execute t1 (t1 + delta)
              -- For j0: service < cost (since not completed)
              have hSLT0 : service_during sched j0 t1 (t1 + delta) < job_cost j0 := by
                by_contra h
                push_neg at h
                have hcat := service_during_cat sched j0 t1 0 (t1 + delta)
                  ⟨Nat.zero_le _, Nat.le_add_right _ _⟩
                have hge : job_cost j0 ≤ service_during sched j0 0 (t1 + delta) :=
                  calc job_cost j0
                      ≤ service_during sched j0 t1 (t1 + delta) := h
                    _ ≤ service_during sched j0 0 t1 + service_during sched j0 t1 (t1 + delta) := Nat.le_add_left _ _
                    _ = service_during sched j0 0 (t1 + delta) := hcat.symm
                exact hNCOMP0 hge
              -- Overall: service ≤ workload (by leq_sum_seq)
              have hLE := Prosa.Util.Sum.leq_sum_seq l (fun j_hp => higher_eq_priority j_hp j)
                (fun j' => service_during sched j' t1 (t1 + delta))
                (fun j' => job_cost j')
                hSLE
              -- Workload ≠ service (because j0 has strict inequality)
              have hNE : workload_of_higher_or_equal_priority_jobs job_cost l higher_eq_priority j ≠
                  service_of_higher_or_equal_priority_jobs sched l higher_eq_priority j t1 (t1 + delta) := by
                intro hEQ
                have hEQ_j0 := Prosa.Util.Sum.sum_majorant_eqn l
                  (fun j' => service_during sched j' t1 (t1 + delta))
                  (fun j' => job_cost j')
                  (fun j_hp => higher_eq_priority j_hp j)
                  hSLE
                  (by unfold workload_of_higher_or_equal_priority_jobs workload_of_jobs
                        service_of_higher_or_equal_priority_jobs service_of_jobs at hEQ
                      exact hEQ.symm)
                  j0 hIN0 hHP0
                dsimp at hEQ_j0
                omega
              -- Combine
              unfold workload_of_higher_or_equal_priority_jobs workload_of_jobs at hNE ⊢
              unfold service_of_higher_or_equal_priority_jobs service_of_jobs at hNE ⊢
              exact Nat.lt_of_le_of_ne hLE (Ne.symm hNE)

            include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_j_is_pending H_is_busy_prefix H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded H_no_quiet_time in
            theorem busy_interval_workload_larger_than_interval :
                priority_inversion_bound +
                  hp_workload job_cost arr_seq higher_eq_priority j t1 (t1 + delta) > delta := by
              have h1 := busy_interval_has_uninterrupted_service job_arrival job_cost
                job_task arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
                H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
                H_work_conserving H_priority_is_reflexive H_priority_is_transitive t_busy
                H_j_is_pending t1 H_is_busy_prefix priority_inversion_bound
                H_priority_inversion_is_bounded delta H_delta_positive H_workload_is_bounded H_no_quiet_time
              have h2 := busy_interval_too_much_workload job_arrival job_cost
                job_task arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
                H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
                H_work_conserving H_priority_is_reflexive H_priority_is_transitive t_busy
                H_j_is_pending t1 H_is_busy_prefix priority_inversion_bound
                H_priority_inversion_is_bounded delta H_delta_positive H_workload_is_bounded H_no_quiet_time
              exact Nat.lt_of_le_of_lt h1 (Nat.add_lt_add_left h2 priority_inversion_bound)

          end CannotBeBusyForSoLong

          include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_j_is_pending H_is_busy_prefix H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded in
          theorem busy_interval_is_bounded :
              ∃ t2,
                t2 ≤ t1 + delta ∧
                busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 := by
            -- Case split: does there exist a quiet time in (t1, t1 + delta]?
            by_cases hEX : ∃ t2, t1 < t2 ∧ t2 ≤ t1 + delta ∧
                quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2
            · -- Case 1: there exists such a quiet time; pick the minimum
              obtain ⟨t2_ex, ht2_gt, ht2_le, ht2_quiet⟩ := hEX
              -- Use well-ordering: find minimum t2 with t1 < t2 ∧ t2 ≤ t1 + delta ∧ quiet
              have hEX_dec : ∃ n, (t1 + 1 + n ≤ t1 + delta ∧
                  quiet_time_dec job_cost arr_seq sched higher_eq_priority j (t1 + 1 + n) = true) := by
                refine ⟨t2_ex - (t1 + 1), ?_⟩
                constructor
                · simp only [Time] at *; omega
                · rw [show t1 + 1 + (t2_ex - (t1 + 1)) = t2_ex from by simp only [Time] at *; omega]
                  exact (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
                    sched H_jobs_come_from_arrival_sequence higher_eq_priority j t2_ex).mpr ht2_quiet
              set n_min := Nat.find hEX_dec with hn_min_def
              have hn_spec := Nat.find_spec hEX_dec
              obtain ⟨hn_le, hn_dec⟩ := hn_spec
              set t2_min := t1 + 1 + n_min
              have hn_quiet : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2_min :=
                (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
                  sched H_jobs_come_from_arrival_sequence higher_eq_priority j t2_min).mp hn_dec
              have hn_gt : t1 < t2_min := by simp only [Time, t2_min] at *; omega
              refine ⟨t2_min, hn_le, ?_⟩
              constructor
              · -- busy_interval_prefix
                obtain ⟨hLT1, hQT1, hNQT1, hARR⟩ := H_is_busy_prefix
                refine ⟨hn_gt, hQT1, ?_, ?_⟩
                · -- ∀ t, t1 < t ∧ t < t2_min → ¬ quiet_time j t
                  intro t ⟨hGT, hLT⟩ hQT
                  have hk_lt : t - (t1 + 1) < n_min := by simp only [Time, t2_min] at *; omega
                  have hNOT := Nat.find_min hEX_dec hk_lt
                  apply hNOT
                  constructor
                  · simp only [Time] at *; omega
                  · rw [show t1 + 1 + (t - (t1 + 1)) = t from by simp only [Time] at *; omega]
                    exact (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
                      sched H_jobs_come_from_arrival_sequence higher_eq_priority j t).mpr hQT
                · -- t1 ≤ job_arrival j ∧ job_arrival j < t2_min
                  constructor
                  · exact hARR.1
                  · have hBUSY_LT : t_busy < t2_min := by
                      by_contra hCONTR
                      push_neg at hCONTR
                      exact hNQT1 t2_min ⟨hn_gt, by simp only [Time] at *; omega⟩ hn_quiet
                    simp only [Time] at *; omega
              · exact hn_quiet
            · -- Case 2: no quiet time in (t1, t1+delta] → contradiction
              push_neg at hEX
              exfalso
              have hALL : ∀ t, t1 < t ∧ t ≤ t1 + delta →
                  ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t := by
                intro t ⟨hGT, hLE⟩ hQT
                exact hEX t hGT hLE hQT
              have hTOOMUCH := busy_interval_workload_larger_than_interval job_arrival job_cost
                job_task arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
                H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
                H_work_conserving H_priority_is_reflexive H_priority_is_transitive t_busy
                H_j_is_pending t1 H_is_busy_prefix priority_inversion_bound
                H_priority_inversion_is_bounded delta H_delta_positive H_workload_is_bounded hALL
              simp only [Time] at *; omega

        end UpperBound

      end BoundingBusyInterval'

      section BusyIntervalFromWorkloadBound

        variable (priority_inversion_bound : Time)
        variable (H_priority_inversion_is_bounded :
          priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j priority_inversion_bound)

        variable (delta : Time)
        variable (H_delta_positive : delta > 0)
        variable (H_workload_is_bounded :
          ∀ t, priority_inversion_bound +
            hp_workload job_cost arr_seq higher_eq_priority j t (t + delta) ≤ delta)

        variable (H_positive_cost : job_cost j > 0)

        include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded H_positive_cost in
        theorem exists_busy_interval :
            ∃ t1 t2,
              t1 ≤ job_arrival j ∧ job_arrival j < t2 ∧
              t2 ≤ t1 + delta ∧
              busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 := by
          -- j is pending at job_arrival j
          have hPEND : pending job_arrival job_cost sched j (job_arrival j) := by
            exact job_pending_at_arrival job_arrival job_cost sched H_jobs_must_arrive_to_execute
              H_completed_jobs_dont_execute j arr_seq H_from_arrival_sequence H_positive_cost
          -- Get a busy interval prefix
          have hPREFIX := exists_busy_interval_prefix job_arrival job_cost job_task arr_seq
            H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
            higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
            H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            H_work_conserving H_priority_is_reflexive H_priority_is_transitive
            (job_arrival j) hPEND
          obtain ⟨t1, hPrefix, hGE1, hGEarr⟩ := hPREFIX
          -- Get bounded busy interval
          have hBOUNDED := busy_interval_is_bounded job_arrival job_cost job_task arr_seq
            H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
            higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
            H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            H_work_conserving H_priority_is_reflexive H_priority_is_transitive
            (job_arrival j) hPEND t1 hPrefix priority_inversion_bound
            H_priority_inversion_is_bounded delta H_delta_positive (H_workload_is_bounded t1)
          obtain ⟨t2, hGE2, hBUSY_int⟩ := hBOUNDED
          refine ⟨t1, t2, hGE1, ?_, hGE2, hBUSY_int⟩
          -- Need: job_arrival j < t2
          by_contra hNLT
          push_neg at hNLT
          -- If t2 ≤ job_arrival j, then t2 is quiet and t2 ∈ (t1, t_busy+1)
          have hLT12 : t1 < t2 := hBUSY_int.1.1
          have hQUIET := hBUSY_int.2
          obtain ⟨_, _, hNQT1, _⟩ := hPrefix
          -- t2 is in (t1, t_busy+1) since t2 ≤ job_arrival j ≤ t_busy
          have : t2 < job_arrival j + 1 := by simp only [Time] at *; omega
          -- t2 is quiet but in (t1, t_busy+1), contradicting prefix
          exact hNQT1 t2 ⟨hLT12, this⟩ hQUIET

      end BusyIntervalFromWorkloadBound

      section ResponseTimeBoundFromBusyInterval

        variable (priority_inversion_bound : Time)
        variable (H_priority_inversion_is_bounded :
          priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j priority_inversion_bound)

        variable (delta : Time)
        variable (H_delta_positive : delta > 0)
        variable (H_workload_is_bounded :
          ∀ t, priority_inversion_bound +
            hp_workload job_cost arr_seq higher_eq_priority j t (t + delta) ≤ delta)

        include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_job_task H_job_cost_positive H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_priority_is_reflexive H_priority_is_transitive H_priority_inversion_is_bounded H_delta_positive H_workload_is_bounded in
        theorem busy_interval_bounds_response_time :
            completed_by job_cost sched j (job_arrival j + delta) := by
          -- Get busy interval
          have hBUSY := exists_busy_interval job_arrival job_cost job_task arr_seq
            H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
            higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
            H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            H_work_conserving H_priority_is_reflexive H_priority_is_transitive
            priority_inversion_bound H_priority_inversion_is_bounded
            delta H_delta_positive H_workload_is_bounded H_job_cost_positive
          obtain ⟨t1, t2, hGE1, hLT2, hGE2, hBUSYint⟩ := hBUSY
          -- j completes within the busy interval
          have hCOMPL := job_completes_within_busy_interval job_arrival job_cost job_task
            arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
            higher_eq_priority tsk j H_from_arrival_sequence H_job_task H_job_cost_positive
            H_priority_is_reflexive t1 t2 hBUSYint
          -- t2 ≤ t1 + delta ≤ job_arrival j + delta
          have hLE : t2 ≤ job_arrival j + delta := by
            simp only [Time] at *; omega
          exact completion_monotonic job_cost sched j t2 (job_arrival j + delta) hLE hCOMPL

      end ResponseTimeBoundFromBusyInterval

    end BoundingBusyInterval

  end Lemmas

  section NonOverloadedProcessor

    def no_carry_in (t : Time) :=
      ∀ j_o,
        arrives_in arr_seq j_o →
        arrived_before job_arrival j_o t →
        completed_by job_cost sched j_o t

    theorem no_carry_in_implies_quiet_time :
        ∀ j t,
          no_carry_in job_arrival job_cost arr_seq sched t →
          quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t := by
      intro j t hNC j_hp hArr _hHP hBef
      exact hNC j_hp hArr hBef

    variable (H_arrival_sequence_is_a_set :
      arrival_sequence_is_a_set arr_seq)

    variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute in
    theorem idle_instant_implies_no_carry_in_at_t :
        ∀ t,
          is_idle sched t = true →
          no_carry_in job_arrival job_cost arr_seq sched t := by
      intro t hIDLE j hARR hAB
      by_contra hNCOMPL
      -- j arrived before t, is not completed at t → pending at t
      have hARRIVED : has_arrived job_arrival j t := by
        unfold has_arrived arrived_before at *; simp only [Time] at *; omega
      have hPEND : pending job_arrival job_cost sched j t := ⟨hARRIVED, hNCOMPL⟩
      -- j is not scheduled at t (idle)
      have hNSCHED : ¬ (scheduled_at sched j t = true) := by
        simp only [is_idle, beq_iff_eq] at hIDLE
        simp only [scheduled_at, beq_iff_eq]; rw [hIDLE]; simp
      have hBACK : backlogged job_arrival job_cost sched j t := ⟨hPEND, hNSCHED⟩
      obtain ⟨j', hSCHED⟩ := H_work_conserving j t hARR hBACK
      simp only [is_idle, beq_iff_eq] at hIDLE
      simp only [scheduled_at, beq_iff_eq] at hSCHED
      rw [hIDLE] at hSCHED; simp at hSCHED

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute in
    theorem idle_instant_implies_no_carry_in_at_t_pl_1 :
        ∀ t,
          is_idle sched t = true →
          no_carry_in job_arrival job_cost arr_seq sched (t + 1) := by
      intro t hIDLE j hARR hAB
      by_contra hNCOMPL
      -- j arrived before t+1, so job_arrival j ≤ t
      have hARRIVED : has_arrived job_arrival j t := by
        unfold arrived_before at hAB; unfold has_arrived; simp only [Time] at *; omega
      -- If j were completed at t, it would be completed at t+1 by monotonicity
      have hNCOMP_t : ¬ completed_by job_cost sched j t := by
        intro hCOMP
        exact hNCOMPL (completion_monotonic job_cost sched j t (t + 1) (by simp only [Time] at *; omega) hCOMP)
      -- j is pending at t
      have hPEND : pending job_arrival job_cost sched j t := ⟨hARRIVED, hNCOMP_t⟩
      -- j is not scheduled at t (because idle)
      have hNSCHED : ¬ (scheduled_at sched j t = true) := by
        simp only [is_idle, beq_iff_eq] at hIDLE
        simp only [scheduled_at, beq_iff_eq]; rw [hIDLE]; simp
      -- j is backlogged at t
      have hBACK : backlogged job_arrival job_cost sched j t := ⟨hPEND, hNSCHED⟩
      -- By work_conserving, there exists a scheduled job
      obtain ⟨jo, hSCHED⟩ := H_work_conserving j t hARR hBACK
      -- But the processor is idle
      simp only [is_idle, beq_iff_eq] at hIDLE
      simp only [scheduled_at, beq_iff_eq] at hSCHED
      rw [hIDLE] at hSCHED; simp at hSCHED

    variable (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)

    private abbrev total_workload (t1' t2' : Time) :=
      workload_of_jobs job_cost (jobs_arrived_between arr_seq t1' t2') (fun _ => true)

    private abbrev total_service (t1' t2' : Time) :=
      service_of_jobs sched (jobs_arrived_between arr_seq 0 t2') (fun _ => true) t1' t2'

    variable (Δ : Time)
    variable (H_delta_positive : Δ > 0)
    variable (H_workload_is_bounded : ∀ t,
      total_workload job_cost arr_seq t (t + Δ) ≤ Δ)

    section ProcessorIsNotTooBusy

      theorem no_carry_in_at_the_beginning :
          no_carry_in job_arrival job_cost arr_seq sched 0 := by
        intro s _hArr hBef
        exfalso
        unfold arrived_before at hBef
        exact Nat.not_lt_zero _ hBef

      section ProcessorIsNotTooBusyInduction

        variable (t : Time)

        variable (H_no_carry_in : no_carry_in job_arrival job_cost arr_seq sched t)

        include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive H_delta_positive H_workload_is_bounded H_no_carry_in in
        theorem total_service_is_bounded_by_Δ :
            service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) ≤ Δ := by
          have h_nodup := arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent
            H_arrival_sequence_is_a_set 0 (t + Δ)
          have h := service_of_jobs_le_delta job_cost sched (jobs_arrived_between arr_seq 0 (t + Δ))
            (fun _ => true) H_completed_jobs_dont_execute h_nodup t (t + Δ)
          simp only [Time] at *; omega

        include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive H_delta_positive H_workload_is_bounded H_no_carry_in in
        theorem low_total_service_implies_existence_of_time_with_no_carry_in :
            service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) < Δ →
            ∃ δ, δ < Δ ∧ no_carry_in job_arrival job_cost arr_seq sched (t + 1 + δ) := by
          intro hLT
          -- Use low_service_implies_existence_of_idle_time to find an idle time in [t, t+Δ)
          have h_le : t ≤ t + Δ := Nat.le_add_right t Δ
          have h_serv : service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) < t + Δ - t := by
            simp only [Time] at *; omega
          obtain ⟨t_idle, hLE, hGT, hIDLE⟩ := low_service_implies_existence_of_idle_time
            job_arrival job_cost arr_seq H_arrival_times_are_consistent
            H_arrival_sequence_is_a_set sched H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute H_jobs_come_from_arrival_sequence t (t + Δ) h_le h_serv
          -- t_idle is in [t, t+Δ) and is idle
          -- Case split: t_idle = t or t_idle > t
          by_cases hEQ : t = t_idle
          · -- t_idle = t: use δ = 0
            exists 0
            constructor
            · exact H_delta_positive
            · rw [Nat.add_zero]
              rw [← hEQ] at hIDLE
              exact idle_instant_implies_no_carry_in_at_t_pl_1 job_arrival job_cost arr_seq
                H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute
                H_jobs_must_arrive_to_execute t hIDLE
          · -- t_idle > t: t_idle = t + γ for some γ > 0
            have hLT_t : t < t_idle := by simp only [Time] at *; omega
            have hEX : ∃ γ, t_idle = t + γ := ⟨t_idle - t, by simp only [Time] at *; omega⟩
            obtain ⟨γ, hγ⟩ := hEX
            subst hγ
            have hGamma_pos : 0 < γ := by simp only [Time] at *; omega
            have hGamma_lt : γ < Δ := by simp only [Time] at *; omega
            -- Use δ = γ - 1
            exists (γ - 1)
            constructor
            · simp only [Time] at *; omega
            · -- t + 1 + (γ - 1) = t + γ
              have hEQ2 : t + 1 + (γ - 1) = t + γ := by simp only [Time] at *; omega
              rw [hEQ2]
              exact idle_instant_implies_no_carry_in_at_t job_arrival job_cost arr_seq
                H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute
                H_jobs_must_arrive_to_execute (t + γ) hIDLE

        include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive H_delta_positive H_workload_is_bounded H_no_carry_in in
        theorem completion_of_all_jobs_implies_no_carry_in :
            service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) = Δ →
            no_carry_in job_arrival job_cost arr_seq sched (t + Δ) := by
          intro hEQserv
          have hWORK := H_workload_is_bounded t
          -- Step 1: all jobs in [0, t) completed by t (from H_no_carry_in)
          have hCOMPL_eq : workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 t) (fun _ => true) =
              service_of_jobs sched (jobs_arrived_between arr_seq 0 t) (fun _ => true) 0 t := by
            apply all_jobs_have_completed_impl_workload_eq_service
              job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
              H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
            intro j' hj' _
            have hARR := in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j' 0 t hj'
            have hBEF := in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent j' t hj'
            exact H_no_carry_in j' hARR hBEF
          -- Step 2: workload [0, t+Δ) = workload [0,t) + workload [t, t+Δ)
          have hWL_cat : workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) =
              workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 t) (fun _ => true) +
              workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + Δ)) (fun _ => true) :=
            workload_of_jobs_cat job_cost arr_seq t 0 (t + Δ) (fun _ => true) ⟨Nat.zero_le _, Nat.le_add_right _ _⟩
          -- Step 3: Split service [0, t+Δ) into three parts
          have hSV_cat : service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) 0 (t + Δ) =
              service_of_jobs sched (jobs_arrived_between arr_seq 0 t) (fun _ => true) 0 t +
              service_of_jobs sched (jobs_arrived_between arr_seq 0 t) (fun _ => true) t (t + Δ) +
              service_of_jobs sched (jobs_arrived_between arr_seq t (t + Δ)) (fun _ => true) t (t + Δ) := by
            exact @service_of_jobs_cat_scheduling_interval Job _ job_arrival arr_seq
              H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
              (fun _ => true) 0 (t + Δ) t ⟨Nat.zero_le _, Nat.le_add_right _ _⟩
          -- Step 4: service [0, t+Δ) [t, t+Δ) = service [0,t) [t, t+Δ) + service [t, t+Δ) [t, t+Δ)
          have hSV_arr_cat : service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) =
              service_of_jobs sched (jobs_arrived_between arr_seq 0 t) (fun _ => true) t (t + Δ) +
              service_of_jobs sched (jobs_arrived_between arr_seq t (t + Δ)) (fun _ => true) t (t + Δ) := by
            exact service_of_jobs_cat_arrival_interval
              (arr_seq := arr_seq) (sched := sched)
              (fun _ => true) 0 (t + Δ) t
              ⟨Nat.zero_le _, Nat.le_add_right _ _⟩
          -- Step 5: Derive workload [0,t+Δ) = service [0,t+Δ) [0, t+Δ)
          -- From hEQserv and hSV_arr_cat:
          --   service [0,t) [t, t+Δ) + service [t,t+Δ) [t, t+Δ) = Δ
          rw [hSV_arr_cat] at hEQserv
          -- Now hEQserv: service [0,t) [t,t+Δ) + service [t,t+Δ) [t,t+Δ) = Δ
          -- From hWORK: workload [t, t+Δ) ≤ Δ
          -- So workload [t, t+Δ) ≤ service [0,t) [t,t+Δ) + service [t,t+Δ) [t,t+Δ)
          -- Combined with hCOMPL_eq:
          --   workload [0,t+Δ) = workload [0,t) + workload [t,t+Δ)
          --                    = service [0,t) [0,t) + workload [t,t+Δ)
          --                    ≤ service [0,t) [0,t) + service [0,t) [t,t+Δ) + service [t,t+Δ) [t,t+Δ)
          --                    = service [0,t+Δ) [0,t+Δ)   (by hSV_cat)
          simp only [total_workload] at hWORK
          have hEQ : workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) =
              service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) 0 (t + Δ) := by
            apply le_antisymm
            · -- workload [0,t+Δ) ≤ service [0,t+Δ) [0,t+Δ)
              have hKey : workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + Δ)) (fun _ => true) ≤
                  service_of_jobs sched (jobs_arrived_between arr_seq 0 t) (fun _ => true) t (t + Δ) +
                  service_of_jobs sched (jobs_arrived_between arr_seq t (t + Δ)) (fun _ => true) t (t + Δ) := by
                rw [hEQserv]; exact hWORK
              rw [hWL_cat, hSV_cat]
              rw [hCOMPL_eq, Nat.add_assoc]
              exact Nat.add_le_add_left hKey _
            · exact service_of_jobs_le_workload job_cost sched (jobs_arrived_between arr_seq 0 (t + Δ))
                (fun _ => true) H_completed_jobs_dont_execute 0 (t + Δ)
          -- Step 6: Use workload_eq_service_impl_all_jobs_have_completed
          intro s hARR_s hBEF_s
          have hIN_s := arrived_between_implies_in_arrivals job_arrival arr_seq
            H_arrival_times_are_consistent s 0 (t + Δ) hARR_s
            ⟨Nat.zero_le _, hBEF_s⟩
          exact workload_eq_service_impl_all_jobs_have_completed job_arrival job_cost arr_seq
            H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute (fun _ => true) 0 (t + Δ) (t + Δ)
            hEQ s hIN_s rfl

      end ProcessorIsNotTooBusyInduction

      include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive H_delta_positive H_workload_is_bounded in
      theorem processor_is_not_too_busy :
          ∀ t, ∃ δ, δ < Δ ∧ no_carry_in job_arrival job_cost arr_seq sched (t + δ) := by
        intro t
        induction t with
        | zero =>
          exact ⟨0, H_delta_positive, by rw [Nat.zero_add]; exact no_carry_in_at_the_beginning job_arrival job_cost arr_seq sched⟩
        | succ t ih =>
          obtain ⟨δ, hLE, hFQT⟩ := ih
          by_cases hPOS : δ > 0
          · -- δ > 0: use δ - 1
            refine ⟨δ - 1, ?_, ?_⟩
            · simp only [Time] at *; omega
            · have : t + 1 + (δ - 1) = t + δ := by simp only [Time] at *; omega
              rw [this]; exact hFQT
          · -- δ = 0: no_carry_in t
            push_neg at hPOS
            have hδ0 : δ = 0 := Nat.eq_zero_of_le_zero hPOS
            subst hδ0
            rw [Nat.add_zero] at hFQT
            -- Case split on total_service t (t + Δ) vs Δ
            have hBounded := total_service_is_bounded_by_Δ job_arrival job_cost arr_seq
              H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
              higher_eq_priority H_arrival_sequence_is_a_set H_work_conserving
              H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
              H_priority_is_reflexive Δ H_delta_positive H_workload_is_bounded t hFQT
            by_cases hEQ : service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) = Δ
            · -- total_service = Δ: use δ = Δ - 1
              refine ⟨Δ - 1, ?_, ?_⟩
              · simp only [Time] at *; omega
              · have : t + 1 + (Δ - 1) = t + Δ := by simp only [Time] at *; omega
                rw [this]
                exact completion_of_all_jobs_implies_no_carry_in job_arrival job_cost arr_seq
                  H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                  higher_eq_priority H_arrival_sequence_is_a_set H_work_conserving
                  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
                  H_priority_is_reflexive Δ H_delta_positive H_workload_is_bounded t hFQT hEQ
            · -- total_service < Δ: use low_total_service_implies_existence_of_time_with_no_carry_in
              have hLT : service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) < Δ := by
                simp only [Time] at *; omega
              exact low_total_service_implies_existence_of_time_with_no_carry_in job_arrival job_cost arr_seq
                H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
                higher_eq_priority H_arrival_sequence_is_a_set H_work_conserving
                H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
                H_priority_is_reflexive Δ H_delta_positive H_workload_is_bounded t hFQT hLT

    end ProcessorIsNotTooBusy

    variable (j : Job)
    variable (H_from_arrival_sequence : arrives_in arr_seq j)
    variable (H_job_cost_positive : job_cost j > 0)

    include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive H_delta_positive H_workload_is_bounded H_from_arrival_sequence H_job_cost_positive in
    theorem exists_busy_interval_from_total_workload_bound :
        ∃ t1 t2,
          t1 ≤ job_arrival j ∧ job_arrival j < t2 ∧
          t2 ≤ t1 + Δ ∧
          busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 := by
      -- Step 1: j is pending at job_arrival j
      have hPEND : pending job_arrival job_cost sched j (job_arrival j) :=
        job_pending_at_arrival job_arrival job_cost sched H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute j arr_seq H_from_arrival_sequence H_job_cost_positive
      -- Step 2: Construct busy interval prefix (inlined from exists_busy_interval_prefix)
      -- We need to find t1 ≤ job_arrival j such that t1 is a quiet time and (t1, job_arrival j + 1) has no quiet time
      set t_busy := job_arrival j with ht_busy_def
      have hPEND_arr : has_arrived job_arrival j t_busy := le_refl _
      have hPEND_notcomp : ¬ completed_by job_cost sched j t_busy := hPEND.2
      -- Find a busy interval prefix ending at t_busy + 1
      -- Use decidability
      have hDP : DecidablePred (fun t => quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true) :=
        fun t => inferInstanceAs (Decidable (quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true))
      by_cases hEX : ∃ t, t ≤ t_busy ∧ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t
      · -- Case 1: there exists a quiet time ≤ t_busy
        set last0 := @Nat.findGreatest (fun t => quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true) hDP t_busy with hlast0_def
        obtain ⟨t_qt, htb, hq⟩ := hEX
        have hPRED : quiet_time_dec job_cost arr_seq sched higher_eq_priority j last0 = true :=
          @Nat.findGreatest_spec t_qt (fun t => quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true) hDP t_busy
            htb ((quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j t_qt).mpr hq)
        have hQUIET_t1 : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j last0 :=
          (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j last0).mp hPRED
        have hlast0_le : last0 ≤ t_busy := @Nat.findGreatest_le _ hDP t_busy
        have hGE1 : last0 ≤ job_arrival j := by
          by_contra hBEFORE
          push_neg at hBEFORE
          have hHP := H_priority_is_reflexive j
          have hCOMP := hQUIET_t1 j H_from_arrival_sequence hHP hBEFORE
          have hCOMP_busy := completion_monotonic job_cost sched j last0 t_busy hlast0_le hCOMP
          exact hPEND_notcomp hCOMP_busy
        have hNQT_prefix : ∀ t0, last0 < t0 ∧ t0 < t_busy + 1 → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t0 := by
          intro t0 ⟨hGT, hLTbusy⟩ hQ
          have ht0_le : t0 ≤ t_busy := Nat.lt_succ_iff.mp hLTbusy
          have hDEC : quiet_time_dec job_cost arr_seq sched higher_eq_priority j t0 = true :=
            (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j t0).mpr hQ
          exact @Nat.findGreatest_is_greatest t0 (fun t => quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true) hDP t_busy hGT ht0_le hDEC
        have hPrefix : busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j last0 (t_busy + 1) :=
          ⟨Nat.lt_succ_of_le hlast0_le, hQUIET_t1, hNQT_prefix, hGE1, Nat.lt_succ_of_le (le_refl _)⟩
        -- Step 3: Get a no_carry_in time from processor_is_not_too_busy (last0+1)
        obtain ⟨δ, hLE_δ, hQT_nc⟩ := processor_is_not_too_busy job_arrival job_cost arr_seq
          H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
          higher_eq_priority H_arrival_sequence_is_a_set H_work_conserving
          H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive
          Δ H_delta_positive H_workload_is_bounded (last0 + 1)
        -- Step 4: Convert no_carry_in to quiet_time
        have hQT : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (last0 + 1 + δ) :=
          no_carry_in_implies_quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (last0 + 1 + δ) hQT_nc
        -- Step 5: Find minimum quiet time t2 with last0 < t2 ≤ last0 + 1 + δ
        have hEX_dec : ∃ n, (last0 + 1 + n ≤ last0 + 1 + δ ∧
            quiet_time_dec job_cost arr_seq sched higher_eq_priority j (last0 + 1 + n) = true) := by
          exact ⟨δ, Nat.le_refl _, (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
            sched H_jobs_come_from_arrival_sequence higher_eq_priority j (last0 + 1 + δ)).mpr hQT⟩
        set n_min := Nat.find hEX_dec with hn_min_def
        have hn_spec := Nat.find_spec hEX_dec
        obtain ⟨hn_le, hn_dec⟩ := hn_spec
        set t2 := last0 + 1 + n_min
        have hn_quiet : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2 :=
          (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
            sched H_jobs_come_from_arrival_sequence higher_eq_priority j t2).mp hn_dec
        have hn_gt : last0 < t2 := by simp only [Time, t2] at *; omega
        -- Step 6: Show last0 ≤ job_arrival j < t2
        have hJA_lt_t2 : job_arrival j < t2 := by
          by_contra hCONTR
          push_neg at hCONTR
          -- t2 ≤ job_arrival j = t_busy, so t2 < t_busy + 1
          have hLT_busy : t2 < t_busy + 1 := by simp only [Time] at *; omega
          exact hNQT_prefix t2 ⟨hn_gt, hLT_busy⟩ hn_quiet
        -- Step 7: Show t2 ≤ last0 + Δ
        have hBound : t2 ≤ last0 + Δ := by simp only [Time, t2] at *; omega
        -- Step 8: Construct busy_interval
        refine ⟨last0, t2, hGE1, hJA_lt_t2, hBound, ?_⟩
        constructor
        · -- busy_interval_prefix
          refine ⟨hn_gt, hQUIET_t1, ?_, hGE1, hJA_lt_t2⟩
          intro t0 ⟨hGT0, hLT0⟩ hQT0
          have hk_lt : t0 - (last0 + 1) < n_min := by simp only [Time, t2] at *; omega
          have hNOT := Nat.find_min hEX_dec hk_lt
          apply hNOT
          constructor
          · simp only [Time] at *; omega
          · have : last0 + 1 + (t0 - (last0 + 1)) = t0 := by simp only [Time] at *; omega
            rw [this]
            exact (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
              sched H_jobs_come_from_arrival_sequence higher_eq_priority j t0).mpr hQT0
        · exact hn_quiet
      · -- Case 2: no quiet time in [0, t_busy]
        push_neg at hEX
        -- t1 = 0
        have hQUIET_0 : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j 0 := by
          intro jhp _ _ hAB
          exact absurd hAB (Nat.not_lt_zero _)
        have hNQT_0 : ∀ t0, 0 < t0 ∧ t0 < t_busy + 1 → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t0 := by
          intro t0 ⟨hGT, hLT⟩ hQ
          exact hEX t0 (Nat.lt_succ_iff.mp hLT) hQ
        have hPrefix : busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j 0 (t_busy + 1) :=
          ⟨Nat.succ_pos _, hQUIET_0, hNQT_0, Nat.zero_le _, Nat.lt_succ_of_le (le_refl _)⟩
        -- Get no_carry_in from processor_is_not_too_busy 1
        obtain ⟨δ, hLE_δ, hQT_nc⟩ := processor_is_not_too_busy job_arrival job_cost arr_seq
          H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
          higher_eq_priority H_arrival_sequence_is_a_set H_work_conserving
          H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute H_priority_is_reflexive
          Δ H_delta_positive H_workload_is_bounded 1
        have hQT : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (1 + δ) :=
          no_carry_in_implies_quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (1 + δ) hQT_nc
        have hEX_dec : ∃ n, (0 + 1 + n ≤ 0 + 1 + δ ∧
            quiet_time_dec job_cost arr_seq sched higher_eq_priority j (0 + 1 + n) = true) := by
          refine ⟨δ, Nat.le_refl _, ?_⟩
          simp only [Nat.zero_add]
          exact (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
            sched H_jobs_come_from_arrival_sequence higher_eq_priority j (1 + δ)).mpr hQT
        set n_min := Nat.find hEX_dec with hn_min_def
        have hn_spec := Nat.find_spec hEX_dec
        obtain ⟨hn_le, hn_dec⟩ := hn_spec
        set t2 := 0 + 1 + n_min
        have hn_quiet : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2 :=
          (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
            sched H_jobs_come_from_arrival_sequence higher_eq_priority j t2).mp hn_dec
        have hn_gt : 0 < t2 := by simp only [Time, t2] at *; omega
        have hJA_lt_t2 : job_arrival j < t2 := by
          by_contra hCONTR
          push_neg at hCONTR
          have hLT_busy : t2 < t_busy + 1 := by simp only [Time] at *; omega
          exact hNQT_0 t2 ⟨hn_gt, hLT_busy⟩ hn_quiet
        have hBound : t2 ≤ 0 + Δ := by simp only [Time, t2] at *; omega
        refine ⟨0, t2, Nat.zero_le _, hJA_lt_t2, by simp only [Time] at *; omega, ?_⟩
        constructor
        · refine ⟨hn_gt, hQUIET_0, ?_, Nat.zero_le _, hJA_lt_t2⟩
          intro t0 ⟨hGT0, hLT0⟩ hQT0
          have hk_lt : t0 - (0 + 1) < n_min := by simp only [Time, t2] at *; omega
          have hNOT := Nat.find_min hEX_dec hk_lt
          apply hNOT
          constructor
          · simp only [Time] at *; omega
          · have : 0 + 1 + (t0 - (0 + 1)) = t0 := by simp only [Time] at *; omega
            rw [this]
            exact (quiet_time_P job_arrival job_cost arr_seq H_arrival_times_are_consistent
              sched H_jobs_come_from_arrival_sequence higher_eq_priority j t0).mpr hQT0
        · exact hn_quiet

  end NonOverloadedProcessor

end Definitions

end BusyIntervalJLFP

end Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval
