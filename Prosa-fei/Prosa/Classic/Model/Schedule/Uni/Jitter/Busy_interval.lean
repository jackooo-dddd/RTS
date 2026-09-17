-- Translated from: ../rt-proofs/classic/model/schedule/uni/jitter/busy_interval.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
import Prosa.Classic.Model.Priority
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.Busy_interval

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Priority

namespace BusyInterval

section Defs

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_jitter : Job → Time)
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (sched : schedule Job)
variable (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
variable (higher_eq_priority : JLFP_policy Job)
variable (j : Job)
variable (H_from_arrival_sequence : arrives_in arr_seq j)

def quiet_time (t : Time) : Prop :=
  ∀ j_hp,
    arrives_in arr_seq j_hp →
    higher_eq_priority j_hp j = true →
    actual_arrival_before job_arrival job_jitter j_hp t →
    completed_by job_cost sched j_hp t

def busy_interval_prefix (t1 t_busy : Time) : Prop :=
  t1 < t_busy ∧
  quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 ∧
  (∀ t, t1 < t ∧ t < t_busy →
    ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t)

def busy_interval (t1 t2 : Time) : Prop :=
  busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 t2 ∧
  quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t2

section Lemmas

section BasicLemmas

variable (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
variable (t1 t2 : Time)
variable (H_busy_interval :
  busy_interval job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 t2)
variable (t : Time)
variable (H_during_interval : t1 ≤ t ∧ t < t2)
variable (H_job_is_pending :
  Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending
    job_arrival job_cost job_jitter sched j t)

section CompletesDuringBusyInterval

include H_from_arrival_sequence H_priority_is_reflexive H_busy_interval H_during_interval H_job_is_pending in
theorem job_completes_within_busy_interval :
    completed_by job_cost sched j t2 := by
  obtain ⟨⟨_, hQT, _⟩, hQT2⟩ := H_busy_interval
  exact hQT2 j H_from_arrival_sequence (H_priority_is_reflexive j)
    (by unfold actual_arrival_before
        have := H_job_is_pending.1
        simp only [jitter_has_passed] at this
        obtain ⟨_, hLT_t2⟩ := H_during_interval
        simp only [Time] at *; omega)

end CompletesDuringBusyInterval

section ArrivesDuringBusyInterval

variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

include H_from_arrival_sequence H_priority_is_reflexive H_busy_interval H_during_interval H_job_is_pending in
theorem job_arrives_within_busy_interval :
    t1 ≤ actual_arrival job_arrival job_jitter j := by
  by_contra h
  push_neg at h
  -- j's actual arrival is before t1, so by quiet_time at t1, j is completed at t1
  obtain ⟨⟨_, hQT, _⟩, _⟩ := H_busy_interval
  have hCOMP := hQT j H_from_arrival_sequence (H_priority_is_reflexive j) h
  -- If j is completed at t1, then by completion_monotonic, completed at t
  have hCOMP_t := completion_monotonic job_cost sched j t1 t
    H_during_interval.1 hCOMP
  -- But j is pending at t
  exact H_job_is_pending.2 hCOMP_t

end ArrivesDuringBusyInterval

end BasicLemmas

section ExistsPendingJob

variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
variable (t1 t2 : Time)
variable (H_interval : t1 ≤ t2)
variable (H_quiet :
  quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1)
variable (H_not_quiet :
  ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t2)

include H_arrival_times_are_consistent H_completed_jobs_dont_execute H_interval H_quiet H_not_quiet in
theorem not_quiet_implies_exists_pending_job :
    ∃ j_hp,
      arrives_in arr_seq j_hp ∧
      actual_arrival_between job_arrival job_jitter j_hp t1 t2 ∧
      higher_eq_priority j_hp j = true ∧
      ¬ completed_by job_cost sched j_hp t2 := by
  by_cases hHAS : ∃ j_hp ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2,
      ¬ completed_by job_cost sched j_hp t2 ∧ higher_eq_priority j_hp j = true
  · obtain ⟨j_hp, hMEM, hNCOMP, hHP⟩ := hHAS
    have hARR := in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq
      H_arrival_times_are_consistent j_hp t1 t2 hMEM
    have hBET := in_actual_arrivals_implies_arrived_between job_arrival job_jitter arr_seq
      H_arrival_times_are_consistent j_hp t1 t2 hMEM
    exact ⟨j_hp, hARR, hBET, hHP, hNCOMP⟩
  · push_neg at hHAS
    exfalso; apply H_not_quiet
    intro j_hp hIN hHP hBEF
    by_cases hBEFORE : actual_arrival_before job_arrival job_jitter j_hp t1
    · exact completion_monotonic job_cost sched j_hp t1 t2 H_interval
        (H_quiet j_hp hIN hHP hBEFORE)
    · simp only [actual_arrival_before, not_lt] at hBEFORE
      have hBET : actual_arrival_between job_arrival job_jitter j_hp t1 t2 :=
        ⟨hBEFORE, hBEF⟩
      have hMEM := arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq
        H_arrival_times_are_consistent j_hp t1 t2 hIN hBET
      by_contra hNCOMP
      exact absurd hHP (hHAS j_hp hMEM hNCOMP)

end ExistsPendingJob

section ProcessorAlwaysBusy

variable (H_work_conserving :
  work_conserving job_arrival job_cost job_jitter arr_seq sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
variable (H_jobs_execute_after_jitter :
  jobs_execute_after_jitter job_arrival job_jitter sched)
variable (t1 t2 : Time)
variable (H_strictly_larger : t1 < t2)
variable (H_quiet :
  quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1)
variable (H_not_quiet :
  ∀ t, t1 < t ∧ t ≤ t2 →
    ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t)

include H_work_conserving H_not_quiet H_strictly_larger in
theorem not_quiet_implies_not_idle :
    ∀ t, t1 ≤ t ∧ t ≤ t2 → ¬ (is_idle sched t = true) := by
  intro t ⟨hGE, hLE⟩ hIDLE
  -- At t+1 we claim quiet_time (because idle at t means all pending jobs get stuck,
  -- but actually idle means nobody is scheduled, so all jobs that arrived before t+1
  -- and have hep must be completed — by completion at t from quiet at t1)
  have idle_implies_quiet : quiet_time job_arrival job_cost job_jitter arr_seq sched
      higher_eq_priority j (t + 1) := by
    intro jhp hARR hHP hAB
    by_contra hNCOMP
    -- jhp actual arrival < t+1, so actual_arrival jhp ≤ t, so jitter_has_passed at t
    have hJP : jitter_has_passed job_arrival job_jitter jhp t := by
      simp only [actual_arrival_before, actual_arrival] at hAB
      simp only [jitter_has_passed, actual_arrival]; simp only [Time] at *; omega
    have hNCOMP_t : ¬ completed_by job_cost sched jhp t := by
      intro hCOMP
      exact hNCOMP (completion_monotonic job_cost sched jhp t (t + 1)
        (by simp only [Time] at *; omega) hCOMP)
    have hPEND : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending
        job_arrival job_cost job_jitter sched jhp t := ⟨hJP, hNCOMP_t⟩
    have hNSCHED : ¬ (scheduled_at sched jhp t = true) := by
      simp only [is_idle, beq_iff_eq] at hIDLE
      simp only [scheduled_at, beq_iff_eq]; rw [hIDLE]; simp
    have hBACK : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
        job_arrival job_cost job_jitter sched jhp t := ⟨hPEND, hNSCHED⟩
    obtain ⟨jo, hSCHED⟩ := H_work_conserving jhp t hARR hBACK
    simp only [is_idle, beq_iff_eq] at hIDLE
    simp only [scheduled_at, beq_iff_eq] at hSCHED
    rw [hIDLE] at hSCHED; simp at hSCHED
  -- But t+1 ∈ (t1, t2] or t = t2
  by_cases hLT' : t + 1 ≤ t2
  · exact H_not_quiet (t + 1) ⟨by simp only [Time] at *; omega, hLT'⟩ idle_implies_quiet
  · -- t = t2: use ¬ quiet at t directly
    push_neg at hLT'
    have hNQ' : ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched
        higher_eq_priority j t :=
      H_not_quiet t ⟨by simp only [Time] at *; omega, by simp only [Time] at *; omega⟩
    have ⟨jhp', h1'⟩ := Classical.not_forall.mp hNQ'
    have ⟨hARR', h2'⟩ := Classical.not_imp.mp h1'
    have ⟨hHP', h3'⟩ := Classical.not_imp.mp h2'
    have ⟨hAB', hNCOMP'⟩ := Classical.not_imp.mp h3'
    have hJP' : jitter_has_passed job_arrival job_jitter jhp' t := by
      simp only [actual_arrival_before, actual_arrival, jitter_has_passed] at hAB' ⊢
      simp only [Time] at *; omega
    have hNSCHED' : ¬ (scheduled_at sched jhp' t = true) := by
      simp only [is_idle, beq_iff_eq] at hIDLE
      simp only [scheduled_at, beq_iff_eq]; rw [hIDLE]; simp
    have hBACK' : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
        job_arrival job_cost job_jitter sched jhp' t :=
      ⟨⟨hJP', hNCOMP'⟩, hNSCHED'⟩
    obtain ⟨jo', hSCHED'⟩ := H_work_conserving jhp' t hARR' hBACK'
    simp only [is_idle, beq_iff_eq] at hIDLE
    simp only [scheduled_at, beq_iff_eq] at hSCHED'
    rw [hIDLE] at hSCHED'; simp at hSCHED'

section OnlyHigherOrEqualPriority

variable (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority)
variable (H_respects_policy :
  respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_work_conserving H_completed_jobs_dont_execute H_jobs_execute_after_jitter H_quiet H_not_quiet H_respects_policy H_priority_is_transitive in
theorem not_quiet_implies_exists_scheduled_hp_job :
    ∀ t, t1 ≤ t ∧ t < t2 →
      ∃ j_hp,
        actual_arrival_between job_arrival job_jitter j_hp t1 t2 ∧
        higher_eq_priority j_hp j = true ∧
        scheduled_at sched j_hp t = true := by
  intro t ⟨hGE, hLT⟩
  -- t+1 ∈ (t1, t2], so not quiet at t+1
  have hNQ : ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched
      higher_eq_priority j (t + 1) :=
    H_not_quiet (t + 1) ⟨by simp only [Time] at *; omega, by simp only [Time] at *; omega⟩
  -- Get pending hep job from [t1, t+1)
  obtain ⟨j_hp, hARR, hBET, hHP, hNCOMP⟩ := not_quiet_implies_exists_pending_job
    job_arrival job_cost job_jitter arr_seq H_arrival_times_are_consistent sched
    higher_eq_priority j H_completed_jobs_dont_execute t1 (t + 1)
    (by simp only [Time] at *; omega) H_quiet hNQ
  -- j_hp has jitter_has_passed at t
  have hJP : jitter_has_passed job_arrival job_jitter j_hp t := by
    simp only [actual_arrival_between, actual_arrival, jitter_has_passed] at hBET ⊢
    simp only [Time] at *; omega
  -- j_hp not completed at t
  have hNCOMP_t : ¬ completed_by job_cost sched j_hp t :=
    fun hC => hNCOMP (completion_monotonic job_cost sched j_hp t (t + 1)
      (by simp only [Time] at *; omega) hC)
  -- Case split: j_hp scheduled or not
  by_cases hS : scheduled_at sched j_hp t = true
  · -- j_hp is scheduled
    have hBET2 : actual_arrival_between job_arrival job_jitter j_hp t1 t2 :=
      ⟨hBET.1, by have := hBET.2; simp only [Time] at *; omega⟩
    exact ⟨j_hp, hBET2, hHP, hS⟩
  · -- j_hp is backlogged
    have hBACK : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
        job_arrival job_cost job_jitter sched j_hp t := ⟨⟨hJP, hNCOMP_t⟩, hS⟩
    -- work_conserving gives some scheduled job
    obtain ⟨j', hS'⟩ := H_work_conserving j_hp t hARR hBACK
    -- respects_policy: hep j' j_hp
    have hHP' := H_respects_policy j_hp j' t hARR hBACK hS'
    -- transitivity: hep j' j
    have hHP_j := H_priority_is_transitive j_hp j' j hHP' hHP
    -- j' from arrival sequence
    have hARR' := H_jobs_come_from_arrival_sequence j' t hS'
    -- j' has jitter_has_passed at t
    have hJP' := H_jobs_execute_after_jitter j' t hS'
    -- actual_arrival j' < t2
    have hAA_lt : actual_arrival job_arrival job_jitter j' < t2 := by
      simp only [jitter_has_passed, actual_arrival] at hJP'
      simp only [actual_arrival]; simp only [Time] at *; omega
    -- actual_arrival j' ≥ t1 (by contradiction: if < t1, completed by quiet, contradicts scheduled)
    have hAA_ge : t1 ≤ actual_arrival job_arrival job_jitter j' := by
      by_contra h; push_neg at h
      have hCOMP := H_quiet j' hARR' hHP_j h
      have hCOMP_t := completion_monotonic job_cost sched j' t1 t hGE hCOMP
      exact absurd hS' (completed_implies_not_scheduled job_cost sched j'
        H_completed_jobs_dont_execute t hCOMP_t)
    exact ⟨j', ⟨hAA_ge, hAA_lt⟩, hHP_j, hS'⟩

end OnlyHigherOrEqualPriority

end ProcessorAlwaysBusy

section BoundingBusyInterval

variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
variable (H_jobs_execute_after_jitter :
  jobs_execute_after_jitter job_arrival job_jitter sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
variable (H_work_conserving :
  work_conserving job_arrival job_cost job_jitter arr_seq sched)
variable (H_respects_policy :
  respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority)
variable (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority)

section BoundingBusyInterval2

variable (t_busy : Time)
variable (H_j_is_pending :
  Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending
    job_arrival job_cost job_jitter sched j t_busy)

section LowerBound

include H_from_arrival_sequence H_priority_is_reflexive H_j_is_pending in
theorem exists_busy_interval_prefix :
    ∃ t1,
      busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched
        higher_eq_priority j t1 (t_busy + 1) ∧
      t1 ≤ actual_arrival job_arrival job_jitter j ∧
      actual_arrival job_arrival job_jitter j ≤ t_busy := by
  -- quiet_time at 0 holds vacuously (no actual_arrival < 0)
  have hQ0 : quiet_time job_arrival job_cost job_jitter arr_seq sched
      higher_eq_priority j 0 := by
    intro j_hp _ _ hAB
    unfold actual_arrival_before at hAB
    exact absurd hAB (not_lt.mpr (Nat.zero_le _))
  -- Use classical decidability + Nat.findGreatest
  haveI : DecidablePred (fun t => quiet_time job_arrival job_cost job_jitter arr_seq sched
      higher_eq_priority j t) := fun t => Classical.dec _
  set tl := Nat.findGreatest (fun t => quiet_time job_arrival job_cost job_jitter arr_seq sched
      higher_eq_priority j t) t_busy with htl_def
  have htl_le : tl ≤ t_busy := Nat.findGreatest_le t_busy
  have hQUIET_tl : quiet_time job_arrival job_cost job_jitter arr_seq sched
      higher_eq_priority j tl := Nat.findGreatest_spec (Nat.zero_le t_busy) hQ0
  -- actual_arrival j ≤ t_busy (from jitter_has_passed)
  have hAA_le : actual_arrival job_arrival job_jitter j ≤ t_busy := by
    have := H_j_is_pending.1
    simp only [jitter_has_passed, actual_arrival] at this ⊢; exact this
  -- tl ≤ actual_arrival j
  have hAA_ge : tl ≤ actual_arrival job_arrival job_jitter j := by
    by_contra h; push_neg at h
    have hCOMP := hQUIET_tl j H_from_arrival_sequence (H_priority_is_reflexive j) h
    exact H_j_is_pending.2 (completion_monotonic job_cost sched j tl t_busy htl_le hCOMP)
  -- tl < t_busy + 1
  have hLT : tl < t_busy + 1 := Nat.lt_succ_of_le htl_le
  -- No quiet time in (tl, t_busy+1)
  have hNQT : ∀ t0, tl < t0 ∧ t0 < t_busy + 1 →
      ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t0 := by
    intro t0 ⟨hGT, hLTbusy⟩ hQ
    have ht0_le : t0 ≤ t_busy := by simp only [Time] at *; omega
    exact absurd hQ (Nat.findGreatest_is_greatest hGT ht0_le)
  exact ⟨tl, ⟨hLT, hQUIET_tl, hNQT⟩, hAA_ge, hAA_le⟩

end LowerBound

section UpperBound

variable (t1 : Time)
variable (H_is_busy_prefix :
  busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched
    higher_eq_priority j t1 (t_busy + 1))
variable (H_busy_prefix_contains_arrival :
  actual_arrival job_arrival job_jitter j ≥ t1)
variable (delta : Time)
variable (H_delta_positive : delta > 0)
variable (H_workload_is_bounded :
  workload_of_higher_or_equal_priority_jobs job_cost
    (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
    higher_eq_priority j ≤ delta)

section CannotBeBusyForSoLong

variable (H_no_quiet_time :
  ∀ t, t1 < t ∧ t ≤ t1 + delta →
    ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched
      higher_eq_priority j t)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence job_cost H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving H_respects_policy H_priority_is_reflexive H_priority_is_transitive t_busy H_j_is_pending H_is_busy_prefix H_no_quiet_time H_delta_positive

theorem busy_interval_has_uninterrupted_service :
    service_of_higher_or_equal_priority_jobs sched
      (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
      higher_eq_priority j t1 (t1 + delta) = delta := by
  apply le_antisymm
  · -- ≤ delta: service bounded by interval length
    simp only [service_of_higher_or_equal_priority_jobs]
    have h_nodup := actual_arrivals_uniq job_arrival job_jitter arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set t1 (t1 + delta)
    calc service_of_jobs sched
          (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
          (fun j_hp => higher_eq_priority j_hp j) t1 (t1 + delta)
        ≤ (t1 + delta) - t1 :=
          service_of_jobs_le_delta job_cost sched
            (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
            (fun j_hp => higher_eq_priority j_hp j) H_completed_jobs_dont_execute
            h_nodup t1 (t1 + delta)
      _ = delta := by simp only [Time] at *; omega
  · -- ≥ delta: at each time step, a scheduled hep job contributes 1
    simp only [service_of_higher_or_equal_priority_jobs, service_of_jobs, service_during]
    set l := actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta)
    set P := fun j_hp : Job => higher_eq_priority j_hp j
    -- Swap sums
    have h_swap : ((l.filter P).map (fun j' =>
        ∑ t' ∈ Finset.Ico t1 (t1 + delta), service_at sched j' t')).sum =
        ∑ t' ∈ Finset.Ico t1 (t1 + delta),
          ((l.filter P).map (fun j' => service_at sched j' t')).sum := by
      induction (l.filter P) with
      | nil => simp
      | cons a l' ih =>
        simp only [List.map_cons, List.sum_cons]; rw [ih, ← Finset.sum_add_distrib]
    rw [h_swap]
    -- At each time step, sum ≥ 1
    calc delta = ∑ _t' ∈ Finset.Ico t1 (t1 + delta), 1 := by
          simp [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
       _ ≤ ∑ t' ∈ Finset.Ico t1 (t1 + delta),
            ((l.filter P).map (fun j' => service_at sched j' t')).sum := by
          apply Finset.sum_le_sum
          intro t' ht'
          rw [Finset.mem_Ico] at ht'
          obtain ⟨ht'_ge, ht'_lt⟩ := ht'
          -- Find scheduled hep job at t'
          have hNI : ¬ (is_idle sched t' = true) := by
            intro hIDLE'
            -- Build quiet_time at t'+1 from idle at t'
            have idle_quiet : quiet_time job_arrival job_cost job_jitter arr_seq sched
                higher_eq_priority j (t' + 1) := by
              intro jhp hARR hHP hAB
              by_contra hNCOMP
              have hJP' : jitter_has_passed job_arrival job_jitter jhp t' := by
                simp only [actual_arrival_before, actual_arrival] at hAB
                simp only [jitter_has_passed, actual_arrival]; simp only [Time] at *
                exact Nat.le_of_lt_succ (by assumption)
              have hNCOMP_t' : ¬ completed_by job_cost sched jhp t' := fun hC =>
                hNCOMP (completion_monotonic job_cost sched jhp t' (t' + 1) (Nat.le_succ t') hC)
              have hNSCHED' : ¬ (scheduled_at sched jhp t' = true) := by
                simp only [is_idle, beq_iff_eq] at hIDLE'
                simp only [scheduled_at, beq_iff_eq]; rw [hIDLE']; simp
              have hBACK' : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
                  job_arrival job_cost job_jitter sched jhp t' :=
                ⟨⟨hJP', hNCOMP_t'⟩, hNSCHED'⟩
              obtain ⟨jo', hSCHED'⟩ := H_work_conserving jhp t' hARR hBACK'
              simp only [is_idle, beq_iff_eq] at hIDLE'
              simp only [scheduled_at, beq_iff_eq] at hSCHED'
              rw [hIDLE'] at hSCHED'; simp at hSCHED'
            exact H_no_quiet_time (t' + 1) ⟨Nat.lt_succ_of_le ht'_ge, ht'_lt⟩ idle_quiet
          obtain ⟨j1, hj1⟩ : ∃ j1, sched t' = some j1 := by
            simp only [is_idle, beq_iff_eq] at hNI; push_neg at hNI
            cases h : sched t' with
            | none => exact absurd h hNI
            | some j1 => exact ⟨j1, rfl⟩
          have hSCHED : scheduled_at sched j1 t' = true := by simp [scheduled_at, hj1]
          -- j1 is hep and in l
          have hARR_j1 := H_jobs_come_from_arrival_sequence j1 t' hSCHED
          have hJP_j1 := H_jobs_execute_after_jitter j1 t' hSCHED
          -- actual_arrival j1 < t1 + delta
          have hAA_lt : actual_arrival job_arrival job_jitter j1 < t1 + delta := by
            simp only [jitter_has_passed, actual_arrival] at hJP_j1
            simp only [actual_arrival]; simp only [Time] at *
            exact lt_of_le_of_lt (by assumption) ht'_lt
          -- actual_arrival j1 ≥ t1
          have hAA_ge : t1 ≤ actual_arrival job_arrival job_jitter j1 := by
            by_contra h; push_neg at h
            have hCOMP := H_is_busy_prefix.2.1 j1 hARR_j1
              (by -- need hep j1 j: use work_conserving + respects_policy
                  -- At t', not quiet at t'+1 (H_no_quiet_time gives it if t'+1 ≤ t1+delta)
                  by_contra hNHP
                  simp only [Bool.not_eq_true] at hNHP
                  -- j1 is scheduled but not hep to j, yet there must be a backlogged hep job
                  -- From not quiet at some time in (t1, t1+delta], get pending hep job
                  have hNQ : ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched
                      higher_eq_priority j (t' + 1) :=
                    H_no_quiet_time (t' + 1) ⟨Nat.lt_succ_of_le ht'_ge, ht'_lt⟩
                  -- get pending hep job via contradiction with quiet_time
                  exfalso
                  have hNQ_t1 : ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched
                      higher_eq_priority j (t' + 1) :=
                    H_no_quiet_time (t' + 1) ⟨Nat.lt_succ_of_le ht'_ge, ht'_lt⟩
                  apply hNQ_t1
                  -- show quiet at t'+1: all hep jobs with actual_arrival < t'+1 completed
                  intro jhp hARR2 hHP2 hAB2
                  -- actual_arrival jhp < t'+1 ≤ t1+delta, and we need completed at t'+1
                  by_cases hBEFORE : actual_arrival_before job_arrival job_jitter jhp t1
                  · exact completion_monotonic job_cost sched jhp t1 (t' + 1)
                      (Nat.le_succ_of_le ht'_ge) (H_is_busy_prefix.2.1 jhp hARR2 hHP2 hBEFORE)
                  · -- actual_arrival jhp ≥ t1, so jhp ∈ actual_arrivals_between
                    simp only [actual_arrival_before, not_lt] at hBEFORE
                    -- jhp completed: if not, j1 not hep gives contradiction
                    by_contra h2NCOMP
                    -- jhp pending at t'
                    have hJPhp : jitter_has_passed job_arrival job_jitter jhp t' := by
                      simp only [actual_arrival_before, actual_arrival, jitter_has_passed] at hAB2 ⊢
                      simp only [Time] at *; exact Nat.le_of_lt_succ (by assumption)
                    have hNCOMP_tp : ¬ completed_by job_cost sched jhp t' := fun hC =>
                      h2NCOMP (completion_monotonic job_cost sched jhp t' (t' + 1) (Nat.le_succ t') hC)
                    have hBACK_jhp : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
                        job_arrival job_cost job_jitter sched jhp t' := by
                      constructor
                      · exact ⟨hJPhp, hNCOMP_tp⟩
                      · intro hS'
                        simp only [scheduled_at, beq_iff_eq] at hS' hSCHED
                        rw [hSCHED] at hS'; injection hS' with hEQ; subst hEQ
                        simp [hHP2] at hNHP
                    have hRP2 := H_respects_policy jhp j1 t' hARR2 hBACK_jhp hSCHED
                    exact absurd (H_priority_is_transitive jhp j1 j hRP2 hHP2) (by simp [hNHP])) h
            exact absurd hSCHED (completed_implies_not_scheduled job_cost sched j1
              H_completed_jobs_dont_execute t' (completion_monotonic job_cost sched j1 t1 t' ht'_ge hCOMP))
          -- j1 ∈ l
          have hBET : actual_arrival_between job_arrival job_jitter j1 t1 (t1 + delta) :=
            ⟨hAA_ge, hAA_lt⟩
          have hIN : j1 ∈ l :=
            arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq
              H_arrival_times_are_consistent j1 t1 (t1 + delta) hARR_j1 hBET
          -- j1 is hep (from the argument above, we showed it or got contradiction)
          have hHEP_j1 : higher_eq_priority j1 j = true := by
            by_contra hNHP
            simp only [Bool.not_eq_true] at hNHP
            -- Same argument as above but simplified
            have hNQ : ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched
                higher_eq_priority j (t' + 1) :=
              H_no_quiet_time (t' + 1) ⟨Nat.lt_succ_of_le ht'_ge, ht'_lt⟩
            -- same argument: get contradiction from not quiet at t'+1
            exfalso
            apply hNQ
            intro jhp2 hARR2 hHP2 hAB2
            by_cases hBEF2 : actual_arrival_before job_arrival job_jitter jhp2 t1
            · exact completion_monotonic job_cost sched jhp2 t1 (t' + 1)
                (Nat.le_succ_of_le ht'_ge) (H_is_busy_prefix.2.1 jhp2 hARR2 hHP2 hBEF2)
            · simp only [actual_arrival_before, not_lt] at hBEF2
              by_contra h2NC
              have hJP2 : jitter_has_passed job_arrival job_jitter jhp2 t' := by
                simp only [actual_arrival_before, actual_arrival, jitter_has_passed] at hAB2 ⊢
                simp only [Time] at *; exact Nat.le_of_lt_succ (by assumption)
              have hNC2 : ¬ completed_by job_cost sched jhp2 t' := fun hC =>
                h2NC (completion_monotonic job_cost sched jhp2 t' (t' + 1) (Nat.le_succ t') hC)
              have hBACK2 : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
                  job_arrival job_cost job_jitter sched jhp2 t' := by
                constructor
                · exact ⟨hJP2, hNC2⟩
                · intro hS2
                  simp only [scheduled_at, beq_iff_eq] at hS2 hSCHED
                  rw [hSCHED] at hS2; injection hS2 with hEQ; subst hEQ
                  simp [hHP2] at hNHP
              exact absurd (H_priority_is_transitive jhp2 j1 j
                (H_respects_policy jhp2 j1 t' hARR2 hBACK2 hSCHED) hHP2) (by simp [hNHP])
          have hIN_f : j1 ∈ l.filter P := by
            rw [List.mem_filter]; exact ⟨hIN, hHEP_j1⟩
          have hSA : service_at sched j1 t' = 1 := by
            simp only [service_at, scheduled_at, hj1]; simp [Bool.toNat]
          exact le_trans (le_of_eq hSA.symm)
            (List.le_sum_of_mem (List.mem_map.mpr ⟨j1, hIN_f, rfl⟩))

theorem busy_interval_too_much_workload :
    workload_of_higher_or_equal_priority_jobs job_cost
      (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
      higher_eq_priority j >
    service_of_higher_or_equal_priority_jobs sched
      (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
      higher_eq_priority j t1 (t1 + delta) := by
  obtain ⟨_, hQT, _⟩ := H_is_busy_prefix
  -- t1 + delta is not quiet
  have hNQ : ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched
      higher_eq_priority j (t1 + delta) :=
    H_no_quiet_time (t1 + delta) ⟨Nat.lt_add_of_pos_right H_delta_positive, le_refl _⟩
  -- Get pending hep job j0 in [t1, t1+delta)
  -- Inline: extract pending hep job from ¬ quiet
  have hNQ_unf := hNQ
  simp only [quiet_time] at hNQ_unf
  push_neg at hNQ_unf
  obtain ⟨j0, hARR0, hHP0, hAB0, hNCOMP0⟩ := hNQ_unf
  -- j0 has actual_arrival_before t1+delta, hep, not completed at t1+delta
  have hBTW0 : actual_arrival_between job_arrival job_jitter j0 t1 (t1 + delta) := by
    constructor
    · by_contra hLT; push_neg at hLT
      exact hNCOMP0 (completion_monotonic job_cost sched j0 t1 (t1 + delta) (Nat.le_add_right t1 delta)
        (hQT j0 hARR0 hHP0 hLT))
    · exact hAB0
  set l := actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta) with hl_def
  have hIN0 : j0 ∈ l :=
    arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq
      H_arrival_times_are_consistent j0 t1 (t1 + delta) hARR0 hBTW0
  -- For all hep jobs: service ≤ cost
  have hSLE : ∀ j', j' ∈ l → higher_eq_priority j' j = true →
      service_during sched j' t1 (t1 + delta) ≤ job_cost j' :=
    fun j' _ _ => cumulative_service_le_job_cost job_cost sched j'
      H_completed_jobs_dont_execute t1 (t1 + delta)
  -- For j0: service < cost (not completed)
  have hSLT0 : service_during sched j0 t1 (t1 + delta) < job_cost j0 := by
    by_contra h
    push_neg at h
    have hcat := service_during_cat sched j0 t1 0 (t1 + delta) ⟨Nat.zero_le _, Nat.le_add_right t1 delta⟩
    have hge : job_cost j0 ≤ service_during sched j0 0 (t1 + delta) := by rw [hcat]; exact h.trans (Nat.le_add_left _ _)
    exact hNCOMP0 hge
  -- service ≤ workload (by leq_sum_seq)
  have hLE := Prosa.Util.Sum.leq_sum_seq l
    (fun j_hp => higher_eq_priority j_hp j)
    (fun j' => service_during sched j' t1 (t1 + delta))
    (fun j' => job_cost j') hSLE
  -- workload ≠ service (because j0 has strict inequality)
  have hNE : workload_of_higher_or_equal_priority_jobs job_cost l higher_eq_priority j ≠
      service_of_higher_or_equal_priority_jobs sched l higher_eq_priority j t1 (t1 + delta) := by
    intro hEQ
    have hEQ_j0 := Prosa.Util.Sum.sum_majorant_eqn l
      (fun j' => service_during sched j' t1 (t1 + delta))
      (fun j' => job_cost j')
      (fun j_hp => higher_eq_priority j_hp j) hSLE
      (by unfold workload_of_higher_or_equal_priority_jobs workload_of_jobs
            service_of_higher_or_equal_priority_jobs service_of_jobs at hEQ
          exact hEQ.symm) j0 hIN0 hHP0
    dsimp at hEQ_j0; omega
  -- Combine
  unfold workload_of_higher_or_equal_priority_jobs workload_of_jobs at hNE ⊢
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs at hNE ⊢
  exact Nat.lt_of_le_of_ne hLE (Ne.symm hNE)

theorem busy_interval_workload_larger_than_interval :
    workload_of_higher_or_equal_priority_jobs job_cost
      (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
      higher_eq_priority j > delta := by
  calc workload_of_higher_or_equal_priority_jobs job_cost
        (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
        higher_eq_priority j >
      service_of_higher_or_equal_priority_jobs sched
        (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
        higher_eq_priority j t1 (t1 + delta) := by
        apply busy_interval_too_much_workload <;> assumption
    _ = delta := by
        apply busy_interval_has_uninterrupted_service <;> assumption

end CannotBeBusyForSoLong

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence job_cost H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving H_respects_policy H_priority_is_reflexive H_priority_is_transitive t_busy H_j_is_pending H_is_busy_prefix H_delta_positive H_workload_is_bounded in
theorem busy_interval_is_bounded :
    ∃ t2,
      t2 ≤ t1 + delta ∧
      busy_interval job_arrival job_cost job_jitter arr_seq sched
        higher_eq_priority j t1 t2 := by
  by_cases hEX : ∃ t2, t1 < t2 ∧ t2 ≤ t1 + delta ∧
      quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t2
  · -- Case 1: find minimum quiet time in (t1, t1+delta]
    obtain ⟨t2_ex, ht2_gt, ht2_le, ht2_quiet⟩ := hEX
    haveI : ∀ t, Decidable (quiet_time job_arrival job_cost job_jitter arr_seq sched
        higher_eq_priority j (t1 + 1 + t)) := fun t => Classical.dec _
    let QT' : ℕ → Prop := fun n => t1 + 1 + n ≤ t1 + delta ∧
        quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j (t1 + 1 + n)
    haveI : DecidablePred QT' := fun (n : ℕ) => Classical.dec (QT' n)
    have hEX_nat : ∃ n, QT' n := by
      refine ⟨t2_ex - (t1 + 1), ?_⟩
      constructor
      · simp only [Time] at *; omega
      · rw [show t1 + 1 + (t2_ex - (t1 + 1)) = t2_ex from by simp only [Time] at *; omega]
        exact ht2_quiet
    set n_min := Nat.find hEX_nat with hn_min_def
    have hn_spec := Nat.find_spec hEX_nat
    obtain ⟨hn_le, hn_quiet⟩ := hn_spec
    set t2_min := t1 + 1 + n_min
    have hn_gt : t1 < t2_min := by simp only [Time, t2_min] at *; omega
    refine ⟨t2_min, hn_le, ?_⟩
    constructor
    · -- busy_interval_prefix
      obtain ⟨_, hQT1, hNQT1⟩ := H_is_busy_prefix
      refine ⟨hn_gt, hQT1, ?_⟩
      intro t0 ⟨hGT0, hLT0⟩ hQT0
      have hk_lt : t0 - (t1 + 1) < n_min := by simp only [Time, t2_min] at *; omega
      have hNOT := Nat.find_min hEX_nat hk_lt
      apply hNOT
      constructor
      · simp only [Time] at *; omega
      · rw [show t1 + 1 + (t0 - (t1 + 1)) = t0 from by simp only [Time] at *; omega]
        exact hQT0
    · exact hn_quiet
  · -- Case 2: no quiet time in (t1, t1+delta] → contradiction
    push_neg at hEX
    exfalso
    have hALL : ∀ t, t1 < t ∧ t ≤ t1 + delta →
        ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t :=
      fun t ⟨hGT, hLE⟩ hQT => hEX t hGT hLE hQT
    have hTOOMUCH : workload_of_higher_or_equal_priority_jobs job_cost
        (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
        higher_eq_priority j > delta := by
      apply busy_interval_workload_larger_than_interval
      all_goals first | exact hALL | assumption
    exact absurd H_workload_is_bounded (not_le.mpr hTOOMUCH)

end UpperBound

end BoundingBusyInterval2

section BusyIntervalFromWorkloadBound

variable (delta : Time)
variable (H_delta_positive : delta > 0)
variable (H_workload_is_bounded :
  ∀ t, workload_of_higher_or_equal_priority_jobs job_cost
    (actual_arrivals_between job_arrival job_jitter arr_seq t (t + delta))
    higher_eq_priority j ≤ delta)
variable (H_positive_cost : job_cost j > 0)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving H_respects_policy H_priority_is_reflexive H_priority_is_transitive H_positive_cost H_delta_positive H_workload_is_bounded in
theorem exists_busy_interval :
    ∃ t1 t2,
      t1 ≤ actual_arrival job_arrival job_jitter j ∧
      actual_arrival job_arrival job_jitter j < t2 ∧
      t2 ≤ t1 + delta ∧
      busy_interval job_arrival job_cost job_jitter arr_seq sched
        higher_eq_priority j t1 t2 := by
  -- j is pending at actual_arrival j (jitter_has_passed and positive cost)
  have hJP : jitter_has_passed job_arrival job_jitter j (actual_arrival job_arrival job_jitter j) := by
    simp only [jitter_has_passed, actual_arrival]; exact le_refl _
  have hNCOMP : ¬ completed_by job_cost sched j (actual_arrival job_arrival job_jitter j) := by
    intro hCOMP
    have hZERO := cumulative_service_before_jitter_is_zero job_arrival job_jitter sched
      H_jobs_execute_after_jitter j 0 (actual_arrival job_arrival job_jitter j) (le_refl _)
    have hS0 : service sched j (actual_arrival job_arrival job_jitter j) = 0 := by
      show service_during sched j 0 (actual_arrival job_arrival job_jitter j) = 0
      exact hZERO
    simp only [completed_by] at hCOMP; rw [hS0] at hCOMP
    exact absurd hCOMP (not_le.mpr H_positive_cost)
  have hPEND : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending
      job_arrival job_cost job_jitter sched j (actual_arrival job_arrival job_jitter j) :=
    ⟨hJP, hNCOMP⟩
  -- Get a busy interval prefix
  let tb := actual_arrival job_arrival job_jitter j
  have hPEND' : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending
      job_arrival job_cost job_jitter sched j tb := hPEND
  obtain ⟨t1, hPrefix, hGE1, hGEarr⟩ :=
    exists_busy_interval_prefix
      (H_from_arrival_sequence := H_from_arrival_sequence)
      (H_priority_is_reflexive := H_priority_is_reflexive)
      (t_busy := tb) (H_j_is_pending := hPEND')
  -- Get bounded busy interval
  obtain ⟨t2, hGE2, hBUSYint⟩ :=
    busy_interval_is_bounded
      (H_arrival_times_are_consistent := H_arrival_times_are_consistent)
      (H_jobs_come_from_arrival_sequence := H_jobs_come_from_arrival_sequence)
      (H_from_arrival_sequence := H_from_arrival_sequence)
      (H_arrival_sequence_is_a_set := H_arrival_sequence_is_a_set)
      (H_jobs_execute_after_jitter := H_jobs_execute_after_jitter)
      (H_completed_jobs_dont_execute := H_completed_jobs_dont_execute)
      (H_work_conserving := H_work_conserving)
      (H_respects_policy := H_respects_policy)
      (H_priority_is_reflexive := H_priority_is_reflexive)
      (H_priority_is_transitive := H_priority_is_transitive)
      (t_busy := tb) (H_j_is_pending := hPEND')
      (t1 := t1) (H_is_busy_prefix := hPrefix)
      (delta := delta) (H_delta_positive := H_delta_positive)
      (H_workload_is_bounded := H_workload_is_bounded t1)
  refine ⟨t1, t2, hGE1, ?_, hGE2, hBUSYint⟩
  -- Need: actual_arrival j < t2
  by_contra hNLT
  push_neg at hNLT
  have hLT12 : t1 < t2 := hBUSYint.1.1
  have hQUIET := hBUSYint.2
  exact hPrefix.2.2 t2 ⟨hLT12, by simp only [Time] at *; omega⟩ hQUIET

end BusyIntervalFromWorkloadBound

section ResponseTimeBoundFromBusyInterval

variable (delta : Time)
variable (H_delta_positive : delta > 0)
variable (H_workload_is_bounded :
  ∀ t, workload_of_higher_or_equal_priority_jobs job_cost
    (actual_arrivals_between job_arrival job_jitter arr_seq t (t + delta))
    higher_eq_priority j ≤ delta)

include H_arrival_times_are_consistent H_jobs_come_from_arrival_sequence H_from_arrival_sequence H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving H_respects_policy H_priority_is_reflexive H_priority_is_transitive H_delta_positive H_workload_is_bounded in
theorem busy_interval_bounds_response_time :
    completed_by job_cost sched j
      (actual_arrival job_arrival job_jitter j + delta) := by
  -- Case split on whether job_cost is 0
  by_cases hCOST : job_cost j = 0
  · -- Trivially completed
    unfold completed_by; rw [hCOST]; exact Nat.zero_le _
  · -- job_cost j > 0
    push_neg at hCOST
    have hPos : job_cost j > 0 := Nat.pos_of_ne_zero hCOST
    -- j is pending at actual_arrival j
    have hJP : jitter_has_passed job_arrival job_jitter j
        (actual_arrival job_arrival job_jitter j) := by
      simp only [jitter_has_passed, actual_arrival]; exact le_refl _
    have hNCOMP : ¬ completed_by job_cost sched j
        (actual_arrival job_arrival job_jitter j) := by
      intro hCOMP
      have hZERO := cumulative_service_before_jitter_is_zero job_arrival job_jitter sched
        H_jobs_execute_after_jitter j 0 (actual_arrival job_arrival job_jitter j) (le_refl _)
      have hS0 : service sched j (actual_arrival job_arrival job_jitter j) = 0 := by
        show service_during sched j 0 (actual_arrival job_arrival job_jitter j) = 0
        exact hZERO
      simp only [completed_by] at hCOMP; rw [hS0] at hCOMP
      exact absurd hCOMP (not_le.mpr hPos)
    have hPEND : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending
        job_arrival job_cost job_jitter sched j
        (actual_arrival job_arrival job_jitter j) := ⟨hJP, hNCOMP⟩
    -- Get busy interval prefix
    let tb := actual_arrival job_arrival job_jitter j
    have hPEND' : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.pending
        job_arrival job_cost job_jitter sched j tb := hPEND
    obtain ⟨t1, hPrefix, hGE1, hGEarr⟩ :=
      exists_busy_interval_prefix
        (H_from_arrival_sequence := H_from_arrival_sequence)
        (H_priority_is_reflexive := H_priority_is_reflexive)
        (t_busy := tb) (H_j_is_pending := hPEND')
    -- Get bounded busy interval
    obtain ⟨t2, hGE2, hBUSYint⟩ :=
      busy_interval_is_bounded
        (H_arrival_times_are_consistent := H_arrival_times_are_consistent)
        (H_jobs_come_from_arrival_sequence := H_jobs_come_from_arrival_sequence)
        (H_from_arrival_sequence := H_from_arrival_sequence)
        (H_arrival_sequence_is_a_set := H_arrival_sequence_is_a_set)
        (H_jobs_execute_after_jitter := H_jobs_execute_after_jitter)
        (H_completed_jobs_dont_execute := H_completed_jobs_dont_execute)
        (H_work_conserving := H_work_conserving)
        (H_respects_policy := H_respects_policy)
        (H_priority_is_reflexive := H_priority_is_reflexive)
        (H_priority_is_transitive := H_priority_is_transitive)
        (t_busy := tb) (H_j_is_pending := hPEND')
        (t1 := t1) (H_is_busy_prefix := hPrefix)
        (delta := delta) (H_delta_positive := H_delta_positive)
        (H_workload_is_bounded := H_workload_is_bounded t1)
    -- j completes within the busy interval
    -- actual_arrival j < t2
    have hAA_lt_t2 : actual_arrival job_arrival job_jitter j < t2 := by
      by_contra hNLT; push_neg at hNLT
      exact hPrefix.2.2 t2 ⟨hBUSYint.1.1, by simp only [Time] at *; omega⟩ hBUSYint.2
    have hCOMPL : completed_by job_cost sched j t2 := by
      apply job_completes_within_busy_interval
      all_goals first | exact hBUSYint | exact ⟨hGE1, hAA_lt_t2⟩ | exact hPEND | assumption
    -- t2 ≤ t1 + delta ≤ actual_arrival j + delta
    exact completion_monotonic job_cost sched j t2
      (actual_arrival job_arrival job_jitter j + delta)
      (by simp only [Time] at *; omega) hCOMPL

end ResponseTimeBoundFromBusyInterval

end BoundingBusyInterval

end Lemmas

end Defs

end BusyInterval

end Prosa.Classic.Model.Schedule.Uni.Jitter.Busy_interval
