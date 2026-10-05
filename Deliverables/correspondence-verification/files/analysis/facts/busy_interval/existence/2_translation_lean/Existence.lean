-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/existence.v

import Prosa.Model.Job.Properties
import Prosa.Model.Schedule.WorkConserving
import Prosa.Analysis.Facts.Model.ServiceOfJobs
import Prosa.Analysis.Definitions.WorkBearingReadiness
import Prosa.Analysis.Facts.Priority.Inversion

namespace Prosa.Analysis.Facts.BusyInterval.Existence

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.WorkConserving
open Prosa.Model.Aggregate.ServiceOfJobs
open Prosa.Model.Aggregate.Workload
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.ServiceOfJobs
open Prosa.Analysis.Facts.Priority.Inversion
open Prosa.Util.Sum
open scoped BigOperators

/-! Existence of busy intervals for JLFP uniprocessor schedules.
Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order; instance inputs
quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `~ P` is `¬ P`;
`a < b <= c` and `a <= b < c` are Boolean conjunctions of decides;
`t.+1` is `t + 1`. -/

section ExistsBusyIntervalJLFP

variable {Job : JobType} [DecidableEq Job]

/-- A job completes by the end of its busy interval. -/
theorem job_completes_within_busy_interval [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : schedule PState)
    (JLFP : JLFP_policy Job) (j : Job) :
    arrives_in arr_seq j → reflexive_job_priorities JLFP →
    ∀ t1 t2 : instant, busy_interval arr_seq sched j t1 t2 → completed_by sched j t2 = true := by
  intro ha hrefl t1 t2 hbi
  obtain ⟨⟨_, _, _, harr⟩, hq⟩ := hbi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
  exact hq j ha (hrefl j) (decide_eq_true harr.2)

/-- Between a quiet and a non-quiet instant some higher-or-equal-priority job
arrived and is not yet complete. -/
theorem not_quiet_implies_exists_pending_job [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState) (JLFP : JLFP_policy Job) (j : Job)
      (t1 t2 : instant), t1 ≤ t2 → quiet_time arr_seq sched j t1 → ¬ quiet_time arr_seq sched j t2 →
      ∃ j_hp : Job, arrives_in arr_seq j_hp ∧ arrived_between j_hp t1 t2 = true ∧
        JLFP.hep_job j_hp j = true ∧ ¬ completed_by sched j_hp t2 = true := by
  intro _ PState sched JLFP j t1 t2 hle hq hnq
  by_contra hno
  apply hnq
  intro j_hp ha hhep hab
  by_contra hnc
  simp only [arrived_before, decide_eq_true_eq] at hab
  rcases Nat.lt_or_ge (job_arrival j_hp) t1 with hlt | hge
  · exact hnc (completion_monotonic sched j_hp t1 t2 hle (hq j_hp ha hhep (decide_eq_true hlt)))
  · exact hno ⟨j_hp, ha, by simp [arrived_between, hge, hab], hhep, hnc⟩

/-- An idle instant is followed by a quiet time. -/
theorem idle_time_implies_quiet_time_at_the_next_time_instant [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
    ∀ j : Job, work_conserving arr_seq sched →
    ∀ t : instant, is_idle arr_seq sched t = true → quiet_time arr_seq sched j (t + 1) := by
  intro hva PState sched hfrom hmust JLFP _ hwb j hwc t hidle j_hp ha hhep hab
  by_contra hnc
  simp only [arrived_before, decide_eq_true_eq] at hab
  have hpend : pending sched j_hp t = true := by
    unfold pending has_arrived
    have : completed_by sched j_hp t = false := by
      cases h : completed_by sched j_hp t
      · rfl
      · exact absurd (completion_monotonic sched j_hp t (t + 1) (Nat.le_succ t) h) hnc
    rw [this]
    simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
    omega'
  obtain ⟨j', ha', hr', _⟩ := hwb j_hp t ha hpend
  have hb : backlogged sched j' t = true := by
    unfold backlogged
    rw [hr', not_scheduled_when_idle arr_seq hva sched hfrom hmust j' t hidle]
    rfl
  obtain ⟨jo, hjo⟩ := hwc j' t ha' hb
  have := not_scheduled_when_idle arr_seq hva sched hfrom hmust jo t hidle
  rw [hjo] at this
  exact absurd this (by decide)

/-- If no higher-or-equal-priority job is pending at `t`, the instants `t`
and `t + 1` are quiet. -/
private theorem quiet_of_no_pending [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t : instant)
    (hno : ¬ ∃ jhp : Job, arrives_in arr_seq jhp ∧ pending sched jhp t = true ∧ hep_job jhp j = true) :
    ∀ s : instant, s ≤ t + 1 → t ≤ s → quiet_time arr_seq sched j s := by
  intro s hs1 hs2 j_hp ha hhep hab
  simp only [arrived_before, decide_eq_true_eq] at hab
  have hct : completed_by sched j_hp t = true := by
    by_contra hnc
    apply hno
    refine ⟨j_hp, ha, ?_, hhep⟩
    unfold pending has_arrived
    have : completed_by sched j_hp t = false := by simpa using hnc
    rw [this]
    simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
    omega'
  exact completion_monotonic sched j_hp t s hs2 hct

/-- Inside a busy-interval prefix some higher-or-equal-priority job is
pending at every instant. -/
theorem pending_hp_job_exists [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState), jobs_must_arrive_to_execute sched →
    ∀ (JLFP : JLFP_policy Job) (j : Job), arrives_in arr_seq j → job_cost_positive j = true →
      reflexive_job_priorities JLFP →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
      ∃ jhp : Job, arrives_in arr_seq jhp ∧ pending sched jhp t = true ∧ JLFP.hep_job jhp j = true := by
  intro _ PState sched hmust JLFP j ha hpos hrefl t1 t2 hbip t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨hlt12, _, hnq, harr⟩ := hbip
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
  by_contra hno
  have hq := quiet_of_no_pending arr_seq sched j t hno
  rcases Nat.lt_or_ge t1 t with hlt | hge
  · exact hnq t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') (hq t (by omega') le_rfl)
  · have ht1 : t = t1 := by omega'
    rcases Nat.lt_or_ge (t1 + 1) t2 with hlt2 | hge2
    · exact hnq (t1 + 1) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
        (hq (t1 + 1) (by omega') (by omega'))
    · have harrt : job_arrival j = t := by omega'
      apply hno
      refine ⟨j, ha, ?_, hrefl j⟩
      rw [← harrt]
      exact job_pending_at_arrival sched j (of_decide_eq_true hpos) hmust

/-- Inside a busy-interval prefix the processor is never idle. -/
theorem not_quiet_implies_not_idle [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true → work_conserving arr_seq sched →
      reflexive_job_priorities JLFP →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → ¬ is_idle arr_seq sched t = true := by
  intro hva PState sched hfrom hmust JLFP _ hwb j ha hpos hwc hrefl t1 t2 hbip t ht hidle
  obtain ⟨jhp, hahp, hpend, _⟩ :=
    pending_hp_job_exists arr_seq hva sched hmust JLFP j ha hpos hrefl t1 t2 hbip t ht
  obtain ⟨j', ha', hr', _⟩ := hwb jhp t hahp hpend
  have hb : backlogged sched j' t = true := by
    unfold backlogged
    rw [hr', not_scheduled_when_idle arr_seq hva sched hfrom hmust j' t hidle]
    rfl
  obtain ⟨jo, hjo⟩ := hwc j' t ha' hb
  have := not_scheduled_when_idle arr_seq hva sched hfrom hmust jo t hidle
  rw [hjo] at this
  exact absurd this (by decide)

/-- Filtered sums split over an appended list. -/
private theorem sumFiltered_append (l1 l2 : List Job) (P : Job → Bool) (F : Job → Nat) :
    sumFiltered (l1 ++ l2) P F = sumFiltered l1 P F + sumFiltered l2 P F := by
  unfold sumFiltered
  simp [List.filter_append, List.map_append, List.sum_append]

/-- Filtered sums vanish when every selected term vanishes. -/
private theorem sumFiltered_eq_zero (l : List Job) (P : Job → Bool) (F : Job → Nat)
    (h : ∀ x, x ∈ l → P x = true → F x = 0) : sumFiltered l P F = 0 := by
  unfold sumFiltered
  rw [List.sum_eq_zero_iff]
  intro n hn
  rw [List.mem_map] at hn
  obtain ⟨x, hx, rfl⟩ := hn
  rw [List.mem_filter] at hx
  exact h x hx.1 hx.2

/-- Higher-or-equal-priority jobs released before a quiet time receive no
service after it. -/
theorem hep_jobs_receive_no_service_before_quiet_time [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState), completed_jobs_dont_execute sched →
    ∀ (JLFP : JLFP_policy Job) (j : Job) (t1 : instant), quiet_time arr_seq sched j t1 →
    ∀ Δ : duration,
      service_of_higher_or_equal_priority_jobs sched (arrivals_between arr_seq t1 (t1 + Δ)) j t1 (t1 + Δ) =
        service_of_higher_or_equal_priority_jobs sched (arrivals_between arr_seq 0 (t1 + Δ)) j t1
          (t1 + Δ) := by
  intro hva PState sched hcomp JLFP j t1 hq Δ
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs
  rw [arrivals_between_cat arr_seq 0 t1 (t1 + Δ) (Nat.zero_le _) (Nat.le_add_right _ _),
    sumFiltered_append]
  have hz : sumFiltered (arrivals_between arr_seq 0 t1) (fun j_hp => hep_job j_hp j)
      (fun j' => service_during sched j' t1 (t1 + Δ)) = 0 := by
    apply sumFiltered_eq_zero
    intro x hx hhep
    have hin : decide (x ∈ arrivals_between arr_seq 0 t1) = true := decide_eq_true hx
    have hcx : completed_by sched x t1 = true :=
      hq x (in_arrivals_implies_arrived arr_seq x 0 t1 hin) hhep
        (in_arrivals_implies_arrived_before arr_seq hva.1 x t1 hin)
    unfold service_during
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_Ico] at ht
    apply not_scheduled_implies_no_service
    exact completed_implies_not_scheduled sched x hcomp t
      (completion_monotonic sched x t1 t ht.1 hcx)
  rw [hz, Nat.zero_add]

/-- A single selected term is bounded by the filtered sum. -/
private theorem le_sumFiltered (l : List Job) (P : Job → Bool) (F : Job → Nat) (x : Job)
    (hx : x ∈ l) (hP : P x = true) : F x ≤ sumFiltered l P F := by
  unfold sumFiltered
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
    (List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, hP⟩, rfl⟩)

/-- Within an interval without quiet times the total service equals its
length. -/
theorem no_idle_time_within_non_quiet_time_interval [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
    ∀ j : Job, work_conserving arr_seq sched → arrival_sequence_uniq arr_seq →
    ∀ (t1 : instant) (Δ : duration),
      (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + Δ)) = true → ¬ quiet_time arr_seq sched j t) →
      uniprocessor_model PState → unit_service_proc_model PState → ideal_progress_proc_model PState →
      total_service_of_jobs_in sched (arrivals_between arr_seq 0 (t1 + Δ)) t1 (t1 + Δ) = Δ := by
  intro hva PState sched hfrom hmust JLFP _ hwb j hwc _ t1 Δ hnq huni hunit hideal
  unfold total_service_of_jobs_in
  rw [service_of_jobs_sum_over_time_interval]
  conv_rhs => rw [← sum_of_ones t1 Δ]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  apply Nat.le_antisymm
  · exact service_of_jobs_le_1 hunit huni sched _ _ (arrivals_uniq arr_seq hva.1 hva.2 0 (t1 + Δ)) t
  · rcases scheduled_at_cases arr_seq hva sched hfrom hmust t with hidle | ⟨jo, hjo⟩
    · exfalso
      exact hnq (t + 1) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
        (idle_time_implies_quiet_time_at_the_next_time_instant arr_seq hva sched hfrom hmust JLFP hwb j
          hwc t hidle)
    · have harr : job_arrival jo ≤ t := of_decide_eq_true (hmust jo t hjo)
      have hin : jo ∈ arrivals_between arr_seq 0 (t1 + Δ) :=
        of_decide_eq_true (arrived_between_implies_in_arrivals arr_seq hva.1 jo 0 (t1 + Δ)
          (hfrom jo t hjo) (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega'))
      have hpos : 0 < service_at sched jo t := hideal jo (sched t) hjo
      unfold service_of_jobs_at
      exact Nat.le_trans hpos (le_sumFiltered _ (fun _ => true) (fun j' => service_at sched j' t) jo hin rfl)

/-- A pending job lies in a (possibly unbounded) busy-interval prefix that
starts no later than its arrival. -/
theorem exists_busy_interval_prefix [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState) (JLFP : JLFP_policy Job) (j : Job),
      arrives_in arr_seq j → reflexive_job_priorities JLFP →
    ∀ t_busy : instant, pending sched j t_busy = true →
      ∃ t1 : instant, busy_interval_prefix arr_seq sched j t1 (t_busy + 1) ∧
        (decide (t1 ≤ job_arrival j) && decide (job_arrival j ≤ t_busy)) = true := by
  intro _ PState sched JLFP j ha hrefl t_busy hpend
  classical
  have hq0 : quiet_time arr_seq sched j 0 := by
    intro j_hp _ _ hab
    simp [arrived_before] at hab
  let t1 := Nat.findGreatest (fun t => quiet_time arr_seq sched j t) t_busy
  have hq1 : quiet_time arr_seq sched j t1 := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hq0
  have hle : t1 ≤ t_busy := Nat.findGreatest_le t_busy
  have hgreat : ∀ t, t1 < t → t ≤ t_busy → ¬ quiet_time arr_seq sched j t :=
    fun t h1 h2 => Nat.findGreatest_is_greatest h1 h2
  unfold pending has_arrived at hpend
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hpend
  obtain ⟨harr, hnc⟩ := hpend
  have ht1arr : t1 ≤ job_arrival j := by
    by_contra hlt
    have hc := hq1 j ha (hrefl j) (decide_eq_true (by omega'))
    have := completion_monotonic sched j t1 t_busy hle hc
    rw [hnc] at this
    exact absurd this (by decide)
  refine ⟨t1, ⟨by omega', hq1, ?_, ?_⟩, ?_⟩
  · intro t ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact hgreat t ht.1 (by omega')
  · simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'
  · simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'

/-- Pointwise dominance with one strict term makes a filtered sum strictly
smaller. -/
private theorem sumFiltered_lt (l : List Job) (P : Job → Bool) (f g : Job → Nat)
    (hle : ∀ x, x ∈ l → P x = true → f x ≤ g x) (x0 : Job) (hx0 : x0 ∈ l) (hP0 : P x0 = true)
    (hlt : f x0 < g x0) : sumFiltered l P f < sumFiltered l P g := by
  unfold sumFiltered
  exact List.sum_lt_sum f g (fun i hi => hle i (List.mem_filter.1 hi).1 (List.mem_filter.1 hi).2)
    ⟨x0, List.mem_filter.2 ⟨hx0, hP0⟩, hlt⟩

/-- The non-higher-or-equal-priority service at an instant is bounded by the
priority-inversion indicator. -/
private theorem nonhep_service_le_priority_inversion [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (hva : valid_arrival_sequence arr_seq)
    {PState : ProcessorState Job} (sched : schedule PState)
    (hfrom : jobs_come_from_arrival_sequence sched arr_seq) (hmust : jobs_must_arrive_to_execute sched)
    (huni : uniprocessor_model PState) (hunit : unit_service_proc_model PState)
    (JLFP : JLFP_policy Job) (hrefl : reflexive_job_priorities JLFP) (j : Job) (jobs : List Job)
    (hnd : jobs.Nodup) (t : instant) :
    service_of_jobs_at sched (fun x => !JLFP.hep_job x j) jobs t ≤
      (priority_inversion arr_seq sched j t).toNat := by
  rcases scheduled_at_cases arr_seq hva sched hfrom hmust t with hidle | ⟨j', hj'⟩
  · rw [service_of_jobs_nsched_or_unsat sched _ jobs t (fun x _ => by
      have h := not_scheduled_when_idle arr_seq hva sched hfrom hmust x t hidle
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
      simp [h])]
    exact Nat.zero_le _
  · cases hhep : JLFP.hep_job j' j
    · -- a lower-priority job is scheduled: this is a priority inversion
      have hpi : priority_inversion arr_seq sched j t = true := by
        unfold priority_inversion
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
          List.any_eq_true]
        refine ⟨?_, ⟨j', ?_, by simp [hhep]⟩⟩
        · intro hin
          have hsj : scheduled_at sched j t = true := by
            rw [← scheduled_jobs_at_iff arr_seq hva sched hfrom hmust j t]; exact decide_eq_true hin
          have := huni j j' sched t hsj hj'
          subst this
          rw [hrefl] at hhep
          exact absurd hhep (by decide)
        · have := scheduled_jobs_at_iff arr_seq hva sched hfrom hmust j' t
          rw [hj'] at this
          exact of_decide_eq_true this
      rw [hpi]
      exact service_of_jobs_le_1 hunit huni sched _ jobs hnd t
    · rw [service_of_jobs_nsched_or_unsat sched _ jobs t (fun x _ => by
        cases hsx : scheduled_at sched x t
        · simp
        · have := huni x j' sched t hsx hj'
          rw [this, hhep]; rfl)]
      exact Nat.zero_le _

/-- Without a quiet time, the interval is filled by higher-or-equal-priority
service and priority inversion. -/
theorem busy_interval_has_uninterrupted_service {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
    ∀ (tsk : Task) (j : Job), arrives_in arr_seq j → job_of_task tsk j = true →
      job_cost_positive j = true → work_conserving arr_seq sched → arrival_sequence_uniq arr_seq →
      reflexive_job_priorities JLFP →
    ∀ t_busy : instant, pending sched j t_busy = true →
      uniprocessor_model PState → unit_service_proc_model PState → ideal_progress_proc_model PState →
    ∀ t1 : instant, busy_interval_prefix arr_seq sched j t1 (t_busy + 1) →
    ∀ priority_inversion_bound : instant → instant,
      priority_inversion_of_job_is_bounded_by arr_seq sched j priority_inversion_bound →
    ∀ delta : duration, 0 < delta →
      priority_inversion_bound (job_arrival j - t1) + workload_of_hep_jobs arr_seq j t1 (t1 + delta) ≤
        delta →
      (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true →
        ¬ quiet_time arr_seq sched j t) →
      delta ≤ priority_inversion_bound (job_arrival j - t1) +
        service_of_higher_or_equal_priority_jobs sched (arrivals_between arr_seq t1 (t1 + delta)) j t1
          (t1 + delta) := by
  intro hva PState sched hfrom hmust hcomp JLFP _ hwb tsk j ha _ hpos hwc _ hrefl t_busy _ huni hunit
    hideal t1 hbip PIB hPIB delta hdelta _ hnq
  have hbip' := hbip
  obtain ⟨hlt, hq1, hnq1, harr⟩ := hbip'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
  obtain ⟨jobs, hjobs⟩ : ∃ jobs, jobs = arrivals_between arr_seq 0 (t1 + delta) := ⟨_, rfl⟩
  have hnd : jobs.Nodup := hjobs ▸ arrivals_uniq arr_seq hva.1 hva.2 0 (t1 + delta)
  -- total service is the interval length
  have htot := no_idle_time_within_non_quiet_time_interval arr_seq hva sched hfrom hmust JLFP hwb j hwc
    hva.2 t1 delta hnq huni hunit hideal
  -- hep service does not depend on the jobs released before t1
  have hsame := hep_jobs_receive_no_service_before_quiet_time arr_seq hva sched hcomp JLFP j t1 hq1 delta
  -- split total service into hep and non-hep service
  have hneg := service_of_jobs_negate_pred sched (fun x => JLFP.hep_job x j) jobs t1 (t1 + delta)
  have hnle := service_of_jobs_pred_impl sched jobs t1 (t1 + delta) (fun x => !JLFP.hep_job x j)
    (fun _ => true) (fun _ _ _ => rfl)
  -- non-hep service is bounded by the cumulative priority inversion
  have hpi : service_of_jobs sched (fun x => !JLFP.hep_job x j) jobs t1 (t1 + delta) ≤
      cumulative_priority_inversion arr_seq sched j t1 (t1 + delta) := by
    rw [service_of_jobs_sum_over_time_interval]
    unfold cumulative_priority_inversion
    apply Finset.sum_le_sum
    intro t _
    exact nonhep_service_le_priority_inversion arr_seq hva sched hfrom hmust huni hunit JLFP hrefl j jobs
      hnd t
  -- the cumulative priority inversion is bounded
  have hpib : cumulative_priority_inversion arr_seq sched j t1 (t1 + delta) ≤
      PIB (job_arrival j - t1) := by
    rcases Nat.le_total (t1 + delta) (t_busy + 1) with hle | hge
    · have hcat := cumulative_priority_inversion_cat arr_seq sched j (t1 + delta) t1 (t_busy + 1)
        (Nat.le_add_right _ _) hle
      have hb := hPIB t1 (t_busy + 1) hbip
      omega'
    · apply hPIB
      refine ⟨by omega', hq1, ?_, ?_⟩
      · intro t ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact hnq t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      · simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'
  subst hjobs
  unfold service_of_higher_or_equal_priority_jobs at hsame ⊢
  unfold total_service_of_jobs_in at htot hneg
  omega'

/-- Without a quiet time, the higher-or-equal-priority workload exceeds the
corresponding service. -/
theorem busy_interval_too_much_workload [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState), jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (JLFP : JLFP_policy Job) (j : Job), arrival_sequence_uniq arr_seq →
    ∀ t_busy : instant, unit_service_proc_model PState →
    ∀ t1 : instant, busy_interval_prefix arr_seq sched j t1 (t_busy + 1) →
    ∀ delta : duration, 0 < delta →
      (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true →
        ¬ quiet_time arr_seq sched j t) →
      service_of_higher_or_equal_priority_jobs sched (arrivals_between arr_seq t1 (t1 + delta)) j t1
          (t1 + delta) <
        workload_of_hep_jobs arr_seq j t1 (t1 + delta) := by
  intro hva PState sched _ hcomp JLFP j _ t_busy hunit t1 hbip delta hdelta hnq
  obtain ⟨_, hq1, _, _⟩ := hbip
  obtain ⟨j0, ha0, hab0, hhep0, hnc0⟩ := not_quiet_implies_exists_pending_job arr_seq hva sched JLFP j t1
    (t1 + delta) (Nat.le_add_right _ _) hq1
    (hnq (t1 + delta) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'))
  have hin0 : j0 ∈ arrivals_between arr_seq t1 (t1 + delta) :=
    of_decide_eq_true (arrived_between_implies_in_arrivals arr_seq hva.1 j0 t1 (t1 + delta) ha0 hab0)
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs workload_of_hep_jobs workload_of_jobs
  apply sumFiltered_lt _ _ _ _ (fun x _ _ => cumulative_service_le_job_cost sched hcomp x hunit t1
    (t1 + delta)) j0 hin0 hhep0
  have hcat := service_cat sched j0 t1 (t1 + delta) (Nat.le_add_right _ _)
  unfold completed_by at hnc0
  simp only [decide_eq_true_eq] at hnc0
  omega'

/-- Hence the workload together with the priority-inversion bound exceeds the
interval length. -/
theorem busy_interval_workload_larger_than_interval {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
    ∀ (tsk : Task) (j : Job), arrives_in arr_seq j → job_of_task tsk j = true →
      job_cost_positive j = true → work_conserving arr_seq sched → arrival_sequence_uniq arr_seq →
      reflexive_job_priorities JLFP →
    ∀ t_busy : instant, pending sched j t_busy = true →
      uniprocessor_model PState → unit_service_proc_model PState → ideal_progress_proc_model PState →
    ∀ t1 : instant, busy_interval_prefix arr_seq sched j t1 (t_busy + 1) →
    ∀ priority_inversion_bound : instant → instant,
      priority_inversion_of_job_is_bounded_by arr_seq sched j priority_inversion_bound →
    ∀ delta : duration, 0 < delta →
      priority_inversion_bound (job_arrival j - t1) + workload_of_hep_jobs arr_seq j t1 (t1 + delta) ≤
        delta →
      (∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true →
        ¬ quiet_time arr_seq sched j t) →
      delta < priority_inversion_bound (job_arrival j - t1) + workload_of_hep_jobs arr_seq j t1 (t1 + delta) := by
  intro hva PState sched hfrom hmust hcomp JLFP _ hwb tsk j ha hjt hpos hwc huniq hrefl t_busy hpend huni hunit
    hideal t1 hbip PIB hPIB delta hdelta hwl hnq
  have h1 := busy_interval_has_uninterrupted_service arr_seq hva sched hfrom hmust hcomp JLFP hwb tsk j ha hjt
    hpos hwc huniq hrefl t_busy hpend huni hunit hideal t1 hbip PIB hPIB delta hdelta hwl hnq
  have h2 := busy_interval_too_much_workload arr_seq hva sched hmust hcomp JLFP j huniq t_busy hunit t1 hbip
    delta hdelta hnq
  omega'

/-- A busy-interval prefix whose workload is bounded ends within the bound. -/
theorem busy_interval_is_bounded {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
    ∀ (tsk : Task) (j : Job), arrives_in arr_seq j → job_of_task tsk j = true →
      job_cost_positive j = true → work_conserving arr_seq sched → arrival_sequence_uniq arr_seq →
      reflexive_job_priorities JLFP →
    ∀ t_busy : instant, pending sched j t_busy = true →
      uniprocessor_model PState → unit_service_proc_model PState → ideal_progress_proc_model PState →
    ∀ t1 : instant, busy_interval_prefix arr_seq sched j t1 (t_busy + 1) →
    ∀ priority_inversion_bound : instant → instant,
      priority_inversion_of_job_is_bounded_by arr_seq sched j priority_inversion_bound →
    ∀ delta : duration, 0 < delta →
      priority_inversion_bound (job_arrival j - t1) + workload_of_hep_jobs arr_seq j t1 (t1 + delta) ≤
        delta →
      ∃ t2 : Nat, t2 ≤ t1 + delta ∧ busy_interval arr_seq sched j t1 t2 := by
  intro hva PState sched hfrom hmust hcomp JLFP _ hwb tsk j ha hjt hpos hwc huniq hrefl t_busy hpend huni hunit
    hideal t1 hbip PIB hPIB delta hdelta hwl
  classical
  by_cases hex : ∃ t, t1 < t ∧ t ≤ t1 + delta ∧ quiet_time arr_seq sched j t
  · let t2 := Nat.find hex
    have hspec : t1 < t2 ∧ t2 ≤ t1 + delta ∧ quiet_time arr_seq sched j t2 := Nat.find_spec hex
    have hmin : ∀ t, t < t2 → ¬ (t1 < t ∧ t ≤ t1 + delta ∧ quiet_time arr_seq sched j t) :=
      fun t ht => Nat.find_min hex ht
    have hbip' := hbip
    obtain ⟨_, hq1, hnq1, harr⟩ := hbip'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
    refine ⟨t2, hspec.2.1, ⟨hspec.1, hq1, ?_, ?_⟩, hspec.2.2⟩
    · intro t ht hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact hmin t ht.2 ⟨ht.1, by omega', hq⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨harr.1, ?_⟩
      by_contra hge
      exact hnq1 t2 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hspec.2.2
  · exfalso
    have hnq : ∀ t : Nat, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true →
        ¬ quiet_time arr_seq sched j t := by
      intro t ht hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact hex ⟨t, ht.1, ht.2, hq⟩
    have := busy_interval_workload_larger_than_interval arr_seq hva sched hfrom hmust hcomp JLFP hwb tsk j ha
      hjt hpos hwc huniq hrefl t_busy hpend huni hunit hideal t1 hbip PIB hPIB delta hdelta hwl hnq
    omega'

/-- A workload bound implies a busy interval containing the arrival of the job. -/
theorem exists_busy_interval {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
    ∀ (tsk : Task) (j : Job), arrives_in arr_seq j → job_of_task tsk j = true →
      job_cost_positive j = true → work_conserving arr_seq sched → arrival_sequence_uniq arr_seq →
      reflexive_job_priorities JLFP →
      uniprocessor_model PState → unit_service_proc_model PState → ideal_progress_proc_model PState →
    ∀ priority_inversion_bound : duration → duration,
      priority_inversion_of_job_is_bounded_by arr_seq sched j priority_inversion_bound →
    ∀ delta : duration, 0 < delta →
      (∀ t : Nat, priority_inversion_bound (job_arrival j - t) + workload_of_hep_jobs arr_seq j t (t + delta) ≤
        delta) →
      0 < job_cost j →
      ∃ t1 t2 : Nat, (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true ∧
        t2 ≤ t1 + delta ∧ busy_interval arr_seq sched j t1 t2 := by
  intro hva PState sched hfrom hmust hcomp JLFP _ hwb tsk j ha hjt hpos hwc huniq hrefl huni hunit hideal
    PIB hPIB delta hdelta hwl hcost
  have hpend := job_pending_at_arrival sched j hcost hmust
  obtain ⟨t1, hbip, _⟩ := exists_busy_interval_prefix arr_seq hva sched JLFP j ha hrefl (job_arrival j) hpend
  obtain ⟨t2, hle, hbi⟩ := busy_interval_is_bounded arr_seq hva sched hfrom hmust hcomp JLFP hwb tsk j ha hjt
    hpos hwc huniq hrefl (job_arrival j) hpend huni hunit hideal t1 hbip PIB hPIB delta hdelta (hwl t1)
  exact ⟨t1, t2, hbi.1.2.2.2, hle, hbi⟩

/-- A workload bound bounds the response time of the job. -/
theorem busy_interval_bounds_response_time {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      completed_jobs_dont_execute sched →
    ∀ (JLFP : JLFP_policy Job) [JobReady Job PState], work_bearing_readiness arr_seq sched →
    ∀ (tsk : Task) (j : Job), arrives_in arr_seq j → job_of_task tsk j = true →
      job_cost_positive j = true → work_conserving arr_seq sched → arrival_sequence_uniq arr_seq →
      reflexive_job_priorities JLFP →
      uniprocessor_model PState → unit_service_proc_model PState → ideal_progress_proc_model PState →
    ∀ priority_inversion_bound : duration → duration,
      priority_inversion_of_job_is_bounded_by arr_seq sched j priority_inversion_bound →
    ∀ delta : duration, 0 < delta →
      (∀ t : Nat, priority_inversion_bound (job_arrival j - t) + workload_of_hep_jobs arr_seq j t (t + delta) ≤
        delta) →
      completed_by sched j (job_arrival j + delta) = true := by
  intro hva PState sched hfrom hmust hcomp JLFP _ hwb tsk j ha hjt hpos hwc huniq hrefl huni hunit hideal
    PIB hPIB delta hdelta hwl
  rcases Nat.eq_zero_or_pos (job_cost j) with h0 | hcost
  · unfold completed_by; rw [h0]; exact decide_eq_true (Nat.zero_le _)
  · obtain ⟨t1, t2, hin, hle, hbi⟩ := exists_busy_interval arr_seq hva sched hfrom hmust hcomp JLFP hwb tsk j
      ha hjt hpos hwc huniq hrefl huni hunit hideal PIB hPIB delta hdelta hwl hcost
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    exact completion_monotonic sched j t2 _ (by omega')
      (job_completes_within_busy_interval arr_seq sched JLFP j ha hrefl t1 t2 hbi)

end ExistsBusyIntervalJLFP

end Prosa.Analysis.Facts.BusyInterval.Existence
