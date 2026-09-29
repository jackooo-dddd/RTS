-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/overheads/priority_bump.v

import Prosa.Model.Readiness.Basic
import Prosa.Model.Processor.Overheads
import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Facts.Priority.Sequential
import Prosa.Analysis.Facts.Model.Overheads.Schedule
import Prosa.Analysis.Definitions.Overheads.PriorityBump

namespace Prosa.Analysis.Facts.Model.Overheads.PriorityBump

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Readiness.Basic
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Processor.Overheads
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.AlwaysHigherPriority
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.Overheads.PriorityBump
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Model.Preemption
open Prosa.Analysis.Facts.Priority.Sequential
open Prosa.Analysis.Facts.BusyInterval.HepAtPt
open Prosa.Analysis.Facts.Model.Overheads.Schedule

/-! Properties of priority bumps in an explicit-overhead uniprocessor schedule.
Binders follow the elaborated source types (unused section hypotheses are not
part of the statements). The source's section-local `basic_ready_instance`
(implicit in the elaborated `valid_schedule`, `work_conserving` and
`respects_JLFP_policy_at_preemption_point`) is the accepted Lean definition of
the same name, passed explicitly. Representation: a Boolean in `Prop` position
is `= true`; `~~ b` is `(!b) = true`; `a < t <= b` is a decided conjunction;
`x \in s` is `decide (x ∈ s) = true`; a Boolean equation `b = (x <= y)` is
`b = decide (x ≤ y)`. -/

variable {Job : JobType} [DecidableEq Job]

/-- LEAN_HELPER: under basic readiness a scheduled job is pending. -/
private theorem pb_scheduled_pending [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job))
    (hvs : @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq)
    (j : Job) (t : instant) (hs : scheduled_at sched j t = true) : pending sched j t = true :=
  hvs.2 j t hs

/-- LEAN_HELPER: a job scheduled at `t + 1` but not the job scheduled at `t`
starts executing at `t + 1`, which is a preemption time. -/
private theorem pb_first_moment [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) (sched : schedule (processor_state Job))
    (hvs : @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq)
    [JobPreemptable Job] (hvpm : valid_preemption_model arr_seq sched) (j2 : Job) (t0 : instant)
    (hns : (!scheduled_at sched j2 t0) = true) (hs : scheduled_at sched j2 (t0 + 1) = true) :
    preemption_time arr_seq sched (t0 + 1) = true := by
  have hmust : jobs_must_arrive_to_execute sched := by
    intro j t hsj
    have h := pb_scheduled_pending arr_seq sched hvs j t hsj
    unfold pending at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  exact first_moment_is_pt arr_seq hva (processor_state Job) overheads_proc_model_is_a_uniprocessor_model
    sched hvs.1 hmust hvpm j2 t0 (hvs.1 j2 (t0 + 1) hs) hns hs

/-- If a priority bump occurs at time `t`, then `t` is a preemption time. -/
theorem priority_bump_implies_preemption_time [JobArrival Job] [JobCost Job] (JLFP : JLFP_policy Job) :
    reflexive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ t : instant, priority_bump sched t = true → preemption_time arr_seq sched t = true := by
  intro hrefl arr_seq hva sched hvs _ hvpm t hpb
  cases t with
  | zero =>
    exfalso
    unfold priority_bump at hpb
    simp only [Nat.pred_zero] at hpb
    cases hsj : scheduled_job sched 0 with
    | none => rw [hsj] at hpb; simp at hpb
    | some j => rw [hsj] at hpb; simp [hrefl j] at hpb
  | succ t0 =>
    unfold priority_bump at hpb
    simp only [Nat.pred_succ, Nat.succ_eq_add_one] at hpb
    cases hs2 : scheduled_job sched (t0 + 1) with
    | none =>
      exfalso
      cases hs1 : scheduled_job sched t0 <;> rw [hs1, hs2] at hpb <;> simp at hpb
    | some j2 =>
      have hsched2 : scheduled_at sched j2 (t0 + 1) = true := (scheduled_at_iff_scheduled_job sched j2 (t0 + 1)).2 hs2
      refine pb_first_moment arr_seq hva sched hvs hvpm j2 t0 ?_ hsched2
      cases hsc : scheduled_at sched j2 t0
      · rfl
      · exfalso
        have hs1 := (scheduled_at_iff_scheduled_job sched j2 t0).1 hsc
        rw [hs1, hs2] at hpb
        simp [hrefl j2] at hpb

/-- A priority bump within a busy-interval prefix can only be caused by a job
that arrived within the same busy-interval prefix. -/
theorem priority_bump_implies_hp_arrival_in_prefix [JobArrival Job] [JobCost Job] (JLFP : JLFP_policy Job) :
    reflexive_job_priorities JLFP → transitive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq
        sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t t_arr : instant, t1 ≤ t → t < t_arr → t_arr ≤ t2 → priority_bump sched t = true →
      ∃ jhp : Job, scheduled_at sched jhp t = true ∧ decide (jhp ∈ arrivals_between arr_seq t1 t_arr) = true := by
  intro hrefl htrans arr_seq hva sched hvs hwc _ hvpm hresp j ha hpos t1 t2 hbip t t_arr h1 h2 h3 hpb
  have hpt := priority_bump_implies_preemption_time JLFP hrefl arr_seq hva sched hvs hvpm t hpb
  letI : JobReady Job (processor_state Job) := basic_ready_instance
  obtain ⟨jhp, harr, _, hs⟩ := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point arr_seq hva
    overheads_proc_model_is_a_uniprocessor_model sched JLFP hrefl htrans
    (basic_readiness_is_work_bearing_readiness arr_seq sched hrefl) hvs hwc hresp j ha hpos t1 t2 hbip t
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1, by ((try dsimp only [instant] at *); omega)⟩) hpt
  refine ⟨jhp, hs, ?_⟩
  have hpend := pb_scheduled_pending arr_seq sched hvs jhp t hs
  unfold pending has_arrived at hpend
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpend
  unfold arrived_between at harr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at harr
  apply arrived_between_implies_in_arrivals arr_seq hva.1 jhp t1 t_arr (hvs.1 jhp t hs)
  unfold arrived_between
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨harr.1, by ((try dsimp only [instant] at *); omega)⟩

/-- Under the FIFO policy, no priority bumps occur during `(t1, t2]`, since jobs
are scheduled in arrival order and thus priorities never increase. -/
theorem no_priority_bumps_in_fifo [JobArrival Job] [JobCost Job] (JLFP : JLFP_policy Job) :
    reflexive_job_priorities JLFP → transitive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq
        sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
      (∀ j1 j2 : Job, JLFP.hep_job j1 j2 = decide (job_arrival j1 ≤ job_arrival j2)) →
    ∀ t : instant, (decide (t1 < t) && decide (t ≤ t2)) = true → (!priority_bump sched t) = true := by
  intro hrefl htrans arr_seq hva sched hvs hwc _ hvpm hresp j ha hpos t1 t2 hbip hfifo t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  cases hpb : priority_bump sched t
  · rfl
  · exfalso
    unfold priority_bump at hpb
    cases hs1 : scheduled_job sched (Nat.pred t) with
    | none =>
      cases hs2 : scheduled_job sched t with
      | none => rw [hs1, hs2] at hpb; simp at hpb
      | some j2 =>
        letI : JobReady Job (processor_state Job) := basic_ready_instance
        obtain ⟨js, hjs⟩ := job_scheduled_in_busy_interval_prefix JLFP hrefl arr_seq hva sched
          (basic_readiness_is_work_bearing_readiness arr_seq sched hrefl) hvs hwc j ha hpos t1 t2 hbip
          (Nat.pred t)
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]
              rw [Nat.pred_eq_sub_one]
              exact ⟨by ((try dsimp only [instant] at *); omega), by ((try dsimp only [instant] at *); omega)⟩)
        rw [(scheduled_at_iff_scheduled_job sched js (Nat.pred t)).1 hjs] at hs1
        cases hs1
    | some j1 =>
      cases hs2 : scheduled_job sched t with
      | none => rw [hs1, hs2] at hpb; simp at hpb
      | some j2 =>
        rw [hs1, hs2] at hpb
        dsimp only at hpb
        rw [hfifo] at hpb
        have hlt : job_arrival j2 < job_arrival j1 := by
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hpb
          ((try dsimp only [instant] at *); omega)
        have hsched1 := (scheduled_at_iff_scheduled_job sched j1 (Nat.pred t)).2 hs1
        have hsched2 := (scheduled_at_iff_scheduled_job sched j2 t).2 hs2
        have hahp : @always_higher_priority Job _ (JLFP_to_JLDP (JLFP := JLFP)) j2 j1 := by
          refine (@always_higher_priority_jlfp Job _ JLFP j2 j1).2 ?_
          rw [hfifo, hfifo]
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
          exact ⟨by ((try dsimp only [instant] at *); omega), by ((try dsimp only [instant] at *); omega)⟩
        letI : JobReady Job (processor_state Job) := basic_ready_instance
        have hc := early_hep_job_is_scheduled arr_seq hva JLFP htrans (processor_state Job)
          overheads_proc_model_is_a_uniprocessor_model sched
          (basic_readiness_is_work_bearing_readiness arr_seq sched hrefl) hvs hvpm hresp j2 j1
          (hvs.1 j2 t hsched2) hlt hahp (Nat.pred t) hsched1
        have hc' := completion_monotonic sched j2 (Nat.pred t) t (Nat.pred_le t) hc
        have hpend := pb_scheduled_pending arr_seq sched hvs j2 t hsched2
        unfold pending at hpend
        rw [hc'] at hpend
        simp at hpend

end Prosa.Analysis.Facts.Model.Overheads.PriorityBump
