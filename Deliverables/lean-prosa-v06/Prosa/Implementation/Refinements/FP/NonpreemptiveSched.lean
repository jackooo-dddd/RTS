-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/FP/nonpreemptive_sched.v

import Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive
import Prosa.Analysis.Facts.Readiness.Sequential
import Prosa.Analysis.Definitions.Tardiness
import Prosa.Implementation.Facts.IdealUni.PrioAware
import Prosa.Implementation.Definitions.Task

/-! # Fully-nonpreemptive fixed-priority schedules

The schedule is valid and nonpreemptive, and the fixed-priority policy is respected at each preemption point.

Representation: the `Task`/`Job` aliases (the concrete types as `eqType`s) are abbreviations of the accepted
concrete types; the source's section `Instance sequential_ready_instance` (which depends on `arr_seq`) is a
definition taking `arr_seq`, passed explicitly wherever the elaborated types use it, as are the section-local
instances `fully_nonpreemptive_job_model` and `NumericFPAscending` (through the accepted canonical FP → JLFP → JLDP
conversions); the section's `arr_seq` and `H_valid_arrivals` are explicit binders, in the order of the elaborated
types; `~~ b` is `(!b) = true` and `t.+1` is `t + 1`. -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.FP.NonpreemptiveSched

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.NumericFixedPriority
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyNonpreemptive
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Definitions.Readiness
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Util.Supremum
open Prosa.Implementation.Definitions.Task
open Prosa.Implementation.Definitions.GenericScheduler
open Prosa.Implementation.Definitions.IdealUniScheduler
open Prosa.Implementation.Facts.GenericSchedule
open Prosa.Implementation.Facts.IdealUni.PreemptionAware
open Prosa.Implementation.Facts.IdealUni.PrioAware

/-- The concrete task type. -/
abbrev Task : Type := concrete_task

/-- The concrete job type. -/
abbrev Job : Type := concrete_job

/-- The sequential readiness model of an arrival sequence. -/
noncomputable def sequential_ready_instance (arr_seq : arrival_sequence Job) : JobReady Job (processor_state Job) :=
  Prosa.Model.Readiness.Sequential.sequential_ready_instance (Task := Task) arr_seq

/-- The fully-nonpreemptive fixed-priority schedule. -/
noncomputable def sched (arr_seq : arrival_sequence Job) : schedule (processor_state Job) :=
  @uni_schedule Job _ _ _ arr_seq (sequential_ready_instance arr_seq) fully_nonpreemptive_job_model
    (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task)))

/-- Jobs are ready when scheduled. -/
theorem sched_jobs_must_be_ready_to_execute :
    ∀ arr_seq : arrival_sequence Job,
      @jobs_must_be_ready_to_execute Job _ _ _ (sched arr_seq) _ (sequential_ready_instance arr_seq) :=
  fun arr_seq =>
    @jobs_must_be_ready Job _ _ _ arr_seq (sequential_ready_instance arr_seq) fully_nonpreemptive_job_model
      (@choose_highest_prio_job Job _ (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task))))
      (fun _ s j h => decide_eq_true (supremum_in _ j s h))
      (Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_nonclairvoyance (Task := Task) arr_seq)

/-- The schedule is valid. -/
theorem sched_valid :
    ∀ arr_seq : arrival_sequence Job,
      @valid_schedule Job _ _ _ (sched arr_seq) _ (sequential_ready_instance arr_seq) arr_seq :=
  fun arr_seq =>
    ⟨@np_schedule_jobs_from_arrival_sequence Job _ _ _ arr_seq (sequential_ready_instance arr_seq) fully_nonpreemptive_job_model
      (@choose_highest_prio_job Job _ (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task))))
      (fun _ s j h => decide_eq_true (supremum_in _ j s h)),
     sched_jobs_must_be_ready_to_execute arr_seq⟩

/-- LEAN_HELPER: schedules with identical prefixes provide the same service within the prefix. -/
private theorem service_of_identical_prefix (s s' : schedule (processor_state Job)) (h : instant)
    (hp : identical_prefix s s' h) (j : Job) (t : instant) (ht : t ≤ h) :
    service s j t = service s' j t := by
  unfold service service_during
  apply Finset.sum_congr rfl
  intro x hx
  have hx' : x < h := by
    simp only [Finset.mem_Ico] at hx
    try dsimp only [instant] at *
    omega
  unfold service_at
  rw [hp x hx']

/-- A scheduled job that is not complete at the next instant stays scheduled. -/
theorem sched_nonpreemptive_next :
    ∀ (arr_seq : arrival_sequence Job) (j : Job) (t : instant),
      scheduled_at (sched arr_seq) j t = true →
      (!completed_by (sched arr_seq) j (t + 1)) = true →
      scheduled_at (sched arr_seq) j (t + 1) = true := by
  intro arr_seq j t SCHED NCOMP
  have READY := sched_jobs_must_be_ready_to_execute arr_seq j t SCHED
  -- the prefix up to `t` and the schedule agree before `t + 1`
  let alloc := @allocation_at Job _ _ _ arr_seq (sequential_ready_instance arr_seq) fully_nonpreemptive_job_model
    (@choose_highest_prio_job Job _ (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task))))
  have PREFIX : identical_prefix (schedule_up_to alloc none t) (sched arr_seq) (t + 1) :=
    schedule_up_to_identical_prefix alloc none t (t + 1) (Nat.le_refl _)
  have SERV : service (schedule_up_to alloc none t) j (t + 1) = service (sched arr_seq) j (t + 1) :=
    service_of_identical_prefix _ _ (t + 1) PREFIX j (t + 1) (Nat.le_refl _)
  have ST : schedule_up_to alloc none t t = some j := by
    rw [PREFIX t (Nat.lt_succ_self t)]
    have h := SCHED
    rw [scheduled_at_def] at h
    simpa only [decide_eq_true_eq] using h
  -- the job has arrived, received some service, and is not complete
  have READY' : (pending (sched arr_seq) j t &&
      prior_jobs_complete (Task := Task) arr_seq (sched arr_seq) j t) = true := READY
  have ARR : has_arrived j t = true := by
    have h := (Bool.and_eq_true_iff.mp READY').1
    unfold pending at h
    exact (Bool.and_eq_true_iff.mp h).1
  have POS : 0 < service (sched arr_seq) j (t + 1) :=
    scheduled_implies_nonzero_service (sched arr_seq) j (ideal_proc_model_ensures_ideal_progress Job) (t + 1)
      ⟨t, Nat.lt_succ_self t, SCHED⟩
  have LT : service (sched arr_seq) j (t + 1) < job_cost j :=
    (less_service_than_cost_is_incomplete (sched arr_seq) j (t + 1)).mpr NCOMP
  -- so the previous job is still nonpreemptive at `t + 1`
  have HA : has_arrived j (t + 1) = true := by
    unfold has_arrived at ARR ⊢
    simp only [decide_eq_true_eq] at ARR ⊢
    exact Nat.le_succ_of_le ARR
  have HCX : ∀ x : Job,
      completed_by (schedule_up_to alloc none t) x (t + 1) = completed_by (sched arr_seq) x (t + 1) := by
    intro x
    unfold completed_by
    rw [service_of_identical_prefix _ _ (t + 1) PREFIX x (t + 1) (Nat.le_refl _)]
  have HC := HCX j
  have PRIOR : prior_jobs_complete (Task := Task) arr_seq (schedule_up_to alloc none t) j (t + 1) = true := by
    have h := (Bool.and_eq_true_iff.mp READY').2
    unfold prior_jobs_complete at h ⊢
    rw [List.all_eq_true] at h ⊢
    intro x hx
    rw [HCX x]
    exact completion_monotonic _ x t (t + 1) (Nat.le_succ t) (h x hx)
  have h0 : decide (service (sched arr_seq) j (t + 1) = 0) = false := decide_eq_false (Nat.ne_of_gt POS)
  have h1 : decide (service (sched arr_seq) j (t + 1) = job_cost j) = false := decide_eq_false (Nat.ne_of_lt LT)
  have NP : @prev_job_nonpreemptive Job _ _ _ (sequential_ready_instance arr_seq) fully_nonpreemptive_job_model
      (schedule_up_to alloc none t) (t + 1) = true := by
    simp only [prev_job_nonpreemptive, ST, SERV]
    have R : (sequential_ready_instance arr_seq).job_ready (schedule_up_to alloc none t) j (t + 1) = true := by
      show ((has_arrived j (t + 1) && !completed_by (schedule_up_to alloc none t) j (t + 1)) &&
        prior_jobs_complete (Task := Task) arr_seq (schedule_up_to alloc none t) j (t + 1)) = true
      rw [HA, HC, NCOMP, PRIOR]; rfl
    have P : (fully_nonpreemptive_job_model (Job := Job)).job_preemptable j (service (sched arr_seq) j (t + 1)) =
        false := by
      show (decide (service (sched arr_seq) j (t + 1) = 0) || decide (service (sched arr_seq) j (t + 1) = job_cost j))
        = false
      rw [h0, h1]; rfl
    rw [R, P]; rfl
  have NEXT : schedule_up_to alloc none (t + 1) (t + 1) = schedule_up_to alloc none (t + 1) t :=
    @np_job_remains_scheduled Job _ _ _ arr_seq (sequential_ready_instance arr_seq) fully_nonpreemptive_job_model _ (t + 1) NP
  rw [scheduled_at_def]
  simp only [decide_eq_true_eq]
  show schedule_up_to alloc none (t + 1) (t + 1) = some j
  rw [NEXT, ← schedule_up_to_widen alloc none t t (Nat.le_refl _), ST]

/-- The schedule is nonpreemptive. -/
theorem sched_nonpreemptive :
    ∀ arr_seq : arrival_sequence Job,
      nonpreemptive_schedule
        (@uni_schedule Job _ _ _ arr_seq (sequential_ready_instance arr_seq) fully_nonpreemptive_job_model
          (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task)))) := by
  intro arr_seq j t t'
  induction t' with
  | zero =>
      intro LE SCHED _
      have : t = 0 := Nat.le_zero.mp LE
      subst this; exact SCHED
  | succ t' IH =>
      intro LE SCHED NCOMP
      rcases Nat.lt_or_ge t (t' + 1) with LT | GE
      · have NCOMP' : (!completed_by (sched arr_seq) j t') = true := by
          cases hc : completed_by (sched arr_seq) j t' with
          | false => rfl
          | true =>
              have := completion_monotonic (sched arr_seq) j t' (t' + 1) (Nat.le_succ _) hc
              change (!completed_by (sched arr_seq) j (t' + 1)) = true at NCOMP
              rw [this] at NCOMP; exact absurd NCOMP (by decide)
        exact sched_nonpreemptive_next arr_seq j t' (IH (Nat.le_of_lt_succ LT) SCHED NCOMP') NCOMP
      · have : t = t' + 1 := Nat.le_antisymm LE GE
        subst this; exact SCHED

/-- The fixed-priority policy is respected at each preemption point. -/
theorem respects_policy_at_preemption_point_np :
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ _ fully_nonpreemptive_job_model
        (sequential_ready_instance arr_seq) arr_seq (sched arr_seq) (NumericFPAscending Task) :=
  fun arr_seq H_valid =>
    @schedule_respects_policy Job _ _ _ arr_seq H_valid (sequential_ready_instance arr_seq)
      (Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_nonclairvoyance (Task := Task) arr_seq)
      fully_nonpreemptive_job_model (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task)))
      (reflexive_priorities_JLFP_implies_JLDP _
        (reflexive_priorities_FP_implies_JLFP (Job := Job) _ NFPA_is_reflexive))
      (total_priorities_JLFP_implies_JLDP _ (total_priorities_FP_implies_JLFP (Job := Job) _ NFPA_is_total))
      (transitive_priorities_JLFP_implies_JLDP _
        (transitive_priorities_FP_implies_JLFP (Job := Job) _ NFPA_is_transitive))

end Prosa.Implementation.Refinements.FP.NonpreemptiveSched
