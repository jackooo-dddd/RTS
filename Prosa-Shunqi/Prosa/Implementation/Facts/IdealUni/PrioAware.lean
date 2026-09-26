-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/facts/ideal_uni/prio_aware.v

import Prosa.Implementation.Facts.IdealUni.PreemptionAware
import Prosa.Model.Schedule.PriorityDriven

namespace Prosa.Implementation.Facts.IdealUni.PrioAware

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Schedule.WorkConserving
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Definitions.Readiness
open Prosa.Analysis.Facts.Readiness.Backlogged
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Util.Supremum
open Prosa.Implementation.Definitions.GenericScheduler
open Prosa.Implementation.Definitions.IdealUniScheduler
open Prosa.Implementation.Facts.GenericSchedule
open Prosa.Implementation.Facts.IdealUni.PreemptionAware

/-! Properties of the priority-aware ideal uniprocessor scheduler. Binders
follow the elaborated source types (each theorem takes only the section inputs
and hypotheses it uses, in their elaborated order; instance inputs quantified
after a hypothesis are `∀ [..]` binders). Representation: the section-local
`idle_state` is `none`; the section-local `prefix t` is inlined as a `match`
on `t`, as in the elaborated types; a Boolean in `Prop` position is `= true`;
`t.+1` is `t + 1`. -/

section PrioAwareUniprocessorScheduler

variable {Job : JobType} [DecidableEq Job] [JC : JobCost Job] [JA : JobArrival Job]

/-- Deciding `s = some j` on an ideal state is deciding it on `Option Job`, as
in the accepted ideal-schedule facts. -/
local instance idealStateDecidableEqSome
    (s : (processor_state Job).State) (j : Job) : Decidable (s = some j) :=
  (inferInstance : DecidableEq (Option Job)) s (some j)

theorem uni_schedule_work_conserving (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ [RM : JobReady Job (processor_state Job)], nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] [JLDP : JLDP_policy Job],
      work_conserving arr_seq (uni_schedule arr_seq) := by
  intro H_valid RM H_nc _ _
  exact np_schedule_work_conserving arr_seq H_valid H_nc choose_highest_prio_job
    (fun t jobs => ⟨supremum_none _ jobs, fun h => by subst h; rfl⟩)

theorem uni_schedule_valid (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] :
    nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] [JLDP : JLDP_policy Job],
      valid_schedule (uni_schedule arr_seq) arr_seq := by
  intro H_nc _ _
  exact np_schedule_valid arr_seq choose_highest_prio_job
    (fun t s j h => decide_eq_true (supremum_in _ j s h)) H_nc

theorem schedule_respects_preemption_model (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] :
    nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] [JLDP : JLDP_policy Job],
      valid_nonpreemptive_readiness RM (uni_schedule arr_seq) →
      (∀ j : Job, arrives_in arr_seq j → job_cannot_become_nonpreemptive_before_execution j = true) →
      Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq
        (uni_schedule arr_seq) := by
  intro H_nc _ _ H_valid_pb H_valid_pf
  exact np_respects_preemption_model arr_seq H_nc choose_highest_prio_job H_valid_pf H_valid_pb

theorem scheduled_job_is_supremum (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ [RM : JobReady Job (processor_state Job)], nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] [JLDP : JLDP_policy Job] (j : Job) (t : instant),
      scheduled_at (uni_schedule arr_seq) j t = true →
      preemption_time arr_seq (uni_schedule arr_seq) t = true →
      supremum (hep_job_at t) (jobs_backlogged_at arr_seq
        (match t with
          | 0 => empty_schedule none
          | t' + 1 => schedule_up_to (allocation_at arr_seq choose_highest_prio_job) none t') t) =
        some j := by
  intro H_valid RM H_nc _ _ j t SCHED PREEMPT
  rw [scheduled_at_def] at SCHED
  have S0 : schedule_up_to (allocation_at arr_seq choose_highest_prio_job) none t t = some j :=
    of_decide_eq_true SCHED
  cases t with
  | zero => exact S0
  | succ t =>
      have NOT_NP : prev_job_nonpreemptive
          (schedule_up_to (allocation_at arr_seq choose_highest_prio_job) none t) (t + 1) = false := by
        cases hp : prev_job_nonpreemptive
            (schedule_up_to (allocation_at arr_seq choose_highest_prio_job) none t) (t + 1) with
        | false => rfl
        | true =>
            have NC := np_consistent arr_seq H_valid H_nc choose_highest_prio_job
              (fun t s j h => decide_eq_true (supremum_in _ j s h)) (t + 1) hp
            have P : preemption_time arr_seq (pmc_uni_schedule arr_seq choose_highest_prio_job) (t + 1) = true :=
              PREEMPT
            rw [P] at NC
            exact absurd NC (by simp)
      have E : (bif prev_job_nonpreemptive
            (schedule_up_to (allocation_at arr_seq choose_highest_prio_job) none t) (t + 1) then
          schedule_up_to (allocation_at arr_seq choose_highest_prio_job) none t t
        else choose_highest_prio_job (t + 1) (jobs_backlogged_at arr_seq
          (schedule_up_to (allocation_at arr_seq choose_highest_prio_job) none t) (t + 1))) = some j :=
        (schedule_up_to_def (allocation_at arr_seq choose_highest_prio_job) none (t + 1)).symm.trans S0
      rw [NOT_NP] at E
      exact E

private theorem respects_aux (arr_seq : arrival_sequence Job) [RM : JobReady Job (processor_state Job)]
    (H_nc : nonclairvoyant_readiness RM) [JobPreemptable Job] [JLDP : JLDP_policy Job]
    (H_valid : valid_arrival_sequence arr_seq)
    (H_refl : reflexive_priorities JLDP) (H_total : total_priorities JLDP)
    (H_trans : transitive_priorities JLDP)
    (pref : schedule (processor_state Job)) (t : instant) (j1 j2 : Job)
    (PREFIX : identical_prefix (uni_schedule arr_seq) pref t) (IDLE : pref t = none)
    (SUP : supremum (hep_job_at t) (jobs_backlogged_at arr_seq pref t) = some j2)
    (hs : scheduled_at (uni_schedule arr_seq) j1 t = false) (ARRIVES : arrives_in arr_seq j1)
    (BACK_j1 : backlogged (uni_schedule arr_seq) j1 t = true) :
    JLDP.hep_job_at t j2 j1 = true := by
  have NOT_SCHED : (!scheduled_at pref j1 t) = true := by
    rw [scheduled_at_def, IDLE]
    simp
  have BACK := backlogged_prefix_invariance' H_nc _ _ t PREFIX t j1 (by rw [hs]; rfl) NOT_SCHED
    (Nat.le_refl _)
  rw [BACK] at BACK_j1
  exact supremum_spec (hep_job_at t) (H_refl t) (H_total t) (fun x y z => H_trans t y x z) j2 _ SUP j1
    (of_decide_eq_true (mem_backlogged_jobs arr_seq _ H_valid.1 j1 t ARRIVES BACK_j1))

theorem schedule_respects_policy (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ [RM : JobReady Job (processor_state Job)], nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] [JLDP : JLDP_policy Job],
      reflexive_priorities JLDP → total_priorities JLDP → transitive_priorities JLDP →
      respects_JLDP_policy_at_preemption_point arr_seq (uni_schedule arr_seq) JLDP := by
  intro H_valid RM H_nc _ JLDP H_refl H_total H_trans j1 j2 t ARRIVES PREEMPT BACK_j1 SCHED_j2
  have SUP := scheduled_job_is_supremum arr_seq H_valid H_nc j2 t SCHED_j2 PREEMPT
  cases hs : scheduled_at (uni_schedule arr_seq) j1 t with
  | true =>
      have E := ideal_proc_model_is_a_uniprocessor_model Job j1 j2 (uni_schedule arr_seq) t hs SCHED_j2
      subst E
      exact H_refl t j1
  | false =>
      cases t with
      | zero =>
          exact respects_aux arr_seq H_nc H_valid H_refl H_total H_trans (empty_schedule none) 0 j1 j2
            (fun x hx => absurd hx (Nat.not_lt_zero _)) rfl SUP hs ARRIVES BACK_j1
      | succ t =>
          exact respects_aux arr_seq H_nc H_valid H_refl H_total H_trans
            (schedule_up_to (allocation_at arr_seq choose_highest_prio_job) none t) (t + 1) j1 j2
            (fun x hx => schedule_up_to_prefix_inclusion _ _ x t (Nat.le_of_lt_succ hx) x (Nat.le_refl _))
            (schedule_up_to_empty (allocation_at arr_seq choose_highest_prio_job) none t (t + 1)
              (Nat.lt_succ_self _))
            SUP hs ARRIVES BACK_j1

end PrioAwareUniprocessorScheduler

end Prosa.Implementation.Facts.IdealUni.PrioAware
