-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/pi_cond.v

import Prosa.Analysis.Facts.BusyInterval.Pi

namespace Prosa.Analysis.Facts.BusyInterval.PiCond

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Schedule.WorkConserving
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.Uniprocessor
open Prosa.Analysis.Facts.Priority.Inversion
open Prosa.Analysis.Facts.BusyInterval.Pi
open scoped BigOperators

/-! Cumulative priority inversion equals its conditional variant for any
predicate satisfied by the job scheduled at the start of the busy-interval
prefix.  Binders follow the elaborated source type.  Representation: a Boolean
in `Prop` position is `= true`; a MathComp `pred Job` is `Job → Bool`. -/

section CondPI

variable {Job : JobType} [DecidableEq Job]

private theorem any_congr_mem {X : Type _} (l : List X) (f g : X → Bool)
    (h : ∀ x, x ∈ l → f x = g x) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- Replacing the cumulative priority inversion by its conditional variant. -/
theorem cum_task_pi_eq [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ (jlp : Job) (P : Job → Bool), scheduled_at sched jlp t1 = true → P jlp = true →
      cumulative_priority_inversion arr_seq sched j t1 t2 =
        cumulative_priority_inversion_cond arr_seq sched j P t1 t2 := by
  intro hva PState huni sched JLFP hrefl htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip jlp P hs hP
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  unfold cumulative_priority_inversion cumulative_priority_inversion_cond
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  unfold priority_inversion priority_inversion_cond
  congr 2
  apply any_congr_mem
  intro j' hj'
  cases hhep : JLFP.hep_job j' j
  · have hs' : scheduled_at sched j' t = true := by
      rw [← scheduled_jobs_at_iff arr_seq hva sched hvs.1 hmust j' t]; exact decide_eq_true hj'
    have hpi : priority_inversion arr_seq sched j t = true := by
      rw [priority_inversion_hep_job arr_seq hva sched hvs.1 hmust hrefl j huni t j' hs', hhep]; rfl
    have hs1 := pi_job_remains_scheduled arr_seq hva huni sched JLFP hrefl htrans hvpm hwb hvs hresp j ha
      hpos t1 t2 hbip t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hpi j' hs' t1
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    have heq := huni j' jlp sched t1 hs1 hs
    subst heq
    simp [hP]
  · simp

end CondPI

end Prosa.Analysis.Facts.BusyInterval.PiCond
