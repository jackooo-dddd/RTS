-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/busy_interval/classical.v

import Prosa.Model.Priority.Classes
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Analysis.Definitions.BusyInterval.Classical

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Facts.Behavior.Arrivals

/-! Representation notes: a Boolean in `Prop` position is `= true`; a single
comparison `a < b` in `Prop` position is the Lean proposition; a chained
`a < b < c` is `(decide (a < b) && decide (b < c)) = true`; `~ P` is `¬ P`;
`a ==> b` is `!a || b`; `all p s` is `s.all p`; the source `reflect` view is
the informative `BoolReflect` family below (as in the accepted implementation
translations). Binder orders follow the elaborated types. -/

/-- LEAN_HELPER: informative reflection, preserving the source `reflect`
truth index (the same shape as the accepted implementation translations). -/
inductive BoolReflect (P : Prop) : Bool → Type where
  | isTrue : P → BoolReflect P true
  | isFalse : ¬ P → BoolReflect P false

section BusyIntervalJLFP

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable [JLFP_policy Job]

/-- `t` is a quiet time for `j`: every higher-or-equal-priority job that
arrived before `t` has completed by `t`. -/
def quiet_time (j : Job) (t : instant) : Prop :=
  ∀ j_hp : Job, arrives_in arr_seq j_hp → hep_job j_hp j = true →
    arrived_before j_hp t = true → completed_by sched j_hp t = true

/-- `[t1, t_busy)` is a busy-interval prefix for `j`. -/
def busy_interval_prefix (j : Job) (t1 t_busy : instant) : Prop :=
  t1 < t_busy ∧
  quiet_time arr_seq sched j t1 ∧
  (∀ t, (decide (t1 < t) && decide (t < t_busy)) = true → ¬ quiet_time arr_seq sched j t) ∧
  (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t_busy)) = true

/-- `[t1, t2)` is a busy interval for `j`. -/
def busy_interval (j : Job) (t1 t2 : instant) : Prop :=
  busy_interval_prefix arr_seq sched j t1 t2 ∧ quiet_time arr_seq sched j t2

end BusyIntervalJLFP

/-- Decidable quiet time over the arrivals before `t`. -/
noncomputable def quiet_time_dec {Job : JobType} [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t : instant) : Bool :=
  (arrivals_before arr_seq t).all (fun j_hp => !hep_job j_hp j || completed_by sched j_hp t)

theorem quiet_time_iff {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (hc : consistent_arrival_times arr_seq) (sched : schedule PState) [JLFP_policy Job]
    (j : Job) (t : instant) :
    quiet_time arr_seq sched j t ↔ quiet_time_dec arr_seq sched j t = true := by
  constructor
  · intro qt
    unfold quiet_time_dec
    rw [List.all_eq_true]
    intro s hs
    have hsd : decide (s ∈ arrivals_between arr_seq 0 t) = true := decide_eq_true hs
    have ha := in_arrivals_implies_arrived arr_seq s 0 t hsd
    have hb := in_arrivals_implies_arrived_between arr_seq hc s 0 t hsd
    cases hhep : hep_job s j
    · rfl
    · have hbef : arrived_before s t = true := by
        simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at hb
        exact decide_eq_true hb.2
      simp [qt s ha hhep hbef]
  · intro h s ha hhep hbef
    unfold quiet_time_dec at h
    rw [List.all_eq_true] at h
    have hbt : arrived_between s 0 t = true := by
      simp only [arrived_before, decide_eq_true_eq] at hbef
      simp [arrived_between, hbef]
    have hin := arrived_between_implies_in_arrivals arr_seq hc s 0 t ha hbt
    have := h s (of_decide_eq_true hin)
    simpa [hhep] using this

/-- The quiet-time predicate is reflected by its decision procedure. -/
noncomputable def quiet_time_P {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (sched : schedule PState) [JLFP_policy Job] (j : Job) (t : instant),
        BoolReflect (quiet_time arr_seq sched j t) (quiet_time_dec arr_seq sched j t) := by
  intro hc sched _ j t
  cases hd : quiet_time_dec arr_seq sched j t
  · exact BoolReflect.isFalse (fun q => by
      have := (quiet_time_iff arr_seq hc sched j t).mp q
      rw [hd] at this; exact Bool.false_ne_true this)
  · exact BoolReflect.isTrue ((quiet_time_iff arr_seq hc sched j t).mpr hd)

end Prosa.Analysis.Definitions.BusyInterval.Classical
