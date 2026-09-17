-- Translated from: ../rt-proofs/analysis/definitions/busy_interval.v
import Prosa.Model.Priority.Classes
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Model.Processor.Ideal

namespace Prosa.Analysis.Definitions.Busy_interval

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Priority.Classes
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Facts.Behavior.Completion

section BusyIntervalJLFP

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

variable (sched : schedule (processor_state Job))

variable [JLFP_policy Job]

section BusyInterval

variable (j : Job)
variable (H_from_arrival_sequence : arrives_in arr_seq j)

def quiet_time (t : instant) :=
  ∀ (j_hp : Job),
    arrives_in arr_seq j_hp →
    hep_job j_hp j = true →
    arrived_before j_hp t →
    completed_by sched j_hp t

def busy_interval_prefix (t1 t_busy : instant) :=
  t1 < t_busy ∧
  quiet_time arr_seq sched j t1 ∧
  (∀ t, t1 < t ∧ t < t_busy → ¬ quiet_time arr_seq sched j t) ∧
  t1 ≤ job_arrival j ∧ job_arrival j < t_busy

def busy_interval (t1 t2 : instant) :=
  busy_interval_prefix arr_seq sched j t1 t2 ∧
  quiet_time arr_seq sched j t2

end BusyInterval

section DecidableQuietTime

noncomputable def quiet_time_dec (j : Job) (t : instant) : Bool :=
  (arrivals_before arr_seq t).all
    (fun j_hp => !(hep_job j_hp j) || decide (service sched j_hp t ≥ job_cost j_hp))

include H_arrival_times_are_consistent in
lemma quiet_time_P :
    ∀ j t, quiet_time_dec arr_seq sched j t = true ↔
      quiet_time arr_seq sched j t := by
  intro j t
  constructor
  · -- → direction: quiet_time_dec → quiet_time
    intro hdec j_hp hArrives hHep hBefore
    unfold quiet_time_dec at hdec
    rw [List.all_eq_true] at hdec
    have hIn : j_hp ∈ arrivals_before arr_seq t :=
      Prosa.Analysis.Facts.Behavior.Arrivals.arrived_between_implies_in_arrivals
        arr_seq H_arrival_times_are_consistent j_hp 0 t hArrives ⟨Nat.zero_le _, hBefore⟩
    have h := hdec j_hp hIn
    rw [hHep, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h
    exact h
  · -- ← direction: quiet_time → quiet_time_dec
    intro hQT
    unfold quiet_time_dec
    rw [List.all_eq_true]
    intro j_hp hIn
    cases hHep : hep_job j_hp j with
    | false => rw [Bool.not_false, Bool.true_or]
    | true =>
      rw [Bool.not_true, Bool.false_or, decide_eq_true_eq]
      exact hQT j_hp
        (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived
          arr_seq H_arrival_times_are_consistent j_hp 0 t hIn)
        hHep
        (Prosa.Analysis.Facts.Behavior.Arrivals.in_arrivals_implies_arrived_before
          arr_seq H_arrival_times_are_consistent j_hp t hIn)

end DecidableQuietTime

end BusyIntervalJLFP

end Prosa.Analysis.Definitions.Busy_interval
