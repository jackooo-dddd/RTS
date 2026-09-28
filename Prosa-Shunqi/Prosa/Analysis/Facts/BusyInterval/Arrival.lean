-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/arrival.v

import Prosa.Analysis.Definitions.BusyInterval.Classical
import Prosa.Analysis.Facts.BusyInterval.HepAtPt

namespace Prosa.Analysis.Facts.BusyInterval.Arrival

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.BusyInterval.Existence

/-! Arrival times within busy intervals.
Binders follow the elaborated source types. Representation: a Boolean in
`Prop` position is `= true`. The source's `Global Hint Resolve` registration
of the two basic facts is proof automation only and has no Lean counterpart. -/

section BasicFacts

variable {Job : JobType} [DecidableEq Job]

/-- A job arrives after the start of its busy-interval prefix. -/
theorem busy_interval_prefix_job_arrival [JobArrival Job] [JobCost Job] [JLFP_policy Job]
    {PState : ProcessorState Job} (sched : schedule PState) (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t t' : instant), busy_interval_prefix arr_seq sched j t t' → t ≤ job_arrival j := by
  intro j t t' hbip
  have h := hbip.2.2.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- A job arrives after the start of its busy interval. -/
theorem busy_interval_job_arrival [JobArrival Job] [JobCost Job] [JLFP_policy Job]
    {PState : ProcessorState Job} (sched : schedule PState) (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t t' : instant), busy_interval arr_seq sched j t t' → t ≤ job_arrival j :=
  fun j t t' hbi => busy_interval_prefix_job_arrival sched arr_seq j t t' hbi.1

end BasicFacts

section Facts

variable {Job : JobType} [DecidableEq Job]

/-- A busy-interval prefix starts with the arrival of a higher-or-equal-priority
job. -/
theorem busy_prefix_starts_when_hep_job_arrives [JobArrival Job] [JobCost Job]
    (JLFP : JLFP_policy Job) :
    reflexive_job_priorities JLFP →
    ∀ {PState : ProcessorState Job} (arr_seq : arrival_sequence Job), valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState, jobs_must_arrive_to_execute sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
      ∃ j_a : Job, arrives_at arr_seq j_a t1 = true ∧ JLFP.hep_job j_a j = true := by
  intro hrefl PState arr_seq hva sched hmust j ha hpos t1 t2 hbip
  have hlt := hbip.1
  obtain ⟨jh, harr, hpend, hhep⟩ := pending_hp_job_exists arr_seq hva sched hmust JLFP j ha hpos hrefl
    t1 t2 hbip t1 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  refine ⟨jh, ?_, hhep⟩
  unfold pending has_arrived at hpend
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpend
  apply job_in_arrivals_at arr_seq hva.1 jh t1 harr
  by_contra hne
  have hq := hbip.2.1 jh harr hhep (by simp only [arrived_before, decide_eq_true_eq]; omega')
  rw [hq] at hpend
  exact absurd hpend.2 (by decide)

end Facts

end Prosa.Analysis.Facts.BusyInterval.Arrival
