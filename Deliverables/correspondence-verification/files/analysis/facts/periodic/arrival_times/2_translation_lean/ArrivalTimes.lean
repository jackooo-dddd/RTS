-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/periodic/arrival_times.v

import Prosa.Model.Task.Arrival.Periodic
import Prosa.Analysis.Facts.Model.Offset

namespace Prosa.Analysis.Facts.Periodic.ArrivalTimes

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Offset
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Analysis.Facts.Model.Offset

/-! Arrival times of the jobs of a periodic task with an offset. Binders follow
the elaborated source types. Representation: a Boolean in `Prop` position is
`= true`. The source's proof-only imports of `periodic_as_sporadic` and
`periodic/max_inter_arrival` are not needed by these statements or proofs. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

theorem periodic_arrival_times {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk →
        ∀ (n : Nat) (j : Job), arrives_in arr_seq j → job_task (Task := Task) j = tsk →
          job_index (Task := Task) arr_seq j = n →
          job_arrival j = task_offset tsk + n * task_period tsk := by
  intro hva tsk hvo _ hper n
  induction n with
  | zero =>
      intro j harr htsk hidx
      rw [Nat.zero_mul, Nat.add_zero]
      exact first_job_arrival arr_seq hva tsk j htsk hvo harr hidx
  | succ n ih =>
      intro j harr htsk hidx
      obtain ⟨pj, hpj, hpidx, htpj, hja⟩ := hper j harr (by omega) htsk
      have := ih pj hpj htpj (by omega)
      rw [hja, this, Nat.succ_mul]
      omega'

theorem job_arrival_times {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk →
        ∀ j : Job, arrives_in arr_seq j → job_task (Task := Task) j = tsk →
          ∃ n : Nat, job_arrival j = task_offset tsk + n * task_period tsk := by
  intro hva tsk hvo hvp hper j harr htsk
  exact ⟨job_index (Task := Task) arr_seq j,
    periodic_arrival_times arr_seq hva tsk hvo hvp hper _ j harr htsk rfl⟩

theorem job_arr_index {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_offset arr_seq tsk → valid_period tsk = true →
        respects_periodic_task_model arr_seq tsk →
        ∀ (n : Nat) (j : Job), arrives_in arr_seq j → job_task (Task := Task) j = tsk →
          job_arrival j = task_offset tsk + n * task_period tsk →
          job_index (Task := Task) arr_seq j = n := by
  intro hva tsk hvo hvp hper n
  have hp : 0 < task_period tsk := of_decide_eq_true hvp
  induction n with
  | zero =>
      intro j harr htsk harrj
      rcases Nat.eq_zero_or_pos (job_index (Task := Task) arr_seq j) with h0 | hpos
      · exact h0
      · have := periodic_arrival_times arr_seq hva tsk hvo hvp hper _ j harr htsk rfl
        rw [harrj] at this
        have : 0 < job_index (Task := Task) arr_seq j * task_period tsk := Nat.mul_pos hpos hp
        omega'
  | succ n ih =>
      intro j harr htsk harrj
      have hpos : 0 < job_index (Task := Task) arr_seq j := by
        rcases Nat.eq_zero_or_pos (job_index (Task := Task) arr_seq j) with h0 | hpos
        · have := first_job_arrival arr_seq hva tsk j htsk hvo harr h0
          rw [Nat.succ_mul] at harrj
          omega'
        · exact hpos
      obtain ⟨j', harr', hidx', htsk', hja⟩ := hper j harr hpos htsk
      have hj' := ih j' harr' htsk' (by rw [Nat.succ_mul] at harrj; omega')
      omega

end Prosa.Analysis.Facts.Periodic.ArrivalTimes
