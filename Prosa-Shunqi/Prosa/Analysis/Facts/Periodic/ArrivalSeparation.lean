-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/periodic/arrival_separation.v

import Prosa.Model.Task.Arrival.PeriodicAsSporadic
import Prosa.Analysis.Facts.Sporadic.ArrivalTimes

namespace Prosa.Analysis.Facts.Periodic.ArrivalSeparation

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Model.Task.Arrival.PeriodicAsSporadic
open Prosa.Analysis.Facts.JobIndex
open Prosa.Analysis.Facts.Sporadic.ArrivalTimes

/-! Arrival separation of the jobs of a periodic task. Binders follow the
elaborated source types. Representation: a Boolean in `Prop` position is
`= true`; `n > 0` is `0 < n`; the sporadic facts are used through the accepted
`periodic_as_sporadic` instance, as in the source. -/

macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

theorem consecutive_job_separation {Task : TaskType} [DecidableEq Task] [PeriodicModel Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_periodic_task_model arr_seq tsk → valid_period tsk = true →
        ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
          job_task (Task := Task) j1 = tsk → job_task (Task := Task) j2 = tsk →
          job_index (Task := Task) arr_seq j2 = job_index (Task := Task) arr_seq j1 + 1 →
          job_arrival j2 = job_arrival j1 + task_period tsk := by
  intro hva tsk hper _ j1 j2 h1 h2 ht1 ht2 hidx
  obtain ⟨pj, hpj, hpidx, htpj, hapj⟩ := hper j2 h2 (by omega) ht2
  have heq : pj = j1 :=
    equal_index_implies_equal_jobs (Task := Task) arr_seq hva pj j1 hpj h1 (htpj.trans ht1.symm)
      (by omega)
  rw [heq] at hapj
  exact hapj

theorem job_arrival_separation_when_index_diff_is_k {Task : TaskType} [DecidableEq Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_periodic_task_model arr_seq tsk → valid_period tsk = true →
        ∀ j1 j2 : Job, arrives_in arr_seq j1 → arrives_in arr_seq j2 →
          job_task (Task := Task) j1 = tsk → job_task (Task := Task) j2 = tsk →
          ∀ k : Nat, job_index (Task := Task) arr_seq j1 + k = job_index (Task := Task) arr_seq j2 →
            job_arrival j1 < job_arrival j2 →
            ∃ n : Nat, 0 < n ∧ job_arrival j2 = job_arrival j1 + n * task_period tsk := by
  intro hva tsk hper hvalid j1 j2 h1 h2 ht1 ht2 k
  have hsp := periodic_task_respects_sporadic_task_model arr_seq hva tsk hvalid hper
  have hvs := valid_period_is_valid_inter_arrival_time tsk hvalid
  induction k generalizing j1 with
  | zero =>
      intro hidx hlt
      have heq : j1 = j2 :=
        equal_index_implies_equal_jobs (Task := Task) arr_seq hva j1 j2 h1 h2 (ht1.trans ht2.symm)
          (by omega)
      rw [heq] at hlt
      exact absurd hlt (Nat.lt_irrefl _)
  | succ s ih =>
      intro hidx hlt
      by_cases hs : s = 0
      · subst hs
        exact ⟨1, Nat.one_pos, by
          rw [Nat.one_mul]
          exact consecutive_job_separation arr_seq hva tsk hper hvalid j1 j2 h1 h2 ht1 ht2
            (by omega)⟩
      · obtain ⟨nj, _, htnj, hnj, hidxnj⟩ :=
          exists_jobs_before_j (Task := Task) arr_seq hva j2 h2
            (job_index (Task := Task) arr_seq j1 + 1) (by omega)
        have htnj' : job_task (Task := Task) nj = tsk := htnj.trans ht2
        have hsep := consecutive_job_separation arr_seq hva tsk hper hvalid j1 nj h1 hnj ht1 htnj'
          hidxnj
        have hltnj : job_arrival nj < job_arrival j2 :=
          lower_index_implies_earlier_arrival arr_seq hva tsk hsp hvs nj j2 hnj h2 htnj' ht2
            (by omega)
        obtain ⟨n, hn, hn2⟩ := ih nj hnj htnj' (by omega) hltnj
        refine ⟨n + 1, Nat.succ_pos n, ?_⟩
        rw [hn2, hsep, Nat.succ_mul]
        omega'

theorem job_sep_periodic {Task : TaskType} [DecidableEq Task] [PeriodicModel Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, respects_periodic_task_model arr_seq tsk → valid_period tsk = true →
        ∀ j1 j2 : Job, j1 ≠ j2 → arrives_in arr_seq j1 → arrives_in arr_seq j2 →
          job_task (Task := Task) j1 = tsk → job_task (Task := Task) j2 = tsk →
          job_arrival j1 ≤ job_arrival j2 →
          ∃ n : Nat, 0 < n ∧ job_arrival j2 = job_arrival j1 + n * task_period tsk := by
  intro hva tsk hper hvalid j1 j2 hne h1 h2 ht1 ht2 hle
  have hsp := periodic_task_respects_sporadic_task_model arr_seq hva tsk hvalid hper
  have hvs := valid_period_is_valid_inter_arrival_time tsk hvalid
  have hidx : job_index (Task := Task) arr_seq j1 < job_index (Task := Task) arr_seq j2 := by
    rcases Nat.lt_trichotomy (job_index (Task := Task) arr_seq j1)
        (job_index (Task := Task) arr_seq j2) with hlt | heq | hgt
    · exact hlt
    · exact absurd (equal_index_implies_equal_jobs (Task := Task) arr_seq hva j1 j2 h1 h2
        (ht1.trans ht2.symm) heq) hne
    · have := lower_index_implies_earlier_arrival arr_seq hva tsk hsp hvs j2 j1 h2 h1 ht2 ht1 hgt
      omega'
  have hlt := lower_index_implies_earlier_arrival arr_seq hva tsk hsp hvs j1 j2 h1 h2 ht1 ht2 hidx
  exact job_arrival_separation_when_index_diff_is_k arr_seq hva tsk hper hvalid j1 j2 h1 h2 ht1 ht2
    (job_index (Task := Task) arr_seq j2 - job_index (Task := Task) arr_seq j1) (by omega) hlt

end Prosa.Analysis.Facts.Periodic.ArrivalSeparation
