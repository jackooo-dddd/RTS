-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/periodic_as_sporadic.v

import Prosa.Model.Task.Arrival.Periodic
import Prosa.Model.Task.Arrival.Sporadic
import Prosa.Analysis.Facts.JobIndex

namespace Prosa.Model.Task.Arrival.PeriodicAsSporadic

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Periodic
open Prosa.Model.Task.Arrival.Sporadic
open Prosa.Analysis.Facts.JobIndex

/-! Representation notes: the source's global instance is a Lean `instance`
with the same name; the statements find it by instance resolution, as the
elaborated source types do. `TaskSet Task` is the accepted `List Task`.
Binder orders follow the elaborated types. -/

/-- A periodic task is a sporadic task whose minimum inter-arrival time is its
period. -/
instance periodic_as_sporadic {Task : TaskType} [DecidableEq Task] [PeriodicModel Task] :
    SporadicModel Task :=
  ⟨task_period⟩

/-- A valid period is a valid minimum inter-arrival time. -/
theorem valid_period_is_valid_inter_arrival_time {Task : TaskType} [DecidableEq Task]
    [PeriodicModel Task] :
    ∀ tsk : Task, valid_period tsk = true → valid_task_min_inter_arrival_time tsk = true :=
  fun _ h => h

/-- A periodic task respects the sporadic task model. -/
theorem periodic_task_respects_sporadic_task_model {Task : TaskType} [DecidableEq Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ tsk : Task, valid_period tsk = true → respects_periodic_task_model arr_seq tsk →
        respects_sporadic_task_model arr_seq tsk := by
  intro hva tsk hvp hper j1 j2 hne h1 h2 htsk1 htsk2 harr
  show job_arrival j1 + task_period tsk ≤ job_arrival j2
  have hpos : 0 < task_period tsk := of_decide_eq_true hvp
  have htsk : job_task (Task := Task) j1 = job_task (Task := Task) j2 := htsk1.trans htsk2.symm
  have hidx_ne := (diff_jobs_iff_diff_indices (Task := Task) arr_seq hva j1 j2 h1 h2 htsk).mp hne
  have hlt : job_index (Task := Task) arr_seq j1 < job_index (Task := Task) arr_seq j2 := by
    by_contra hge
    have hgt : job_index (Task := Task) arr_seq j2 < job_index (Task := Task) arr_seq j1 := by
      omega
    obtain ⟨pj, hpj, hidx, htpj, hapj⟩ := hper j1 h1 (by omega) htsk1
    have hle : job_index (Task := Task) arr_seq j2 ≤ job_index (Task := Task) arr_seq pj := by
      omega
    have := index_lte_implies_arrival_lte (Task := Task) arr_seq hva pj j2 hpj h2
      (htpj.trans htsk2.symm) hle
    dsimp only [instant, duration] at *
    omega
  obtain ⟨pj, hpj, hidx, htpj, hapj⟩ := hper j2 h2 (by omega) htsk2
  have hle : job_index (Task := Task) arr_seq j1 ≤ job_index (Task := Task) arr_seq pj := by
    omega
  have := index_lte_implies_arrival_lte (Task := Task) arr_seq hva pj j1 hpj h1
    (htpj.trans htsk1.symm) hle
  dsimp only [instant, duration] at *
  omega

/-- A task set with valid periods has valid minimum inter-arrival times. -/
theorem valid_periods_are_valid_inter_arrival_times {Task : TaskType} [DecidableEq Task]
    [PeriodicModel Task] :
    ∀ ts : TaskSet Task, valid_periods ts → valid_taskset_inter_arrival_times ts :=
  fun _ h => h

/-- A periodic task set respects the sporadic task model. -/
theorem periodic_task_sets_respect_sporadic_task_model {Task : TaskType} [DecidableEq Task]
    [PeriodicModel Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      ∀ ts : TaskSet Task, valid_periods ts → taskset_respects_periodic_task_model arr_seq ts →
        taskset_respects_sporadic_task_model ts arr_seq := by
  intro hva ts hvp hper tsk hin
  exact periodic_task_respects_sporadic_task_model arr_seq hva tsk (hvp tsk hin) (hper tsk hin)

end Prosa.Model.Task.Arrival.PeriodicAsSporadic
