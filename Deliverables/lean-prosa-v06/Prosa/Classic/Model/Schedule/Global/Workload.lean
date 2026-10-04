-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/workload.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 32)

import Prosa.Util.Sum
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule

/-!
Workload of a task (Rocq module `Workload`).

Representation notes: `(job_task j' == tsk)` used as a number is
`(decide (job_task j' = tsk)).toNat` (MathComp's `nat_of_bool`);
`\sum_(cpu < num_cpus) F cpu` is `∑ cpu : Fin num_cpus, F cpu`;
`\sum_(j <- l) F j` is the accepted v0.6 `Prosa.Util.Sum.sumSeq l F`.
Binder lists follow the Rocq contract (`service_of_task` takes `cpu` although
its body does not use it, as in the source).
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Global.Workload.Workload

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Util.Sum (sumSeq)
open Prosa.Util.Notation (bigCat)
open BigOperators

universe u v

def service_of_task {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat} (tsk : sporadic_task)
    (_cpu : processor num_cpus) (scheduled_job : Option Job) : time :=
  match scheduled_job with
  | some j' => (decide (job_task j' = tsk)).toNat
  | none => 0

def workload {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, ∑ cpu : Fin num_cpus, service_of_task job_task tsk cpu (sched cpu t)

def workload_joblist {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_task : Job → sporadic_task) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 t2 : time) : Nat :=
  sumSeq (jobs_of_task_scheduled_between job_task sched tsk t1 t2)
    (fun j => service_during sched j t1 t2)

theorem workload_eq_workload_joblist {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) :
    ∀ t1 t2 : time,
      workload job_task sched tsk t1 t2 = workload_joblist job_task sched tsk t1 t2 := by
  intro t1 t2
  set L := jobs_of_task_scheduled_between job_task sched tsk t1 t2 with hL
  have hnd : L.Nodup := (List.nodup_dedup _).filter _
  -- a job scheduled in the interval is in the job list iff it belongs to `tsk`
  have hmem : ∀ t, t1 ≤ t → t < t2 → ∀ (cpu : Fin num_cpus) (j0 : Job),
      sched cpu t = some j0 → (j0 ∈ L ↔ job_task j0 = tsk) := by
    intro t ht1 ht2 cpu j0 hs
    simp only [hL, jobs_of_task_scheduled_between, jobs_scheduled_between, List.mem_filter,
      List.mem_dedup, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      apply Prosa.Util.Bigcat.mem_bigcat_nat _ j0 t1 t2 t ⟨ht1, ht2⟩
      have hsch : scheduled sched j0 t = true := by
        simp only [scheduled, scheduled_on, List.any_eq_true, List.mem_finRange, true_and,
          decide_eq_true_eq]
        exact ⟨cpu, hs⟩
      have := mem_scheduled_jobs_eq_scheduled sched j0 t
      rw [hsch] at this
      simpa using this
  unfold workload workload_joblist sumSeq
  rw [← List.sum_toFinset _ hnd]
  simp only [service_during, service_at, Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cpu _
  unfold service_of_task scheduled_on
  cases hs : sched cpu t with
  | none => simp
  | some j0 =>
      simp only [Option.some.injEq, decide_eq_true_eq]
      rw [Finset.sum_ite_eq]
      have := hmem t ht.1 ht.2 cpu j0 hs
      by_cases h : job_task j0 = tsk
      · simp [h, List.mem_toFinset, this.mpr h]
      · have hn : j0 ∉ L := fun hm => h (this.mp hm)
        simp [h, List.mem_toFinset, hn]

end Prosa.Classic.Model.Schedule.Global.Workload.Workload
