-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/apa/interference.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 33)

import Prosa.Util.Sum
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity

/-!
Interference under processor affinities (APA; Rocq module `Interference` of
`classic/model/schedule/apa`).  As the global version, plus the affinity
condition `can_execute_on alpha (job_task j) cpu` in each per-processor term
(`a && b && c` is `(a && b) && c`).

Representation notes: a Boolean summed as a number (MathComp `nat_of_bool`) is
`Bool.toNat`; `\sum_(t1 <= t < t2)` is `∑ t ∈ Finset.Ico t1 t2`;
`\sum_(cpu < num_cpus)` is `∑ cpu : Fin num_cpus`; the filtered list sum
`\sum_(j <- l | P j) F j` is the v0.6 `Prosa.Util.Sum.sumFiltered l P F`.  The
section-local `job_is_backlogged t := backlogged job_arrival job_cost sched j t`
is unfolded.  Binder lists follow the Rocq contract.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Apa.Interference.Interference

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Util.Sum (sumFiltered)
open Prosa.Classic.Model.Priority.Priority (FP_policy)
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open BigOperators

universe u v

/-! ### Possibly interfering tasks -/

def higher_priority_task_in {sporadic_task : Type u} [DecidableEq sporadic_task]
    {num_cpus : Nat} (alpha : task_affinity sporadic_task num_cpus)
    (higher_eq_priority : FP_policy sporadic_task) (tsk : sporadic_task)
    (alpha' : affinity num_cpus) (tsk_other : sporadic_task) : Bool :=
  higher_eq_priority tsk_other tsk && !decide (tsk_other = tsk) &&
    affinity_intersects alpha' (alpha tsk_other)

def different_task_in {sporadic_task : Type u} [DecidableEq sporadic_task] {num_cpus : Nat}
    (alpha : task_affinity sporadic_task num_cpus) (tsk : sporadic_task)
    (alpha' : affinity num_cpus) (tsk_other : sporadic_task) : Bool :=
  !decide (tsk_other = tsk) && affinity_intersects alpha' (alpha tsk_other)

/-! ### Interference -/

def total_interference {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (j : Job) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (backlogged job_arrival job_cost sched j t).toNat

def job_interference {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (j job_other : Job) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, ∑ cpu : Fin num_cpus,
    (backlogged job_arrival job_cost sched j t && can_execute_on alpha (job_task j) cpu &&
      scheduled_on sched job_other cpu t).toNat

def task_interference {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (j : Job) (tsk_other : sporadic_task)
    (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, ∑ cpu : Fin num_cpus,
    (backlogged job_arrival job_cost sched j t && can_execute_on alpha (job_task j) cpu &&
      task_scheduled_on job_task sched tsk_other cpu t).toNat

def task_interference_joblist {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (j : Job) (tsk_other : sporadic_task)
    (t1 t2 : time) : Nat :=
  sumFiltered (jobs_scheduled_between sched t1 t2) (fun j' => decide (job_task j' = tsk_other))
    (fun j' => job_interference job_arrival job_cost job_task sched alpha j j' t1 t2)

/-! ### Basic lemmas -/

theorem total_interference_le_delta {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (j : Job) :
    ∀ t1 t2 : time, total_interference job_arrival job_cost sched j t1 t2 ≤ t2 - t1 := by
  intro t1 t2
  unfold total_interference
  calc ∑ t ∈ Finset.Ico t1 t2, (backlogged job_arrival job_cost sched j t).toNat
      ≤ ∑ _t ∈ Finset.Ico t1 t2, 1 := Finset.sum_le_sum fun t _ => Bool.toNat_le _
    _ = t2 - t1 := by simp

/-- LEAN_HELPER: service at `t` as a sum over all processors. -/
private theorem service_at_eq_sum {Job : Type v} [DecidableEq Job] {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) (t : time) :
    service_at sched j t = ∑ cpu : Fin num_cpus, (scheduled_on sched j cpu t).toNat := by
  unfold service_at
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro cpu _
  cases scheduled_on sched j cpu t <;> rfl

theorem job_interference_le_service {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (j : Job) :
    ∀ (j_other : Job) (t1 t2 : time),
      job_interference job_arrival job_cost job_task sched alpha j j_other t1 t2 ≤
        service_during sched j_other t1 t2 := by
  intro j_other t1 t2
  unfold job_interference service_during
  apply Finset.sum_le_sum
  intro t _
  rw [service_at_eq_sum]
  apply Finset.sum_le_sum
  intro cpu _
  cases backlogged job_arrival job_cost sched j t <;>
    cases can_execute_on alpha (job_task j) cpu <;>
    cases scheduled_on sched j_other cpu t <;> simp

theorem task_interference_le_workload {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (j : Job) :
    ∀ (tsk : sporadic_task) (t1 t2 : time),
      task_interference job_arrival job_cost job_task sched alpha j tsk t1 t2 ≤
        workload job_task sched tsk t1 t2 := by
  intro tsk t1 t2
  unfold task_interference workload
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro cpu _
  unfold task_scheduled_on service_of_task
  cases backlogged job_arrival job_cost sched j t <;>
    cases can_execute_on alpha (job_task j) cpu <;> cases sched cpu t <;> simp

theorem job_interference_le_delta {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (j : Job)
    (H_sequential_jobs : sequential_jobs sched) :
    ∀ (j_other : Job) (t1 delta : time),
      job_interference job_arrival job_cost job_task sched alpha j j_other t1 (t1 + delta) ≤
        delta := by
  intro j_other t1 delta
  unfold job_interference
  calc ∑ t ∈ Finset.Ico t1 (t1 + delta), ∑ cpu : Fin num_cpus,
        (backlogged job_arrival job_cost sched j t && can_execute_on alpha (job_task j) cpu &&
          scheduled_on sched j_other cpu t).toNat
      ≤ ∑ _t ∈ Finset.Ico t1 (t1 + delta), 1 := by
        apply Finset.sum_le_sum
        intro t _
        calc ∑ cpu : Fin num_cpus,
              (backlogged job_arrival job_cost sched j t && can_execute_on alpha (job_task j) cpu &&
                scheduled_on sched j_other cpu t).toNat
            ≤ ∑ cpu : Fin num_cpus, (scheduled_on sched j_other cpu t).toNat := by
              apply Finset.sum_le_sum
              intro cpu _
              cases backlogged job_arrival job_cost sched j t <;>
                cases can_execute_on alpha (job_task j) cpu <;>
                cases scheduled_on sched j_other cpu t <;> simp
          _ = service_at sched j_other t := (service_at_eq_sum sched j_other t).symm
          _ ≤ 1 := service_at_most_one sched j_other H_sequential_jobs t
    _ = delta := by simp

/-! ### Per-task interference bounded by per-job interference -/

theorem interference_le_interference_joblist {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (alpha : task_affinity sporadic_task num_cpus) (j : Job) :
    ∀ (tsk : sporadic_task) (t1 t2 : time),
      task_interference job_arrival job_cost job_task sched alpha j tsk t1 t2 ≤
        task_interference_joblist job_arrival job_cost job_task sched alpha j tsk t1 t2 := by
  intro tsk t1 t2
  set L := (jobs_scheduled_between sched t1 t2).filter (fun j' => decide (job_task j' = tsk))
    with hL
  have hnd : L.Nodup := (List.nodup_dedup _).filter _
  unfold task_interference task_interference_joblist sumFiltered job_interference
  rw [← hL, ← List.sum_toFinset _ hnd]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mem_Ico] at ht
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro cpu _
  unfold task_scheduled_on
  cases hb : backlogged job_arrival job_cost sched j t with
  | false => simp
  | true =>
    cases hc : can_execute_on alpha (job_task j) cpu with
    | false => simp
    | true =>
      cases hs : sched cpu t with
      | none => simp
      | some j' =>
          by_cases htsk : job_task j' = tsk
          · have hmem : j' ∈ L.toFinset := by
              rw [List.mem_toFinset, hL, List.mem_filter, jobs_scheduled_between, List.mem_dedup]
              refine ⟨?_, by simpa using htsk⟩
              apply Prosa.Util.Bigcat.mem_bigcat_nat _ j' t1 t2 t ht
              have hsch : scheduled sched j' t = true := by
                simp only [scheduled, scheduled_on, List.any_eq_true, List.mem_finRange,
                  true_and, decide_eq_true_eq]
                exact ⟨cpu, hs⟩
              have := mem_scheduled_jobs_eq_scheduled sched j' t
              rw [hsch] at this
              simpa using this
            have hle := Finset.single_le_sum
              (f := fun x => (true && true && scheduled_on sched x cpu t).toNat)
              (fun _ _ => Nat.zero_le _) hmem
            simp only [Bool.true_and, scheduled_on, hs, decide_true, Bool.toNat_true] at hle
            simpa [htsk, scheduled_on, hs] using hle
          · simp [htsk]

end Prosa.Classic.Model.Schedule.Apa.Interference.Interference
