-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/apa/bertogna_fp_example.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 176)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Platform
import Prosa.Classic.Analysis.Apa.WorkloadBound
import Prosa.Classic.Analysis.Apa.InterferenceBoundFp
import Prosa.Classic.Analysis.Apa.BertognaFpComp
import Prosa.Classic.Implementation.Apa.Job
import Prosa.Classic.Implementation.Apa.Task
import Prosa.Classic.Implementation.Apa.Schedule
import Prosa.Classic.Implementation.Apa.ArrivalSequence

/-!
An APA FP response-time analysis example (Rocq module `ResponseTimeAnalysisFP` of
`classic/implementation/apa/bertogna_fp_example.v`).

Representation notes:
* The section-local `Let`s that define the concrete example (`cpu`, `alpha1`, `alpha2`, `alpha3`, `tsk1`, `tsk2`,
  `tsk3`, `ts`, `arr_seq`, `higher_priority`, `sched`) are kept as `LEAN_HELPER` definitions of the same names;
  `num_cpus := 2`, `schedulability_test` and `no_deadline_missed_by` are unfolded. `cpu j` is MathComp's
  `@Ordinal num_cpus j`, i.e. `⟨j, h⟩ : Fin 2` with the bound proof `h` as an explicit argument.
* The `Program` obligations are kept as theorems of the same names: the ordinal bounds `j < 2` (Rocq `j.+1 <= 2`)
  and the duplicate-freeness of the processor and task lists, all proved by `decide`.
* Concrete jobs and tasks use the accepted APA `ConcreteJob`/`ConcreteTask` records (parameterised by `num_cpus`).
  The task set is used as its underlying list `ts.val` where the Rocq source coerces it to a sequence. `#|A|` is
  `(Finset.univ.filter (fun x => x ∈ A)).card`, as in the accepted APA analysis. As in the Rocq source, the
  subaffinity `alpha'` is the affinity `task_affinity` itself.
* `schedulability_test_succeeds` is checked by `decide` (kernel evaluation of the fixed-point iteration; no
  `native_decide`; the elaborator's `maxRecDepth` is raised for that one theorem). The sortedness of `ts` by rate-monotonic priority, discharged by computation in the Rocq proof
  (`try (by done)`), is likewise checked by `decide`.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Implementation.Apa.BertognaFpExample.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule (schedule processor)
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability (task_misses_no_deadline)
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity (affinity)
open Prosa.Classic.Analysis.Apa.BertognaFpComp.ResponseTimeIterationFP
  (fp_schedulable taskset_schedulable_by_fp_rta)
open Prosa.Classic.Implementation.Apa.Job.ConcreteJob
open Prosa.Classic.Implementation.Apa.Task.ConcreteTask
open Prosa.Classic.Implementation.Apa.ArrivalSequence.ConcreteArrivalSequence
open Prosa.Classic.Implementation.Apa.Schedule.ConcreteScheduler

/-! ### The example (LEAN_HELPER definitions for the section `Let`s) -/

/-- LEAN_HELPER (Rocq `Let cpu j := @Ordinal num_cpus j`). -/
def cpu (j : Nat) (h : j < 2) : processor 2 := ⟨j, h⟩

theorem alpha1_obligation_1 : 0 < 2 := by decide
theorem alpha1_obligation_2 : 1 < 2 := by decide
theorem alpha1_obligation_3 : [cpu 0 alpha1_obligation_1, cpu 1 alpha1_obligation_2].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let alpha1 : affinity num_cpus := Build_set [:: cpu 0 _; cpu 1 _] _`). -/
def alpha1 : affinity 2 := ⟨[cpu 0 alpha1_obligation_1, cpu 1 alpha1_obligation_2], alpha1_obligation_3⟩

theorem alpha2_obligation_1 : 0 < 2 := by decide
theorem alpha2_obligation_2 : [cpu 0 alpha2_obligation_1].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let alpha2 : affinity num_cpus := Build_set [:: cpu 0 _] _`). -/
def alpha2 : affinity 2 := ⟨[cpu 0 alpha2_obligation_1], alpha2_obligation_2⟩

theorem alpha3_obligation_1 : 1 < 2 := by decide
theorem alpha3_obligation_2 : [cpu 1 alpha3_obligation_1].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let alpha3 : affinity num_cpus := Build_set [:: cpu 1 _] _`). -/
def alpha3 : affinity 2 := ⟨[cpu 1 alpha3_obligation_1], alpha3_obligation_2⟩

/-- LEAN_HELPER (Rocq `Let tsk1`). -/
def tsk1 : @concrete_task 2 :=
  { task_id := 1, task_cost := 3, task_period := 5, task_deadline := 3, task_affinity := alpha1 }
/-- LEAN_HELPER (Rocq `Let tsk2`). -/
def tsk2 : @concrete_task 2 :=
  { task_id := 2, task_cost := 2, task_period := 6, task_deadline := 5, task_affinity := alpha2 }
/-- LEAN_HELPER (Rocq `Let tsk3`). -/
def tsk3 : @concrete_task 2 :=
  { task_id := 3, task_cost := 2, task_period := 12, task_deadline := 11, task_affinity := alpha3 }

theorem ts_obligation_1 : [tsk1, tsk2, tsk3].Nodup := by decide

/-- LEAN_HELPER (Rocq `Program Let ts := Build_set [:: tsk1; tsk2; tsk3] _`). -/
def ts : concrete_taskset 2 := ⟨[tsk1, tsk2, tsk3], ts_obligation_1⟩

theorem ts_non_empty_affinities :
    ∀ tsk, tsk ∈ ts → 0 < (Finset.univ.filter (fun x => x ∈ concrete_task.task_affinity tsk)).card := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> decide

theorem ts_has_valid_parameters :
    valid_sporadic_taskset (concrete_task.task_cost (num_cpus := 2)) (concrete_task.task_period (num_cpus := 2))
      (concrete_task.task_deadline (num_cpus := 2)) ts.val := by
  intro tsk IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ts_has_constrained_deadlines :
    ∀ tsk, tsk ∈ ts → concrete_task.task_deadline tsk ≤ concrete_task.task_period tsk := by
  intro tsk IN
  change tsk ∈ ts.val at IN
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN
  rcases IN with rfl | rfl | rfl <;> decide

/-- LEAN_HELPER (Rocq `Let arr_seq`). -/
def arr_seq : arrival_sequence (@concrete_job 2) := periodic_arrival_sequence ts

/-- LEAN_HELPER (Rocq `Let higher_priority`). -/
def higher_priority : JLDP_policy (@concrete_job 2) :=
  FP_to_JLDP concrete_job.job_task (RM concrete_task.task_period)

theorem ts_has_unique_priorities :
    FP_is_antisymmetric_over_task_set (RM (concrete_task.task_period (num_cpus := 2))) ts.val := by
  intro tsk tsk' IN IN' HP HP'
  simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at IN IN'
  rcases IN with rfl | rfl | rfl <;> rcases IN' with rfl | rfl | rfl <;> first | rfl | (exfalso; revert HP HP'; decide)

theorem priority_is_total : FP_is_total_over_task_set (RM (concrete_task.task_period (num_cpus := 2))) ts.val := by
  intro tsk tsk' _ _
  rcases Nat.le_total tsk.task_period tsk'.task_period with h | h
  · left; simp [RM, h]
  · right; simp [RM, h]

set_option maxRecDepth 100000 in
theorem schedulability_test_succeeds :
    fp_schedulable concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline 2
      (RM concrete_task.task_period) concrete_task.task_affinity concrete_task.task_affinity ts.val = true := by
  decide

/-- LEAN_HELPER (Rocq `Let sched`, with `num_cpus := 2`). -/
def sched : schedule (@concrete_job 2) 2 :=
  scheduler concrete_job.job_arrival concrete_job.job_cost concrete_job.job_task 2 arr_seq concrete_task.task_affinity
    higher_priority

theorem ts_is_schedulable :
    ∀ tsk, tsk ∈ ts →
      task_misses_no_deadline concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline
        concrete_job.job_task arr_seq sched tsk := by
  intro tsk IN
  have CONS := periodic_arrivals_are_consistent ts
  have SET := periodic_arrivals_is_a_set ts ts_has_valid_parameters
  have TRANS : JLDP_is_transitive higher_priority :=
    fun t y x z h1 h2 => RM_is_transitive concrete_task.task_period _ _ _ h1 h2
  have TOTAL : ∀ t, ∀ x y, (higher_priority t x y || higher_priority t y x) = true := by
    intro t j1 j2
    rcases Nat.le_total j1.job_task.task_period j2.job_task.task_period with h | h
    · simp [higher_priority, FP_to_JLDP, FP_to_JLFP, RM, h]
    · simp [higher_priority, FP_to_JLDP, FP_to_JLFP, RM, h]
  exact taskset_schedulable_by_fp_rta concrete_task.task_cost concrete_task.task_period concrete_task.task_deadline
    concrete_job.job_arrival concrete_job.job_cost concrete_job.job_deadline concrete_job.job_task 2
    (RM concrete_task.task_period) concrete_task.task_affinity concrete_task.task_affinity ts
    ts_has_valid_parameters ts_has_constrained_deadlines ts_non_empty_affinities (fun _ _ _ hx => hx) (by decide)
    ts_has_unique_priorities priority_is_total (RM_is_transitive _) arr_seq
    (periodic_arrivals_all_jobs_from_taskset ts)
    (periodic_arrivals_valid_job_parameters ts ts_has_valid_parameters) (periodic_arrivals_are_sporadic ts)
    sched
    (scheduler_jobs_come_from_arrival_sequence _ _ _ _ _ _ _)
    (scheduler_jobs_must_arrive_to_execute _ _ _ _ _ _ _)
    (scheduler_completed_jobs_dont_execute _ _ _ _ _ _ CONS SET _)
    (scheduler_sequential_jobs _ _ _ _ _ _ CONS SET _)
    (scheduler_respects_affinity _ _ _ _ _ _ _)
    (scheduler_apa_work_conserving _ _ _ _ _ _ CONS SET higher_priority TRANS TOTAL)
    (scheduler_respects_policy _ _ _ _ _ _ CONS SET higher_priority TRANS TOTAL)
    schedulability_test_succeeds tsk IN

end Prosa.Classic.Implementation.Apa.BertognaFpExample.ResponseTimeAnalysisFP
