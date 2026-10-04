-- Case study 2007-RTSS-Theorem2: Bertogna, Cirinei — Response-Time Analysis for Globally Scheduled Symmetric Multiprocessor Platforms (RTSS 2007).
-- Original Rocq statement: RTS_Papers/2007-RTSS-Theorem2/Theorem2.v.
-- Benchmark file: read-only.  Prove `CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP.theorem_2_statement` in `Solutions/RTSS2007/Theorem2.lean`.
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Interference

/-!
Theorem 2 of RTSS 2007: the interference that a task causes on a job is bounded by the task's
workload in the same interval (Rocq module `ResponseTimeAnalysisFP`, section `Theorem2`).

As in the Rocq original, every section variable declared before the theorem is abstracted, so the
unused task parameters, `job_deadline` and the `arr_seq`-hypothesis `H_j_arrives` are binders here
as well.
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference

universe u v

/-- The statement of the case study's theorem `theorem_2`. -/
def theorem_2_statement : Prop :=
  ∀ {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (j : Job)
    (H_j_arrives : arrives_in arr_seq j),
    ∀ (tsk : sporadic_task) (t1 t2 : time),
      task_interference job_arrival job_cost job_task sched j tsk t1 t2 ≤
        workload job_task sched tsk t1 t2

end CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP
