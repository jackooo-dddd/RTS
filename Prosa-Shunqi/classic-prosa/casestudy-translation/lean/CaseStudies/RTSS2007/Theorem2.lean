-- Case study: RTS_Papers/2007-RTSS-Theorem2/Theorem2.v
-- (Bertogna & Cirinei, RTSS 2007, "Response-Time Analysis for Globally Scheduled Symmetric
-- Multiprocessor Platforms", Theorem 2); sha256 and elaborated contract:
-- classic-prosa/casestudy-translation/contracts/
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Interference

/-!
Theorem 2 of RTSS 2007: the interference that a task causes on a job is bounded by the task's
workload in the same interval (Rocq module `ResponseTimeAnalysisFP`, section `Theorem2`).

Binder list as in the Rocq contract (`Check @ResponseTimeAnalysisFP.theorem_2` in ProsaBuddy's
toolchain): every section variable declared before the theorem is abstracted, so the unused task
parameters, `job_deadline` and `arr_seq`-hypothesis `H_j_arrives` are binders here as well.
-/

set_option linter.unusedVariables false

namespace CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference

universe u v

theorem theorem_2 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (j : Job)
    (H_j_arrives : arrives_in arr_seq j) :
    ∀ (tsk : sporadic_task) (t1 t2 : time),
      task_interference job_arrival job_cost job_task sched j tsk t1 t2 ≤
        workload job_task sched tsk t1 t2 :=
  task_interference_le_workload job_arrival job_cost job_task sched j

end CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP
