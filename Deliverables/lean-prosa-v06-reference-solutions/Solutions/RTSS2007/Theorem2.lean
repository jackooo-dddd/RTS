import CaseStudies.RTSS2007.Theorem2
import Solutions.Support.Common

/-! Reference solution of benchmark task `2007-RTSS-Theorem2`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference

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

theorem Solutions.RTSS2007.Theorem2.solution : CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP.theorem_2_statement.{u, v} :=
  @CaseStudies.RTSS2007.Theorem2.ResponseTimeAnalysisFP.theorem_2
