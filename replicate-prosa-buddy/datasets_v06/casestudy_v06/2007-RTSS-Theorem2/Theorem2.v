Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform
               prosa.classic.model.schedule.global.basic.constrained_deadlines prosa.classic.model.schedule.global.basic.interference.
Require Import 
               prosa.classic.model.schedule.global.response_time.
               
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Interference
          Platform Schedulability ResponseTime
          TaskArrival  ConstrainedDeadlines.


  Section Theorem2.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_deadline: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable arr_seq: arrival_sequence Job.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
    
    (* Next, consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    Variable j :Job.
      Hypothesis H_j_arrives: arrives_in arr_seq j.
      
    (* Assume any job arrival sequence... *)
Theorem theorem_2 :   
    forall tsk t1 t2,
          task_interference job_arrival job_cost job_task sched j tsk t1 t2 <= workload job_task sched tsk t1 t2.
Proof.
Admitted.
End Theorem2.
End ResponseTimeAnalysisFP.