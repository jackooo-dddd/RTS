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

Section Theorem3_07.
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

    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    (* Assume that we have a task set where all tasks have valid
       parameters and constrained deadlines, ... *)
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.


    (* ... and that all jobs in the arrival sequence come from the task set. *)
     Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    (* Next, consider any schedule such that...*)
    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    
    (* ...jobs are sequential and do not execute before their
       arrival times nor longer than their execution costs. *)
    
      Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.
    Hypothesis H_sporadic_tasks:
  sporadic_task_model task_period job_arrival job_task arr_seq.
    
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    (* Assume that there exists at least one processor. *)
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.

    (* Next, we consider the response-time recurrence.
       Let tsk be a task in ts that is to be analyzed. *)
    Variable tsk: sporadic_task.
    Hypothesis H_tsk_in_ts: tsk \in ts.

    Variable R: time.
    (* R must be at least the task cost (implicit in the paper). *)
    Hypothesis H_R_ge_cost: R >= task_cost tsk.
    Hypothesis H_arrival_times_are_consistent:
  arrival_times_are_consistent job_arrival arr_seq.
   
Hypothesis H_no_duplicate_arrivals:
  arrival_sequence_is_a_set arr_seq.
  Hypothesis H_constrained_deadlines :
    constrained_deadline_model task_deadline task_period ts.
     Hypothesis H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq.


Variable j: Job.
Hypothesis H_j_arrives: arrives_in arr_seq j.
Hypothesis H_job_of_tsk: job_task j = tsk.

 Let x (tsk_other: sporadic_task) :=
        task_interference job_arrival job_cost job_task sched j tsk_other
                          (job_arrival j) (job_arrival j + R).

Hypothesis j_has_max_interference :
forall j0 , job_task j0=tsk ->arrives_in arr_seq j0 ->
total_interference job_arrival job_cost sched j0 (job_arrival j0) (job_arrival j0+R)
<=total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j+R).

Hypothesis Lemma1:  forall (j: Job) a b c, arrives_in arr_seq j ->job_task j=tsk ->
        total_interference job_arrival job_cost sched j a b >= c <->
        \sum_(t <- ts | t != tsk)
          PeanoNat.Nat.min (task_interference job_arrival job_cost job_task sched j t a b) c
          >= num_cpus * c.

Theorem Theorem3_07 :

      \sum_(t <- ts | t != tsk) PeanoNat.Nat.min (x t) (R-task_cost tsk+1) < num_cpus*(R-task_cost tsk+1)-> response_time_bounded_by tsk R.
Proof.
Admitted.

End Theorem3_07.
End ResponseTimeAnalysisFP.