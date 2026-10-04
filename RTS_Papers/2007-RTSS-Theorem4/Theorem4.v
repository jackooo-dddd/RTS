Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform
               prosa.classic.model.schedule.global.basic.constrained_deadlines prosa.classic.model.schedule.global.basic.interference.
Require Import 
               prosa.classic.model.schedule.global.response_time.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq div fintype bigop path.


Module WorkloadBound.
  
    Export Job SporadicTaskset ScheduleOfSporadicTask Workload 
          Platform Schedulability ResponseTime
          TaskArrival  ConstrainedDeadlines.

  Section WorkloadBoundDef.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline : sporadic_task->time.

    Variable tsk: sporadic_task.
    Variable tsk_k: sporadic_task.
    Variable delta: time.
    
    
    Definition max_jobs :=
      div_floor (delta + task_deadline tsk - task_cost tsk) (task_period tsk).


    Definition W :=
      let e_k := (task_cost tsk) in
      let p_k := (task_period tsk) in 
         let d_k:=  (task_deadline tsk) in          
        minn e_k (delta + d_k - e_k - max_jobs * p_k) + max_jobs * e_k.

  End WorkloadBoundDef.
  

 
  Section Theorem4_07.
 
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    Context {Job: eqType}.
    Variable job_arrival: Job -> time.
    Variable job_cost: Job -> time.
    Variable job_task: Job -> sporadic_task.
    Variable job_deadline: Job -> time.

    Variable arr_seq: arrival_sequence Job.

     Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

 
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.

    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.

       Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    
  
    
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    
  Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.

  Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.  


    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    


    Let workload_of (tsk: sporadic_task) (t1 t2: time) :=
      workload job_task sched tsk t1 t2.


    Variable tsk: sporadic_task.
Hypothesis task_in_ts: tsk \in ts.
 
  


    Hypothesis H_constrained_deadline: task_deadline tsk <= task_period tsk.
     Hypothesis H_no_deadline_miss: task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk. 
    (* Consider an interval [t1, t1 + delta). *)
    Variable t1 delta: time.
Let workload_bound := W task_cost task_period task_deadline tsk delta.
 
    Section MainProof.

  
      Theorem Theorem4_07 :
        workload_of tsk t1 (t1 + delta) <= workload_bound.
      Proof.
        Admitted.
    End MainProof.
    
  End Theorem4_07.

End WorkloadBound.