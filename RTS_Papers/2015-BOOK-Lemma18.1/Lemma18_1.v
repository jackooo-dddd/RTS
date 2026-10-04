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
         Priority TaskArrival  ConstrainedDeadlines.


 Section WorkloadBoundDef.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.

   
    Variable tsk: sporadic_task.
    Variable tsk_k: sporadic_task.
    Variable R_tsk: time.
    Variable delta: time.
    
   
    Definition max_jobs :=
      div_floor (delta + R_tsk - task_cost tsk) (task_period tsk).

   
    Definition W :=
      let e_k := (task_cost tsk) in
      let p_k := (task_period tsk) in            
        minn e_k (delta + R_tsk - e_k - max_jobs * p_k) + max_jobs * e_k.


    Definition W_NC := 
      let e_i := (task_cost tsk) in
      let p_i := (task_period tsk) in
      
       (div_floor delta p_i) * e_i + (minn e_i (delta %%p_i)).
  End WorkloadBoundDef.
Section InterferenceDef.

    Import Schedule.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.

    Variable R_prev: seq task_with_response_time.

    (* ... and an interval length delta. *)
    Variable delta: time.

    Section PerTask.

      Variable tsk_R: task_with_response_time.
      Let tsk_other := fst tsk_R.
      Let R_other := snd tsk_R.
    

      Definition interference_bound_generic :=
        minn (W task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1).

      Definition interference_bound_nc :=
        minn (W_NC task_cost task_period tsk_other delta) (delta - task_cost tsk + 1).
    
      Definition interference_bound_delta :=
          interference_bound_generic-interference_bound_nc.
End PerTask.

  End InterferenceDef.

Section Interference_Bound.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    
    Variable R_prev: seq task_with_response_time.

    Variable delta: time.
    Variable num_cpus:nat.

    Variable higher_eq_priority: FP_policy sporadic_task.
Definition sum_largest (n : nat) (xs : seq nat) :=
  \sum_(x <- take n (sort geq xs)) x.
    
    Let total_interference_bound := interference_bound_generic task_cost task_period tsk delta.
    
    Let interference_bound_nc :=interference_bound_nc task_cost task_period tsk delta.
    
    Let total_interference_bound_delta :=interference_bound_delta task_cost task_period tsk delta.
Definition total_interference_bound_fp :=
      \sum_((tsk_other, R_other) <- R_prev)
         total_interference_bound (tsk_other, R_other).



Definition CI_taskset  : seq task_with_response_time :=
  take (num_cpus.-1)
       (sort
          (fun p q =>
             total_interference_bound_delta q
           <= total_interference_bound_delta p)
          R_prev).
Definition NC_taskset : seq task_with_response_time :=
  [seq p <- R_prev | p \notin CI_taskset].

Definition total_interference_bound_ci := 
\sum_(p <- CI_taskset) total_interference_bound p.

Definition total_interference_bound_nc := 
\sum_(p <- NC_taskset) interference_bound_nc p.
Definition total_interference_bound_gn :=
  (\sum_(p <- NC_taskset) interference_bound_nc p)
  + (\sum_(p <- CI_taskset) total_interference_bound p).
  End Interference_Bound.
  Section ResponseTimeBound.

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

    
    Hypothesis H_sporadic_tasks:
      sporadic_task_model task_period job_arrival job_task arr_seq.
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.
    Hypothesis H_constrained_deadlines:
      forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

    
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

   
    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.

    
    Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

 
    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    
    Variable higher_eq_priority: FP_policy sporadic_task.


    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    Hypothesis H_respects_FP_policy:
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority.




   
    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.


    
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    
    Let is_hp_task := higher_priority_task higher_eq_priority tsk.

    
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
    Hypothesis H_response_time_of_interfering_tasks_is_known:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->
        response_time_bounded_by hp_tsk R.
    
    Hypothesis H_hp_bounds_has_interfering_tasks:
      forall hp_tsk,
        hp_tsk \in ts ->
        is_hp_task hp_tsk ->
          exists R, (hp_tsk, R) \in hp_bounds.

   
    Hypothesis H_response_time_bounds_ge_cost:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds -> R >= task_cost hp_tsk.
    
    
    Hypothesis H_interfering_tasks_miss_no_deadlines:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds -> R <= task_deadline hp_tsk.

    

    Hypothesis num_higher_priority_tsk :
       \sum_((hp_tsk, R)<-hp_bounds) 1<num_cpus.
    Variable R1: time.
    Variable R2: time.
    Hypothesis H_response_time_recurrence_holds_gn :
      R1 = task_cost tsk +
          div_floor
            (total_interference_bound_gn task_cost task_period tsk hp_bounds R1 num_cpus)
            num_cpus.
 Hypothesis H_response_time_recurrence_holds_bertogna :
      R2 = task_cost tsk +
          div_floor
             (total_interference_bound_fp task_cost task_period tsk hp_bounds R2)
            num_cpus.
Hypothesis R1_is_least_solution :
     forall x,
       x = task_cost tsk +
           div_floor
             (total_interference_bound_gn task_cost task_period tsk hp_bounds x num_cpus)
             num_cpus ->
       R1 <= x.
Hypothesis R2_is_least_solution :
     forall x,
       x = task_cost tsk +
           div_floor
             (total_interference_bound_fp task_cost task_period tsk hp_bounds x)
             num_cpus ->
       R2 <= x.

Lemma Lemma18_1_15:
\sum_((hp_tsk, R)<-hp_bounds) 1<num_cpus->(R1=task_cost tsk) /\ (R2=task_cost tsk).
Proof.
Admitted.
    

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.
