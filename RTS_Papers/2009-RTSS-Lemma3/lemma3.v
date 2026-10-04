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
      div_floor (delta  - task_cost tsk) (task_period tsk).

   
    Definition W :=
      let e_k := (task_cost tsk) in
      let p_k := (task_period tsk) in            
        minn (e_k-1) (delta + R_tsk - e_k - max_jobs * p_k-p_k) + max_jobs * e_k+e_k.


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
    Hypothesis H_sequential_tasks:
      forall j1 j2 t cpu,
        arrives_in arr_seq j1 ->
        arrives_in arr_seq j2 ->
        job_task j1 = job_task j2 ->
        job_arrival j1 < job_arrival j2 ->
        scheduled_on sched j2 cpu t ->
        completed job_cost sched j1 t.
    
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

    

    
    Variable R: time.

    Hypothesis H_response_time_recurrence_holds :
      R = task_cost tsk +
          div_floor
            (total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus)
            num_cpus.
 
Hypothesis Huniq_hp_bounds : uniq hp_bounds.
Let NC_taskset (t:time):=  NC_taskset task_cost task_period tsk hp_bounds t num_cpus.
Let CI_taskset (t:time):= CI_taskset task_cost task_period tsk hp_bounds t num_cpus.
   

   
Hypothesis H_response_time_no_larger_than_deadline:
      R <= task_deadline tsk.

    
 Section Lemma3.
    Variable j: Job.  
Variable t0 : schedule Job num_cpus->Job->time.
      Hypothesis t0_leq_arrival_time: t0 sched j<=job_arrival j.
Hypothesis H_j_of_tsk : job_task j = tsk.
      Let scheduled_heptask (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          is_hp_task tsk_other.
      Definition hp_busy (t:time) :=
  count (scheduled_heptask t) ts = num_cpus.

Hypothesis cpu_busy_during_t0_rk :
  forall t, t0 sched j <= t < job_arrival j -> hp_busy t.

Hypothesis t0_left_boundary :
  t0 sched j = 0 \/
  ~ hp_busy (t0 sched j - 1).


Hypothesis j_has_worstcase_responsetime: 
forall j0 x,arrives_in arr_seq j0 ->
          job_task j0 = tsk 
        ->completed job_cost sched j (job_arrival j + x)
          ->completed job_cost sched j0 (job_arrival j0 + x).

Let other_scheduled_task (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          is_hp_task tsk_other.
 

 Hypothesis H_j_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_tsk: job_task j = tsk.

     
      
      Hypothesis H_previous_jobs_of_tsk_completed :
        forall j0,
          arrives_in arr_seq j0 ->
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j0 + R).
     

Hypothesis H_Lemma2_1 :
forall tsk_other R_other t1 delta, (tsk_other,R_other) \in NC_taskset delta
  -> workload job_task sched tsk_other t1 (t1+delta) <= W_NC task_cost task_period tsk_other delta.

Hypothesis H_Lemma2_2:
forall tsk_other R_other t1 delta, (tsk_other,R_other) \in CI_taskset delta
  -> workload job_task sched tsk_other t1 (t1+delta)<= W task_cost task_period tsk_other R_other delta.


    Variable f:time.
    Hypothesis f_is_finish_time : (~~ completed job_cost sched j (f-1)) && (completed job_cost sched j f). 
Hypothesis arrival_before_finish : job_arrival j < f. 



  Lemma Lemma3_09 :
      forall t, t< f-t0 sched j -> t>=task_cost tsk ->
          div_floor
            (total_interference_bound_gn task_cost task_period tsk hp_bounds t num_cpus)
            num_cpus>t-task_cost tsk.
Proof.

Admitted.
End Lemma3.



  End ResponseTimeBound.

End ResponseTimeAnalysisFP.
