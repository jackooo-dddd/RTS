Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.arrival_sequence prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform
                prosa.classic.model.schedule.global.basic.interference.
Require Import 
               prosa.classic.model.schedule.global.response_time.
             
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Interference
          Platform Schedulability ResponseTime
         Priority TaskArrival .



 Section WorkloadBoundDef.

    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.

   
    Variable tsk: sporadic_task.
    Variable tsk_k: sporadic_task.
    Variable R_tsk: time.
    Variable delta: time.
    
  

  Definition x_p :=
       let e_i := (task_cost tsk) in
      let p_i := (task_period tsk) in
          e_i-1+ (div_ceil(R_tsk-e_i) (p_i-e_i))*p_i-R_tsk.

 Definition x_delta:= let e_i := (task_cost tsk) in
      let p_i := (task_period tsk) in
                minn delta ((div_ceil(R_tsk-e_i) (p_i-e_i))*e_i-1).

    Definition W_NC := 
      let e_i := (task_cost tsk) in
      let p_i := (task_period tsk) in
       (div_floor delta p_i) * e_i + (minn e_i (delta %%p_i)).

Definition W_CI :=
        let e_i := (task_cost tsk) in
      let p_i := (task_period tsk) in
            (div_floor (delta-x_p) p_i) * e_i + (minn e_i ((delta-x_p) %%p_i))+x_delta.

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
        minn (W_CI task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1).

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
      forall tsk,
        tsk \in ts ->
        task_cost tsk > 0 /\
        task_period tsk > 0 /\
        task_deadline tsk > 0 /\
        task_cost tsk <= task_deadline tsk /\
        task_cost tsk < task_period tsk.


    
    Hypothesis H_all_jobs_from_taskset:
      forall j, arrives_in arr_seq j -> job_task j \in ts.

   
    Variable num_cpus: nat.
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
  Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
 Hypothesis H_no_duplicate_arrivals: arrival_sequence_is_a_set arr_seq.
    
    Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

    Hypothesis H_at_least_one_cpu: num_cpus > 0.

    Hypothesis previous_job_must_finished : forall j1 j2 t,
        scheduled sched j1 t->job_task j1= job_task j2->job_arrival j2 <job_arrival j1 -> completed  job_cost sched j2 t.

    Variable higher_eq_priority: FP_policy sporadic_task.

    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.
    Hypothesis H_work_conserving: work_conserving job_arrival job_cost arr_seq sched.
    Hypothesis H_respects_FP_policy:
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority.

      Hypothesis H_priority_transitive:
  FP_is_transitive higher_eq_priority.
  Hypothesis H_priority_antisymmetric:
  FP_is_antisymmetric_over_task_set higher_eq_priority ts.
  Hypothesis H_sequential_tasks:
      forall j1 j2 t cpu,
        arrives_in arr_seq j1 ->
        arrives_in arr_seq j2 ->
        job_task j1 = job_task j2 ->
        job_arrival j1 < job_arrival j2 ->
        scheduled_on sched j2 cpu t ->
        completed job_cost sched j1 t.
   Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    

    Let is_hp_task := higher_priority_task higher_eq_priority tsk.

   
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
    Hypothesis H_response_time_of_interfering_tasks_is_known:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->
        response_time_bounded_by hp_tsk R.
    
    (* ... for every higher-priority task. *)
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

    Hypothesis H_hp_bounds_uniq: uniq hp_bounds.
  Let CI_taskset (t:time):= CI_taskset task_cost task_period tsk hp_bounds t num_cpus.
Let NC_taskset (t:time):= NC_taskset task_cost task_period tsk hp_bounds t num_cpus.




   
  
    Let workload_of (tsk: sporadic_task) (t1 t2: time) :=
      workload job_task sched tsk t1 t2.    
    

Variable critical_instant : time.
   

      Let scheduled_heptask (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          is_hp_task tsk_other.
      Definition hp_busy (t:time) :=
  count (scheduled_heptask t) ts = num_cpus.

Hypothesis critical_instant_left_boundary :
  critical_instant = 0 \/
  ~ hp_busy (critical_instant - 1).

Hypothesis critical_instant_is_busy :
      count (scheduled_heptask critical_instant) ts = num_cpus.

Let other_scheduled_task (t: time) (tsk_other: sporadic_task) :=
          task_is_scheduled job_task sched tsk_other t &&
          is_hp_task tsk_other.
 




Definition is_carry_in_job (j0 : Job) (t: time):=
  arrives_in arr_seq j0 /\
  is_hp_task (job_task j0) /\
  job_arrival j0 < t /\
  ~~ completed job_cost sched j0 t.

Definition carry_in_jobs_of (tsk_other : sporadic_task) (t: time) :=
  [seq j0 <- jobs_arrived_before arr_seq t |
     (job_task j0 == tsk_other) &&
     is_hp_task (job_task j0) &&
     ~~ completed job_cost sched j0 t].

Definition number_of_carry_in_jobs (tsk_other : sporadic_task) (t: time) :=
  size (carry_in_jobs_of tsk_other t).

Definition task_has_carry_in_job (tsk_other : sporadic_task) (t: time) :=
  exists j0,
    job_task j0 = tsk_other /\
    is_carry_in_job j0 t.

Definition no_carry_in_workload_of_task (hp_tsk : sporadic_task) (t:time):=
  forall j0,
    arrives_in arr_seq j0 ->
    job_task j0 = hp_tsk ->
    job_arrival j0 < t ->
    completed job_cost sched j0 t.

Definition carry_in_job_workload (j0 : Job) (t: time) :=
  job_cost j0 - service sched j0 t.

Definition carry_in_workload (tsk_other : sporadic_task) (t:time) :=
  \sum_(j0 <- carry_in_jobs_of tsk_other t) carry_in_job_workload j0 t.

Hypothesis Lemma1_09:
   forall tsk_other t,
  task_has_carry_in_job tsk_other t ->
  carry_in_workload tsk_other t <=
    number_of_carry_in_jobs tsk_other t * task_cost tsk_other - 1.

Hypothesis Lemma2 :forall tsk_other R_other t delta, no_carry_in_workload_of_task tsk_other t -> (tsk_other,R_other) \in hp_bounds->
   workload job_task sched tsk_other t (t+delta) <= W_NC task_cost task_period tsk_other delta.


Let job_released_in_window
    (tsk_other : sporadic_task) (delta : time) (j0 : Job) :=
  arrives_in arr_seq j0 /\
  job_task j0 = tsk_other /\
  critical_instant <= job_arrival j0 /\
  job_arrival j0 < critical_instant + delta.

Let job_released_after_critical_instant
    (tsk_other : sporadic_task) (j0 : Job) :=
  arrives_in arr_seq j0 /\
  job_task j0 = tsk_other /\
  critical_instant <= job_arrival j0.

Let jobs_released_before_in_window
    (tsk_other : sporadic_task) (t : time) :=
  [seq j0 <- jobs_arrived_before arr_seq t |
     (job_task j0 == tsk_other) &&
     (critical_instant <= job_arrival j0)].

Let job_has_xi_index_in_window
    (tsk_other : sporadic_task) (xi : time) (j_xi : Job) :=
  xi > 0 /\
  size (jobs_released_before_in_window tsk_other (job_arrival j_xi)) = xi.-1.

Let xi_release_offset
    (tsk_other : sporadic_task) (R_other xi : time) :=
  task_cost tsk_other - 1 +
  (number_of_carry_in_jobs tsk_other critical_instant + xi.-1) *
    task_period tsk_other -
  R_other.

Let released_at_xi_tight_chain_time
    (tsk_other : sporadic_task) (R_other xi : time) (j_xi : Job) :=
  job_arrival j_xi =
    critical_instant + xi_release_offset tsk_other R_other xi.

Let tight_chain_prefix_job_count
    (tsk_other : sporadic_task) (xi : time) :=
  number_of_carry_in_jobs tsk_other critical_instant + xi.-1.

Let tight_chain_prefix_workload_bound_by_job_count
    (tsk_other : sporadic_task) (k : time) :=
  k * task_cost tsk_other - 1.

Let tight_chain_prefix_workload_bound
    (tsk_other : sporadic_task) (xi : time) :=
  number_of_carry_in_jobs tsk_other critical_instant * task_cost tsk_other - 1 +
  xi.-1 * task_cost tsk_other.

Let tight_chain_prefix_workload_fits
    (tsk_other : sporadic_task) (R_other xi : time) :=
  R_other + tight_chain_prefix_workload_bound tsk_other xi <=
    task_cost tsk_other - 1 +
      tight_chain_prefix_job_count tsk_other xi * task_period tsk_other.

Let tight_chain_prefix_job_count_fits
    (tsk_other : sporadic_task) (R_other k : time) :=
  R_other + tight_chain_prefix_workload_bound_by_job_count tsk_other k <=
    task_cost tsk_other - 1 + k * task_period tsk_other.

Let tight_chain_prefix_job_count_is_minimal
    (tsk_other : sporadic_task) (R_other xi : time) :=
  let k := tight_chain_prefix_job_count tsk_other xi in
  k > 0 /\
  tight_chain_prefix_job_count_fits tsk_other R_other k /\
  forall k0,
    k0 > 0 ->
    tight_chain_prefix_job_count_fits tsk_other R_other k0 ->
    k <= k0.

Let tight_chain_prefix_workload_le_job_count_bound
    (tsk_other : sporadic_task) (xi : time) (j_xi : Job) :=
  workload_of tsk_other critical_instant (job_arrival j_xi) <=
    tight_chain_prefix_workload_bound_by_job_count tsk_other
      (tight_chain_prefix_job_count tsk_other xi).

Let clears_previous_jobs_at_arrival (tsk_other : sporadic_task) (j0 : Job) :=
  arrives_in arr_seq j0 /\
  job_task j0 = tsk_other /\
  forall j1,
    arrives_in arr_seq j1 ->
    job_task j1 = tsk_other ->
    job_arrival j1 < job_arrival j0 ->
    completed job_cost sched j1 (job_arrival j0).

Let tight_chain_boundary_job
    (tsk_other : sporadic_task) (R_other xi : time) (j_xi : Job) :=
  job_released_after_critical_instant tsk_other j_xi /\
  job_has_xi_index_in_window tsk_other xi j_xi /\
  released_at_xi_tight_chain_time tsk_other R_other xi j_xi /\
  clears_previous_jobs_at_arrival tsk_other j_xi.

Let worst_case_tight_chain_release_pattern
    (tsk_other : sporadic_task) (R_other xi : time) (j_xi : Job) :=
  tight_chain_boundary_job tsk_other R_other xi j_xi /\
  tight_chain_prefix_job_count_is_minimal tsk_other R_other xi /\
  tight_chain_prefix_workload_le_job_count_bound tsk_other xi j_xi.

Let has_tight_chain_boundary_job
    (tsk_other : sporadic_task) (R_other : time) :=
  exists xi j_xi,
    tight_chain_boundary_job tsk_other R_other xi j_xi.

Let has_worst_case_tight_chain_release_pattern
    (tsk_other : sporadic_task) (R_other : time) :=
  exists xi j_xi,
    worst_case_tight_chain_release_pattern tsk_other R_other xi j_xi.

Hypothesis Lemma1_14:
  forall tsk_other R_other,
    task_has_carry_in_job tsk_other critical_instant ->
    (tsk_other,R_other) \in hp_bounds ->
    R_other > task_cost tsk_other ->
    exists xi j_xi,
      tight_chain_boundary_job tsk_other R_other xi j_xi /\
      tight_chain_prefix_job_count_is_minimal tsk_other R_other xi.


Variable tsk_other : sporadic_task.
Variable R_other delta xi : time.
Variable j_xi : Job.

Let prefix_scheduled_jobs :=
  jobs_of_task_scheduled_between job_task sched tsk_other
    critical_instant (job_arrival j_xi).

Let prefix_released_jobs :=
  jobs_released_before_in_window tsk_other (job_arrival j_xi).

Let prefix_cover_jobs :=
  carry_in_jobs_of tsk_other critical_instant ++ prefix_released_jobs.

Hypothesis H_tight_chain_boundary_job :
  tight_chain_boundary_job tsk_other R_other xi j_xi.

Hypothesis H_tight_chain_prefix_job_count_is_minimal :
  tight_chain_prefix_job_count_is_minimal tsk_other R_other xi.

Lemma Lemma4_14:

    forall tsk_other R_other t,  task_has_carry_in_job tsk_other critical_instant -> (tsk_other,R_other)\in hp_bounds-> workload_of tsk_other critical_instant (critical_instant + t) <=  W_CI task_cost task_period tsk_other R_other t.
    
Proof.
Admitted.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.