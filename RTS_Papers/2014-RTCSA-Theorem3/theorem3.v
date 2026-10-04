
Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform
                prosa.classic.model.schedule.global.basic.interference.
Require Import prosa.classic.model.schedule.global.basic.constrained_deadlines
               prosa.classic.model.schedule.global.response_time.
             
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Interference
          Platform Schedulability ResponseTime
         Priority TaskArrival ConstrainedDeadlines.



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
     

      Definition interference_bound_arbitrary_ci :=
        minn (W_CI task_cost task_period tsk_other R_other delta) (delta - task_cost tsk + 1).

      Definition interference_bound_arbitrary_nc :=
        minn (W_NC task_cost task_period tsk_other delta) (delta - task_cost tsk + 1).
    
     
End PerTask.

  End InterferenceDef.

Section Interference_Bound.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
    
    Variable tsk: sporadic_task.

    Let task_with_response_time := (sporadic_task * time)%type.
    
    
    Variable R_carryin: seq task_with_response_time.
    Variable R_noncarryin : seq task_with_response_time.
    Variable delta: time.
    Variable num_cpus:nat.

    Variable higher_eq_priority: FP_policy sporadic_task.

    

    Let interference_bound_ci := interference_bound_arbitrary_ci task_cost task_period tsk delta .
    
    Let interference_bound_nc :=interference_bound_arbitrary_nc task_cost task_period tsk delta.
    
   
Definition total_interference_bound_CI :=
      \sum_((tsk_other, R_other) <- R_carryin)
         interference_bound_ci (tsk_other, R_other) .

Definition total_interference_bound_NC :=
      \sum_((tsk_other, R_other) <- R_noncarryin)
         interference_bound_nc (tsk_other, R_other) .


Definition total_interference_bound_rtcsa14 :=total_interference_bound_CI+total_interference_bound_NC.



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

   Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    

    Let is_hp_task := higher_priority_task higher_eq_priority tsk.

   
    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.

    Hypothesis task_in_hpbound_in_ts :
    forall  hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->hp_tsk \in ts /\ is_hp_task hp_tsk.
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
 Hypothesis exist_j_released_at_criticalinstant : exists j,  arrives_in arr_seq j /\job_task j = tsk->job_arrival j=critical_instant.


Definition valid_CI_taskset (CI_taskset : seq task_with_response_time) : Prop :=
  {subset CI_taskset <= hp_bounds} /\
  uniq CI_taskset /\
  size CI_taskset < num_cpus /\
  (forall tsk_other R_other,
      (tsk_other, R_other) \in CI_taskset ->
      exists j0,
        arrives_in arr_seq j0 /\
        job_task j0 = tsk_other /\
        job_arrival j0 < critical_instant /\
        ~~ completed job_cost sched j0 critical_instant).
Variable R_of_CI : seq task_with_response_time -> time.

Hypothesis H_response_time_recurrence_holds :
  forall CI_taskset,
    valid_CI_taskset CI_taskset ->
    let NC_taskset := [seq x <- hp_bounds | x \notin CI_taskset] in
    let R := R_of_CI CI_taskset in
      R = task_cost tsk +
          div_floor
            (total_interference_bound_rtcsa14
               task_cost task_period tsk
               CI_taskset NC_taskset R)
            num_cpus .
Hypothesis R_is_minimal_solution: 
    forall CI_taskset,
    valid_CI_taskset CI_taskset ->
    let NC_taskset := [seq x <- hp_bounds | x \notin CI_taskset] in
    let R := R_of_CI CI_taskset in (forall x,
         x = task_cost tsk +
             div_floor
               (total_interference_bound_rtcsa14
                  task_cost task_period tsk
                  CI_taskset NC_taskset x)
               num_cpus ->
         R <= x).


Hypothesis H_response_time_no_larger_than_deadline:
      forall CI_taskset,
    valid_CI_taskset CI_taskset -> R_of_CI CI_taskset <= task_deadline tsk.

Variable R_global : time.

Hypothesis H_R_global_upper :
  forall CI_taskset,
    valid_CI_taskset CI_taskset ->
    R_of_CI CI_taskset <= R_global.
Hypothesis H_R_global_least :
  forall R',
    (forall CI_taskset,
        valid_CI_taskset CI_taskset ->
        R_of_CI CI_taskset <= R') ->
    R_global <= R'.

Hypothesis lemma5: forall CI_taskset, response_time_bounded_by tsk (R_of_CI CI_taskset).

Lemma Theorem3_14:

    response_time_bounded_by tsk R_global.
    
Proof.
Admitted.

  End ResponseTimeBound.

End ResponseTimeAnalysisFP.


