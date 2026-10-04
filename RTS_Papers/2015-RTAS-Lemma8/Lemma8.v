Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.response_time prosa.classic.model.schedule.global.schedulability
               prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.schedule.global.basic.schedule.
Require Import prosa.classic.model.schedule.apa.platform prosa.classic.model.schedule.apa.constrained_deadlines
               prosa.classic.model.schedule.apa.interference prosa.classic.model.schedule.apa.affinity.

               
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module ResponseTimeAnalysisFP.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Interference 
         Platform Schedulability ResponseTime Priority
         TaskArrival Affinity ConstrainedDeadlines.
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
  Section InterferenceDef.

 
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.

    Variable num_cpus: nat.
    
    (* Let tsk be the task to be analyzed. *)
    Variable tsk: sporadic_task.


    Variable delta: time.

    Section PerTask.

      Variable tsk_other: sporadic_task.
 
     
      Definition interference_bound_generic :=
        minn (W task_cost task_period task_deadline tsk_other delta) (delta - (task_cost tsk) + 1).

    End PerTask.

  End InterferenceDef.



    Section InterferenceBound.
    
    Context {sporadic_task: eqType}.
    Variable task_cost: sporadic_task -> time.
    Variable task_period: sporadic_task -> time.
    Variable task_deadline: sporadic_task -> time.
    
  
    Context {num_cpus: nat}.
    Variable alpha: task_affinity sporadic_task num_cpus.

 
    Variable tsk: sporadic_task.

 
    Variable alpha': affinity num_cpus.

    Let task_with_response_time := (sporadic_task * time)%type.
    

    Variable R_prev: seq task_with_response_time.


    Variable delta: time.
      
 
    Variable higher_eq_priority: FP_policy sporadic_task.


    Let total_interference_bound := interference_bound_generic task_cost task_period task_deadline tsk delta.

  
    Let hp_task_in alpha' := higher_priority_task_in alpha higher_eq_priority tsk alpha'.
    
    Definition total_interference_bound_fp :=
      \sum_((tsk_other, R_other) <- R_prev | hp_task_in alpha' tsk_other)
         total_interference_bound tsk_other.
      
  End InterferenceBound.

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
    
    (* Assume any job arrival sequence... *)
    Variable arr_seq: arrival_sequence Job.

    (* ... in which jobs arrive sporadically and have valid parameters. *)
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
      forall j,
        arrives_in arr_seq j -> job_task j \in ts.

 
    Context {num_cpus: nat}.
    Variable alpha: task_affinity sporadic_task num_cpus.

   
    Variable sched: schedule Job num_cpus.
    Hypothesis H_jobs_come_from_arrival_sequence:
      jobs_come_from_arrival_sequence sched arr_seq.
    
 
    Hypothesis H_sequential_jobs: sequential_jobs sched.
    Hypothesis H_jobs_must_arrive_to_execute: jobs_must_arrive_to_execute job_arrival sched.
    Hypothesis H_completed_jobs_dont_execute: completed_jobs_dont_execute job_cost sched.

Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
      Hypothesis H_arr_seq_is_a_set: arrival_sequence_is_a_set arr_seq.
    Variable higher_eq_priority: FP_policy sporadic_task.


    Hypothesis H_respects_affinity: respects_affinity job_task sched alpha.
    Hypothesis H_work_conserving: apa_work_conserving job_arrival job_cost job_task
                                                      arr_seq sched alpha.
    Hypothesis H_respects_FP_policy:
      respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
                                        sched alpha higher_eq_priority.


    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.

    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.


    Variable alpha': task_affinity sporadic_task num_cpus.
    Hypothesis H_affinity_subset: forall tsk, tsk \in ts -> is_subaffinity (alpha' tsk) (alpha tsk).
    Hypothesis H_at_least_one_cpu : forall tsk, tsk \in ts -> #|alpha' tsk| > 0.

    Let hp_task_in alpha' := higher_priority_task_in alpha higher_eq_priority tsk alpha'.


    Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
    Hypothesis H_response_time_of_interfering_tasks_is_known:
      forall hp_tsk R,
        (hp_tsk, R) \in hp_bounds ->
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R.
 
    Hypothesis H_hp_bounds_has_interfering_tasks:
      forall hp_tsk,
        hp_tsk \in ts ->
        hp_task_in (alpha tsk) hp_tsk ->
        exists R,
          (hp_tsk, R) \in hp_bounds.

  
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
            (total_interference_bound_fp task_cost task_period task_deadline alpha tsk
                            (alpha' tsk) hp_bounds R higher_eq_priority)
            #|alpha' tsk|.

    Hypothesis H_response_time_no_larger_than_deadline:
      R <= task_deadline tsk.


    Theorem bertogna_cirinei_response_time_bound_fp :
      response_time_bounded_by tsk R.
    Proof.
      Admitted.
  End ResponseTimeBound.

End ResponseTimeAnalysisFP.

