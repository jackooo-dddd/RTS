Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival
               prosa.classic.model.arrival.basic.arrival_bounds.
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
         Priority TaskArrival  .


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
     Variable h:nat.

      Definition interference_bound_arbitrary_ci :=
        minn (W task_cost task_period tsk_other R_other delta) (delta - h*task_cost tsk + 1).

      Definition interference_bound_arbitrary_nc :=
        minn (W_NC task_cost task_period tsk_other delta) (delta - h*task_cost tsk + 1).
    
       Definition interference_bound_delta :=
          interference_bound_arbitrary_ci-interference_bound_arbitrary_nc.
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
    Variable h:nat.

    Let total_interference_bound := interference_bound_arbitrary_ci task_cost task_period tsk delta .
    
    Let interference_bound_nc :=interference_bound_arbitrary_nc task_cost task_period tsk delta.
    
   Let total_interference_bound_delta :=interference_bound_delta task_cost task_period tsk delta.
Definition total_interference_bound_fp :=
      \sum_((tsk_other, R_other) <- R_prev)
         total_interference_bound (tsk_other, R_other) h.



Definition CI_taskset  : seq task_with_response_time :=
  take (num_cpus.-1)
       (sort
          (fun p q =>
             total_interference_bound_delta q h
           <= total_interference_bound_delta p h)
          R_prev).
Definition NC_taskset : seq task_with_response_time :=
  [seq p <- R_prev | p \notin CI_taskset].

Definition total_interference_bound_ci := 
\sum_(p <- CI_taskset) total_interference_bound p h.

Definition total_interference_bound_nc := 
\sum_(p <- NC_taskset) interference_bound_nc p h.
Definition total_interference_bound_gn_arbitrary :=
  (\sum_(p <- NC_taskset) interference_bound_nc p h)
  + (\sum_(p <- CI_taskset) total_interference_bound p h).
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
    Hypothesis H_arrival_times_are_consistent:
      arrival_times_are_consistent job_arrival arr_seq.
    Hypothesis H_arrival_sequence_is_a_set:
      arrival_sequence_is_a_set arr_seq.
    Hypothesis H_valid_job_parameters:
      forall j,
        arrives_in arr_seq j ->
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j.

    
    Variable ts: taskset_of sporadic_task.
    Hypothesis H_valid_task_parameters:
      valid_sporadic_taskset task_cost task_period task_deadline ts.


    
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



   
    Let no_deadline_is_missed_by_tsk (tsk: sporadic_task) :=
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.
    Let response_time_bounded_by (tsk: sporadic_task) :=
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk.


    
    Variable tsk: sporadic_task.
    Hypothesis task_in_ts: tsk \in ts.

    
    Let is_hp_task := higher_priority_task higher_eq_priority tsk.
Let task_with_response_time := (sporadic_task * time)%type.
    Variable hp_bounds: seq task_with_response_time.
Let CI_taskset (t:time):= CI_taskset task_cost task_period tsk hp_bounds t num_cpus.
Let NC_taskset (t:time):= NC_taskset task_cost task_period tsk hp_bounds t num_cpus.

    
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

Definition f_chi  (h:nat) (chi:time):=
   h* (task_cost tsk)+
    div_floor
          (total_interference_bound_gn_arbitrary task_cost task_period tsk hp_bounds chi num_cpus h)
            num_cpus.

Definition chi_is_least_solution (h:nat) (chi:time):=

    chi=f_chi h chi /\ (forall x, x=f_chi h x->x>=chi).
Variable chi_min : nat -> time.
Hypothesis chi_min_spec :
  forall h, chi_is_least_solution h (chi_min h).



    

 
Hypothesis Huniq_hp_bounds : uniq hp_bounds.


    
 Section Lemma5.

    Variable j: Job.  
Variable t0 : schedule Job num_cpus->Job->time.
      Hypothesis t0_leq_arrival_time: t0 sched j<=job_arrival j.
 Hypothesis H_j_arrives: arrives_in arr_seq j.
      Hypothesis H_job_of_tsk: job_task j = tsk.

     
      
      Hypothesis H_previous_jobs_of_tsk_completed :
        forall j0,
          arrives_in arr_seq j0 ->
          job_task j0 = tsk ->
          job_arrival j0 < job_arrival j ->
          completed job_cost sched j0 (job_arrival j).
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
Variable phi:time.
Hypothesis phi_is_defined : phi= job_arrival j-t0 sched j.


Variable H_phi : nat.


Definition H_phi_satisfy (h:nat) :=
  chi_min h <= h * task_period tsk + phi.



Hypothesis H_phi_is_minimal :
   1 <= H_phi /\ H_phi_satisfy H_phi /\ forall x, 1<=x -> H_phi_satisfy x -> H_phi <= x.
Definition R_phi_term (h:nat) : time :=
  chi_min h - ((h - 1) * task_period tsk + phi).

Fixpoint max_R_phi_term (h:nat) : time :=
  match h with
  | 0 => 0
  | S h' => maxn (max_R_phi_term h') (R_phi_term (S h'))
  end.


  Hypothesis H_Lemma2_1 :
forall tsk_other R_other t1 h delta, (tsk_other,R_other) \in NC_taskset delta h
  -> workload job_task sched tsk_other t1 (t1+delta) <= W_NC task_cost task_period tsk_other delta.

Hypothesis H_Lemma2_2:
forall tsk_other R_other t1 h delta, (tsk_other,R_other) \in CI_taskset delta h
  -> workload job_task sched tsk_other t1 (t1+delta)<= W task_cost task_period tsk_other R_other delta.

Definition jobs_of_tsk_between (t1 t2 : time) :=
  arrivals_of_task_between job_task arr_seq tsk t1 t2.

Definition first_h_jobs_through (j_h : Job) :=
  jobs_of_tsk_between (job_arrival j) (job_arrival j_h).+1.

Definition job_finishes_at (j_h : Job) (f_h : time) :=
  (~~ completed job_cost sched j_h (f_h - 1)) && completed job_cost sched j_h f_h.

Definition job_is_hth_after_j (h : nat) (j_h : Job) :=
  1 <= h /\
  arrives_in arr_seq j_h /\
  job_task j_h = tsk /\
  job_arrival j_h = job_arrival j + (h - 1) * task_period tsk /\
  size (first_h_jobs_through j_h) = h /\
  j_h \in first_h_jobs_through j_h.

Hypothesis H_jobs_before_H_phi_do_not_complete_by_next_release :
  forall h j_h,
    h < H_phi ->
    job_is_hth_after_j h j_h ->
    ~~ completed job_cost sched j_h (job_arrival j_h + task_period tsk).

    Definition preceding_jobs_are_completed_before_first_job :=
  forall j_prev,
    arrives_in arr_seq j_prev ->
    job_task j_prev = tsk ->
    job_arrival j_prev < job_arrival j ->
    completed job_cost sched j_prev (job_arrival j).

Definition consecutive_jobs_exist_through (h_last : nat) :=
  forall h,
    1 <= h ->
    h <= h_last ->
    exists j_h, job_is_hth_after_j h j_h.

Definition consecutive_jobs_are_tight_through (h_last : nat) :=
  forall h j_h j_next,
    1 <= h ->
    h < h_last ->
    job_is_hth_after_j h j_h ->
    job_is_hth_after_j h.+1 j_next ->
    job_arrival j_next = job_arrival j_h + task_period tsk.

Definition consecutive_jobs_overlap_through (h_last : nat) :=
  forall h j_h j_next,
    1 <= h ->
    h < h_last ->
    job_is_hth_after_j h j_h ->
    job_is_hth_after_j h.+1 j_next ->
    ~~ completed job_cost sched j_h (job_arrival j_next).

Definition tight_chain_ending_at (h_last : nat) (j_last : Job) :=
  job_is_hth_after_j h_last j_last /\
  preceding_jobs_are_completed_before_first_job /\
  consecutive_jobs_exist_through h_last /\
  consecutive_jobs_are_tight_through h_last /\
  consecutive_jobs_overlap_through h_last.

Definition job_has_worstcase_response_time (j_worst : Job) :=
  forall j0 x,
    arrives_in arr_seq j0 ->
    job_task j0 = tsk ->
    completed job_cost sched j_worst (job_arrival j_worst + x) ->
    completed job_cost sched j0 (job_arrival j0 + x).

Definition worstcase_job_selected_from_tight_chain
    (h_last h_worst : nat) (j_worst : Job) (f_worst : time) :=
  h_worst <= h_last /\
  job_is_hth_after_j h_worst j_worst /\
  job_finishes_at j_worst f_worst /\
  job_arrival j_worst < f_worst /\
  job_has_worstcase_response_time j_worst.

Hypothesis H_current_chain_reaches_H_phi :
  exists j_H_phi, job_is_hth_after_j H_phi j_H_phi.

Hypothesis H_Lemma1_selects_worstcase_job_from_tight_chain :
  forall h_last j_last,
    tight_chain_ending_at h_last j_last ->
    exists h_worst j_worst f_worst,
      worstcase_job_selected_from_tight_chain
        h_last h_worst j_worst f_worst.

  
 
Lemma Lemma5_09 :
    response_time_bounded_by tsk (max_R_phi_term H_phi).

Proof.
Admitted.


End Lemma5.
  End ResponseTimeBound.

End ResponseTimeAnalysisFP.
