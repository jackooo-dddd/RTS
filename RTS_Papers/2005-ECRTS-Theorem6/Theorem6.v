Require Import prosa.classic.util.all.
Require Import prosa.classic.model.arrival.basic.task prosa.classic.model.arrival.basic.job prosa.classic.model.priority prosa.classic.model.arrival.basic.task_arrival.
Require Import prosa.classic.model.schedule.global.workload.
Require Import prosa.classic.model.schedule.global.schedulability.
Require Import prosa.classic.model.schedule.global.basic.schedule prosa.classic.model.schedule.global.basic.platform
               prosa.classic.model.schedule.global.basic.constrained_deadlines prosa.classic.model.schedule.global.basic.interference.


From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop div path.

Module SchedulabilityAnalysisEDF.

  Export Job SporadicTaskset ScheduleOfSporadicTask Workload Interference
          Platform Schedulability 
      TaskArrival ConstrainedDeadlines Priority.

Section Theorem6_05.
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
      job_cost j > 0 /\
      job_cost j < job_deadline j /\
      job_deadline j > 0 /\
      job_deadline j = task_deadline (job_task j)/\ job_cost j = task_cost (job_task j).
 

  Variable ts: taskset_of sporadic_task.
  Hypothesis H_valid_task_parameters:
    valid_sporadic_taskset task_cost task_period task_deadline ts.

  Hypothesis H_sporadic_tasks:
    sporadic_task_model task_period job_arrival job_task arr_seq.

  Hypothesis H_all_jobs_from_taskset:
    forall j, arrives_in arr_seq j -> job_task j \in ts.

  Variable num_cpus: nat.
  Variable sched: schedule Job num_cpus.

  Hypothesis H_jobs_must_arrive_to_execute:
    jobs_must_arrive_to_execute job_arrival sched.

  Hypothesis H_jobs_come_from_arrival_sequence:
    jobs_come_from_arrival_sequence sched arr_seq.

  Hypothesis H_sequential_jobs: sequential_jobs sched.



  Hypothesis H_at_least_one_cpu: num_cpus > 0.

  Hypothesis H_completed_jobs_dont_execute:
    completed_jobs_dont_execute job_cost sched.
Hypothesis H_arrival_times_are_consistent:
  arrival_times_are_consistent job_arrival arr_seq.

Hypothesis H_no_duplicate_arrivals:
  arrival_sequence_is_a_set arr_seq.
  Hypothesis H_work_conserving:
    work_conserving job_arrival job_cost arr_seq sched.
Hypothesis uniq_ts:
    uniq ts.

  Hypothesis H_edf_policy:
    respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline).



  Hypothesis H_constrained_deadlines:
    forall tsk, tsk \in ts -> task_deadline tsk <= task_period tsk.

  Hypothesis H_positive_slack:
    forall tsk, tsk \in ts -> task_cost tsk < task_deadline tsk.

   
 Definition cumulative_task_interference (j: Job) (a b: time) (tsk: sporadic_task) :=
      \sum_(tsk_other <- ts | tsk_other != tsk)
        task_interference job_arrival job_cost job_task sched j tsk_other a b.


    Hypothesis Lemma5_05:  forall (j: Job) a b (tsk: sporadic_task),
    tsk \in ts->
        arrives_in arr_seq j ->
        job_task j = tsk ->
        cumulative_task_interference j a b tsk =
          num_cpus * total_interference job_arrival job_cost sched j a b.

  Hypothesis H_Lemma4_05:
    forall (tsk_k: sporadic_task) (j: Job) a b c,
      tsk_k \in ts ->
      arrives_in arr_seq j ->
      job_task j = tsk_k ->
      total_interference job_arrival job_cost sched j a b >= c <->
      \sum_(tsk_other <- ts | tsk_other != tsk_k)
        PeanoNat.Nat.min
          (task_interference job_arrival job_cost job_task sched j tsk_other a b) c
        >= num_cpus * c.

  Variable worst_case_job_of_task: sporadic_task -> Job.

  Hypothesis H_worst_case_job_arrives:
    forall tsk, tsk \in ts -> arrives_in arr_seq (worst_case_job_of_task tsk).

  Hypothesis H_worst_case_job_of_task:
    forall tsk, tsk \in ts -> job_task (worst_case_job_of_task tsk) = tsk.

  Let total_interference_in_job_window (j: Job) :=
    total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j+ job_deadline j).

  Hypothesis H_worst_case_interference:
    forall tsk j,
      tsk \in ts ->
      arrives_in arr_seq j ->
      job_task j = tsk ->
      total_interference_in_job_window j <=
        total_interference_in_job_window (worst_case_job_of_task tsk).

  Definition slack (tsk: sporadic_task) :=
    task_deadline tsk - task_cost tsk.

  Definition task_interference_in_worst_case_window
             (tsk_other tsk: sporadic_task) :=
    let j := worst_case_job_of_task tsk in
    task_interference job_arrival job_cost job_task sched j tsk_other
      (job_arrival j) (job_arrival j+ job_deadline j).

  Definition truncated_task_interference_sum (tsk: sporadic_task) :=
    \sum_(tsk_other <- ts | tsk_other != tsk)
      PeanoNat.Nat.min
        (task_interference_in_worst_case_window tsk_other tsk)
        (slack tsk).

  Definition theorem6_first_condition (tsk: sporadic_task) :=
    truncated_task_interference_sum tsk < num_cpus * slack tsk.

  Definition theorem6_second_condition (tsk: sporadic_task) :=
    truncated_task_interference_sum tsk = num_cpus * slack tsk /\
    exists tsk_h,
      tsk_h \in ts /\
      tsk_h != tsk /\
      0 < task_interference_in_worst_case_window tsk_h tsk /\
      task_interference_in_worst_case_window tsk_h tsk <= slack tsk.

  Definition theorem6_task_condition (tsk: sporadic_task) :=
    theorem6_first_condition tsk \/ theorem6_second_condition tsk.

  Definition taskset_schedulable :=
    forall tsk,
      tsk \in ts ->
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk.

  Theorem Theorem6_05 :
    taskset_schedulable <->
    forall tsk,
      tsk \in ts -> theorem6_task_condition tsk.
  Proof.


  Admitted.

End Theorem6_05.

End SchedulabilityAnalysisEDF.