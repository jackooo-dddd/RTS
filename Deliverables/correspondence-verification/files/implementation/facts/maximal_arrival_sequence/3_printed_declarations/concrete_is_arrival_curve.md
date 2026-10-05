# `concrete_is_arrival_curve`

- Kind (Rocq): Theorem
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.concrete_is_arrival_curve`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.concrete_is_arrival_curve`
- Certificate: `concrete_is_arrival_curve_correspondence`

## Official Rocq

```coq
concrete_is_arrival_curve :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} (ts : seq (Equality.sort Task)),
is_true (@uniq Task ts) ->
forall {H3 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H3) ->
forall generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job),
(forall (tsk : Equality.sort Task) (n : nat) (t : instant),
 is_true (tsk \in ts) -> @size (Equality.sort Job) (generate_jobs_at tsk n t) = n) ->
(forall (tsk : Equality.sort Task) (n : nat) (t : instant) (j : Equality.sort Job),
 is_true (j \in generate_jobs_at tsk n t) ->
 @job_task Job Task H0 j = tsk /\
 @job_arrival Job H1 j = t /\ is_true (@job_cost Job H2 j <= @task_cost Task H tsk)) ->
@taskset_respects_max_arrivals Task Job H0 (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts) H3 ts

concrete_is_arrival_curve is not universe polymorphic
Arguments concrete_is_arrival_curve {Task H Job H0 H1 H2} ts%seq_scope H_ts_uniq 
  {H3} H_valid_arrival_curve
  (generate_jobs_at H_job_generation_valid_number H_job_generation_valid_jobs)%function_scope 
  tsk _ t1 t2 _
concrete_is_arrival_curve is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.concrete_is_arrival_curve
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 233, characters 10-35
@concrete_is_arrival_curve
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (ts : seq (Equality.sort Task)),
       is_true (@uniq Task ts) ->
       forall H3 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H3) ->
       forall generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job),
       (forall (tsk : Equality.sort Task) (n : nat) (t : instant),
        is_true (tsk \in ts) -> @size (Equality.sort Job) (generate_jobs_at tsk n t) = n) ->
       (forall (tsk : Equality.sort Task) (n : nat) (t : instant) (j : Equality.sort Job),
        is_true (j \in generate_jobs_at tsk n t) ->
        @job_task Job Task H0 j = tsk /\
        @job_arrival Job H1 j = t /\ is_true (@job_cost Job H2 j <= @task_cost Task H tsk)) ->
       @taskset_respects_max_arrivals Task Job H0
         (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts) H3 ts
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.concrete_is_arrival_curve : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job] (ts : List Task),
  ts.Nodup →
    ∀ [inst_6 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
      Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
        ∀ (generate_jobs_at : Task → ℕ → Prosa.Behavior.Time.instant → List Job),
          (∀ (tsk : Task) (n : ℕ) (t : Prosa.Behavior.Time.instant),
              decide (tsk ∈ ts) = true → (generate_jobs_at tsk n t).length = n) →
            (∀ (tsk : Task) (n : ℕ) (t : Prosa.Behavior.Time.instant) (j : Job),
                decide (j ∈ generate_jobs_at tsk n t) = true →
                  Prosa.Model.Task.Concept.job_task j = tsk ∧
                    Prosa.Behavior.Job.job_arrival j = t ∧
                      Prosa.Behavior.Job.job_cost j ≤ Prosa.Model.Task.Concept.task_cost tsk) →
              Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals
                (Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence generate_jobs_at ts)
                ts
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_concrete_is_arrival_curve
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (ts : List Task),
       List_Nodup Task ts ->
       forall
         inst_26 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_26) ->
       forall generate_jobs_at : Task -> Nat -> Prosa_Behavior_Time_instant -> List Job,
       (forall (tsk : Task) (n : Nat) (t : Prosa_Behavior_Time_instant),
        @eq Bool
          (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
             (List_instDecidableMemOfLawfulBEq Task
                (instBEqOfDecidableEq Task
                   inst_3)
                (instLawfulBEq Task
                   inst_3)
                tsk ts))
          Bool_true ->
        @eq Nat (List_length Job (generate_jobs_at tsk n t)) n) ->
       (forall (tsk : Task) (n : Nat) (t : Prosa_Behavior_Time_instant) (j : Job),
        @eq Bool
          (Decidable_decide
             (Membership_mem Job (List Job) (List_instMembership Job) (generate_jobs_at tsk n t) j)
             (List_instDecidableMemOfLawfulBEq Job
                (instBEqOfDecidableEq Job
                   inst_10)
                (instLawfulBEq Job
                   inst_10)
                j (generate_jobs_at tsk n t)))
          Bool_true ->
        And
          (@eq Task
             (Prosa_Model_Task_Concept_JobTask_job_task Job
                inst_10 Task
                inst_3
                inst_13 j)
             tsk)
          (And
             (@eq Prosa_Behavior_Time_instant
                (Prosa_Behavior_Job_JobArrival_job_arrival Job
                   inst_10
                   inst_17 j)
                t)
             (LE_le_inst1 Prosa_Behavior_Job_work instLENat
                (Prosa_Behavior_Job_JobCost_job_cost Job
                   inst_10
                   inst_20 j)
                (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                   inst_3
                   inst_6 tsk)))) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13
         (Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence Task
            inst_3 Job
            inst_10
            inst_26
            generate_jobs_at ts)
         inst_26 ts
```
