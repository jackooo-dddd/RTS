# `arrival_times_are_consistent`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.arrival_times_are_consistent`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.arrival_times_are_consistent`
- Certificate: `arrival_times_are_consistent_correspondence`

## Official Rocq

```coq
arrival_times_are_consistent :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} (ts : seq (Equality.sort Task)) {H3 : MaxArrivals Task}
  (generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)),
(forall (tsk : Equality.sort Task) (n : nat) (t : instant) (j : Equality.sort Job),
 is_true (j \in generate_jobs_at tsk n t) ->
 @job_task Job Task H0 j = tsk /\
 @job_arrival Job H1 j = t /\ is_true (@job_cost Job H2 j <= @task_cost Task H tsk)) ->
@consistent_arrival_times Job H1 (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts)

arrival_times_are_consistent is not universe polymorphic
Arguments arrival_times_are_consistent {Task H Job H0 H1 H2} ts%seq_scope {H3}
  (generate_jobs_at H_job_generation_valid_jobs)%function_scope j t _
arrival_times_are_consistent is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.arrival_times_are_consistent
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 77, characters 8-36
@arrival_times_are_consistent
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (ts : seq (Equality.sort Task)) 
         (H3 : MaxArrivals Task)
         (generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)),
       (forall (tsk : Equality.sort Task) (n : nat) (t : instant) (j : Equality.sort Job),
        is_true (j \in generate_jobs_at tsk n t) ->
        @job_task Job Task H0 j = tsk /\
        @job_arrival Job H1 j = t /\ is_true (@job_cost Job H2 j <= @task_cost Task H tsk)) ->
       @consistent_arrival_times Job H1 (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts)
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.arrival_times_are_consistent : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job] (ts : List Task)
  [inst_6 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  (generate_jobs_at : Task → ℕ → Prosa.Behavior.Time.instant → List Job),
  (∀ (tsk : Task) (n : ℕ) (t : Prosa.Behavior.Time.instant) (j : Job),
      decide (j ∈ generate_jobs_at tsk n t) = true →
        Prosa.Model.Task.Concept.job_task j = tsk ∧
          Prosa.Behavior.Job.job_arrival j = t ∧
            Prosa.Behavior.Job.job_cost j ≤ Prosa.Model.Task.Concept.task_cost tsk) →
    Prosa.Behavior.Arrival_sequence.consistent_arrival_times
      (Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence generate_jobs_at ts)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_arrival_times_are_consistent
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
         (ts : List Task)
         (inst_25 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (generate_jobs_at : Task -> Nat -> Prosa_Behavior_Time_instant -> List Job),
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
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_10
         inst_17
         (Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence Task
            inst_3 Job
            inst_10
            inst_25
            generate_jobs_at ts)
```
