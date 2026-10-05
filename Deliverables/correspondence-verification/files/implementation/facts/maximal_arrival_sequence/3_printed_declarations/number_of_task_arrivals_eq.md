# `number_of_task_arrivals_eq`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.number_of_task_arrivals_eq`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.number_of_task_arrivals_eq`
- Certificate: `number_of_task_arrivals_eq_correspondence`

## Official Rocq

```coq
number_of_task_arrivals_eq :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {H2 : JobCost Job} (ts : seq (Equality.sort Task)),
is_true (@uniq Task ts) ->
forall {H3 : MaxArrivals Task}
  (generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)),
(forall (tsk : Equality.sort Task) (n : nat) (t : instant),
 is_true (tsk \in ts) -> @size (Equality.sort Job) (generate_jobs_at tsk n t) = n) ->
(forall (tsk : Equality.sort Task) (n : nat) (t : instant) (j : Equality.sort Job),
 is_true (j \in generate_jobs_at tsk n t) ->
 @job_task Job Task H0 j = tsk /\
 @job_arrival Job H1 j = t /\ is_true (@job_cost Job H2 j <= @task_cost Task H tsk)) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall t1 t2 : instant,
@number_of_task_arrivals Job Task H0 (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts) tsk t1 t2 =
\sum_(t1 <= t < t2) @max_arrivals_at Task H3 tsk t

number_of_task_arrivals_eq is not universe polymorphic
Arguments number_of_task_arrivals_eq {Task H Job H0 H1 H2} ts%seq_scope H_ts_uniq 
  {H3} (generate_jobs_at H_job_generation_valid_number H_job_generation_valid_jobs)%function_scope 
  tsk H_tsk_in_ts t1 t2
number_of_task_arrivals_eq is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.number_of_task_arrivals_eq
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 126, characters 10-36
@number_of_task_arrivals_eq
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (H2 : JobCost Job) (ts : seq (Equality.sort Task)),
       is_true (@uniq Task ts) ->
       forall (H3 : MaxArrivals Task)
         (generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)),
       (forall (tsk : Equality.sort Task) (n : nat) (t : instant),
        is_true (tsk \in ts) -> @size (Equality.sort Job) (generate_jobs_at tsk n t) = n) ->
       (forall (tsk : Equality.sort Task) (n : nat) (t : instant) (j : Equality.sort Job),
        is_true (j \in generate_jobs_at tsk n t) ->
        @job_task Job Task H0 j = tsk /\
        @job_arrival Job H1 j = t /\ is_true (@job_cost Job H2 j <= @task_cost Task H tsk)) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall t1 t2 : instant,
       @number_of_task_arrivals Job Task H0 (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts) tsk
         t1 t2 =
       \sum_(t1 <= t < t2) @max_arrivals_at Task H3 tsk t
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.number_of_task_arrivals_eq : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job] (ts : List Task),
  ts.Nodup →
    ∀ [inst_6 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
      (generate_jobs_at : Task → ℕ → Prosa.Behavior.Time.instant → List Job),
      (∀ (tsk : Task) (n : ℕ) (t : Prosa.Behavior.Time.instant),
          decide (tsk ∈ ts) = true → (generate_jobs_at tsk n t).length = n) →
        (∀ (tsk : Task) (n : ℕ) (t : Prosa.Behavior.Time.instant) (j : Job),
            decide (j ∈ generate_jobs_at tsk n t) = true →
              Prosa.Model.Task.Concept.job_task j = tsk ∧
                Prosa.Behavior.Job.job_arrival j = t ∧
                  Prosa.Behavior.Job.job_cost j ≤ Prosa.Model.Task.Concept.task_cost tsk) →
          ∀ (tsk : Task),
            decide (tsk ∈ ts) = true →
              ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                Prosa.Model.Task.Arrivals.number_of_task_arrivals
                    (Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence generate_jobs_at
                      ts)
                    tsk t1 t2 =
                  Prosa.Util.Sum.sumSeq (List.range' t1 (t2 - t1)) fun t =>
                    Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at tsk t
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_number_of_task_arrivals_eq
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
         (inst_26 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (generate_jobs_at : Task -> Nat -> Prosa_Behavior_Time_instant -> List Job),
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
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       @eq Nat
         (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
            inst_10 Task
            inst_3
            inst_13
            (Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence Task
               inst_3 Job
               inst_10
               inst_26
               generate_jobs_at ts)
            tsk t1 t2)
         (Prosa_Util_Sum_sumSeq_inst1 Nat
            (List_range' t1
               (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            (fun t : Nat =>
             Prosa_Implementation_Definitions_MaximalArrivalSequence_max_arrivals_at Task
               inst_3
               inst_26 tsk t))
```
