# `arr_seq_is_a_set`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.maximal_arrival_sequence.arr_seq_is_a_set`
- Lean: `Prosa.Implementation.Facts.MaximalArrivalSequence.arr_seq_is_a_set`
- Certificate: `arr_seq_is_a_set_correspondence`

## Official Rocq

```coq
arr_seq_is_a_set :
forall {Task : TaskType} {Job : JobType} (ts : seq (Equality.sort Task)) {H3 : MaxArrivals Task}
  (generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)),
(forall t1 t2 : instant,
 is_true
   (@uniq Job (@arrivals_between Job (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts) t1 t2))) ->
@arrival_sequence_uniq Job (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts)

arr_seq_is_a_set is not universe polymorphic
Arguments arr_seq_is_a_set {Task Job} ts%seq_scope {H3} (generate_jobs_at H_jobs_unique)%function_scope t
arr_seq_is_a_set is opaque
Expands to: Constant prosa.implementation.facts.maximal_arrival_sequence.arr_seq_is_a_set
Declared in library prosa.implementation.facts.maximal_arrival_sequence, line 58, characters 8-24
@arr_seq_is_a_set
     : forall (Task : TaskType) (Job : JobType) (ts : seq (Equality.sort Task)) (H3 : MaxArrivals Task)
         (generate_jobs_at : Equality.sort Task -> nat -> instant -> seq (Equality.sort Job)),
       (forall t1 t2 : instant,
        is_true
          (@uniq Job
             (@arrivals_between Job (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts) t1 t2))) ->
       @arrival_sequence_uniq Job (@concrete_arrival_sequence Task Job H3 generate_jobs_at ts)
```

## Lean

```lean
@Prosa.Implementation.Facts.MaximalArrivalSequence.arr_seq_is_a_set : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job] (ts : List Task)
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  (generate_jobs_at : Task → ℕ → Prosa.Behavior.Time.instant → List Job),
  (∀ (t1 t2 : Prosa.Behavior.Time.instant),
      (Prosa.Behavior.Arrival_sequence.arrivals_between
          (Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence generate_jobs_at ts) t1
          t2).Nodup) →
    Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq
      (Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence generate_jobs_at ts)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_MaximalArrivalSequence_arr_seq_is_a_set
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (ts : List Task)
         (inst_12 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (generate_jobs_at : Task -> Nat -> Prosa_Behavior_Time_instant -> List Job),
       (forall t1 t2 : Prosa_Behavior_Time_instant,
        List_Nodup Job
          (Prosa_Behavior_Arrival_sequence_arrivals_between Job
             inst_7
             (Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence Task
                inst_3 Job
                inst_7
                inst_12
                generate_jobs_at ts)
             t1 t2)) ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_7
         (Prosa_Implementation_Definitions_MaximalArrivalSequence_concrete_arrival_sequence Task
            inst_3 Job
            inst_7
            inst_12
            generate_jobs_at ts)
```
