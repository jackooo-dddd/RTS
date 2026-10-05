# `arrives_in_propagated_only_if`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.delay_propagation.arrives_in_propagated_only_if`
- Lean: `Prosa.Analysis.Facts.DelayPropagation.arrives_in_propagated_only_if`
- Certificate: `arrives_in_propagated_only_if_correspondence`

## Official Rocq

```coq
arrives_in_propagated_only_if :
forall {Task2 : TaskType} {Job1 Job2 : JobType} {H0 : JobTask Job2 Task2} (JA1 : JobArrival Job1)
  (JA2 : JobArrival Job2) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
  (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2)) (arrival_delay : Equality.sort Job2 -> duration)
  (delay_bound : Equality.sort Task2 -> duration) (ts2 : seq (Equality.sort Task2))
  (arr_seq1 : arrival_sequence Job1),
@valid_arr_seq_propagation_mapping Task2 Job1 Job2 H0 JA1 JA2 job1_of delay_bound arr_seq1 job2_of
  arrival_delay ts2 ->
forall j2 : Equality.sort Job2,
@arrives_in Job2 (@propagated_arrival_sequence Job1 Job2 JA1 job1_of arr_seq1 job2_of arrival_delay) j2 ->
@arrives_in Job1 arr_seq1 (job1_of j2)

arrives_in_propagated_only_if is not universe polymorphic
Arguments arrives_in_propagated_only_if {Task2 Job1 Job2 H0} JA1 JA2
  (job1_of job2_of arrival_delay delay_bound)%function_scope ts2%seq_scope arr_seq1 
  H_arr_seq_mapping j2 _
arrives_in_propagated_only_if is opaque
Expands to: Constant prosa.analysis.facts.delay_propagation.arrives_in_propagated_only_if
Declared in library prosa.analysis.facts.delay_propagation, line 132, characters 8-37
@arrives_in_propagated_only_if
     : forall (Task2 : TaskType) (Job1 Job2 : JobType) (H0 : JobTask Job2 Task2) 
         (JA1 : JobArrival Job1) (JA2 : JobArrival Job2) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
         (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2))
         (arrival_delay : Equality.sort Job2 -> duration) (delay_bound : Equality.sort Task2 -> duration)
         (ts2 : seq (Equality.sort Task2)) (arr_seq1 : arrival_sequence Job1),
       @valid_arr_seq_propagation_mapping Task2 Job1 Job2 H0 JA1 JA2 job1_of delay_bound arr_seq1 job2_of
         arrival_delay ts2 ->
       forall j2 : Equality.sort Job2,
       @arrives_in Job2 (@propagated_arrival_sequence Job1 Job2 JA1 job1_of arr_seq1 job2_of arrival_delay)
         j2 ->
       @arrives_in Job1 arr_seq1 (job1_of j2)
```

## Lean

```lean
@Prosa.Analysis.Facts.DelayPropagation.arrives_in_propagated_only_if : ∀ {Task2 : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task2] {Job1 : Prosa.Behavior.Job.JobType} {Job2 : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job1] [inst_2 : DecidableEq Job2] [inst_3 : Prosa.Model.Task.Concept.JobTask Job2 Task2]
  [JA1 : Prosa.Behavior.Job.JobArrival Job1] [JA2 : Prosa.Behavior.Job.JobArrival Job2] (job1_of : Job2 → Job1)
  (job2_of : Job1 → List Job2) (arrival_delay : Job2 → Prosa.Behavior.Time.duration)
  (delay_bound : Task2 → Prosa.Behavior.Time.duration) (ts2 : List Task2)
  (arr_seq1 : Prosa.Behavior.Arrival_sequence.arrival_sequence Job1),
  Prosa.Analysis.Definitions.DelayPropagation.valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1
      job2_of arrival_delay ts2 →
    ∀ (j2 : Job2),
      Prosa.Behavior.Arrival_sequence.arrives_in
          (Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of
            arrival_delay)
          j2 →
        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq1 (job1_of j2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_DelayPropagation_arrives_in_propagated_only_if
     : forall (Task2 : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task2)
         (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_8 : DecidableEq Job1)
         (inst_11 : DecidableEq Job2)
         (inst_14 : 
          Prosa_Model_Task_Concept_JobTask Job2
            inst_11 Task2
            inst_3)
         (JA1 : Prosa_Behavior_Job_JobArrival Job1
                  inst_8)
         (JA2 : Prosa_Behavior_Job_JobArrival Job2
                  inst_11)
         (job1_of : Job2 -> Job1) (job2_of : Job1 -> List Job2)
         (arrival_delay : Job2 -> Prosa_Behavior_Time_duration)
         (delay_bound : Task2 -> Prosa_Behavior_Time_duration) (ts2 : List Task2)
         (arr_seq1 : Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
                       inst_8),
       Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping Task2
         inst_3 Job1 Job2
         inst_8
         inst_11
         inst_14 JA1 JA2 job1_of
         delay_bound arr_seq1 job2_of arrival_delay ts2 ->
       forall j2 : Job2,
       Prosa_Behavior_Arrival_sequence_arrives_in Job2
         inst_11
         (Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence Job1 Job2
            inst_8
            inst_11 JA1 job1_of arr_seq1
            job2_of arrival_delay)
         j2 ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job1
         inst_8 arr_seq1 
         (job1_of j2)
```
