# `earlier_arrival_implies_lower_index`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.earlier_arrival_implies_lower_index`
- Lean: `Prosa.Analysis.Facts.JobIndex.earlier_arrival_implies_lower_index`
- Certificate: `earlier_arrival_implies_lower_index_correspondence`

## Official Rocq

```coq
earlier_arrival_implies_lower_index :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall j1 j2 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@arrives_in Job arr_seq j2 ->
@job_task Job Task H j1 = @job_task Job Task H j2 ->
is_true (@job_arrival Job H0 j1 < @job_arrival Job H0 j2) ->
is_true (@job_index Task Job H0 H arr_seq j1 < @job_index Task Job H0 H arr_seq j2)

earlier_arrival_implies_lower_index is not universe polymorphic
Arguments earlier_arrival_implies_lower_index {Task Job H H0} arr_seq H_valid_arrival_sequence 
  j1 j2 H_j1_from_arrival_sequence H_j2_from_arrival_sequence H_same_task _
earlier_arrival_implies_lower_index is opaque
Expands to: Constant prosa.analysis.facts.job_index.earlier_arrival_implies_lower_index
Declared in library prosa.analysis.facts.job_index, line 201, characters 8-43
@earlier_arrival_implies_lower_index
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall j1 j2 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @arrives_in Job arr_seq j2 ->
       @job_task Job Task H j1 = @job_task Job Task H j2 ->
       is_true (@job_arrival Job H0 j1 < @job_arrival Job H0 j2) ->
       is_true (@job_index Task Job H0 H arr_seq j1 < @job_index Task Job H0 H arr_seq j2)
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.earlier_arrival_implies_lower_index : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j1 j2 : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j2 →
          Prosa.Model.Task.Concept.job_task j1 = Prosa.Model.Task.Concept.job_task j2 →
            Prosa.Behavior.Job.job_arrival j1 < Prosa.Behavior.Job.job_arrival j2 →
              Prosa.Model.Task.Arrivals.job_index arr_seq j1 < Prosa.Model.Task.Arrivals.job_index arr_seq j2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_earlier_arrival_implies_lower_index
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (inst_14 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall j1 j2 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j1 ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j2 ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_7 Task
            inst_3
            inst_10 j1)
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_7 Task
            inst_3
            inst_10 j2) ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_7
            inst_14 j1)
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_7
            inst_14 j2) ->
       LT_lt_inst1 Nat instLTNat
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_7
            inst_14
            inst_10 arr_seq j1)
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_7
            inst_14
            inst_10 arr_seq j2)
```
