# `first_job_arrival`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.offset.first_job_arrival`
- Lean: `Prosa.Analysis.Facts.Model.Offset.first_job_arrival`
- Certificate: `first_job_arrival_correspondence`

## Official Rocq

```coq
first_job_arrival :
forall {Task : TaskType} {H : TaskOffset Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job),
@job_task Job Task H0 j = tsk ->
@valid_offset Task H Job H0 H1 arr_seq tsk ->
@arrives_in Job arr_seq j ->
@job_index Task Job H1 H0 arr_seq j = 0 -> @job_arrival Job H1 j = @task_offset Task H tsk

first_job_arrival is not universe polymorphic
Arguments first_job_arrival {Task H Job H0 H1} arr_seq H_valid_arrival_sequence tsk 
  j H_job_of_task H_valid_offset H_job_from_arrseq _
first_job_arrival is opaque
Expands to: Constant prosa.analysis.facts.model.offset.first_job_arrival
Declared in library prosa.analysis.facts.model.offset, line 30, characters 8-25
@first_job_arrival
     : forall (Task : TaskType) (H : TaskOffset Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job),
       @job_task Job Task H0 j = tsk ->
       @valid_offset Task H Job H0 H1 arr_seq tsk ->
       @arrives_in Job arr_seq j ->
       @job_index Task Job H1 H0 arr_seq j = 0 -> @job_arrival Job H1 j = @task_offset Task H tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Offset.first_job_arrival : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task) (j : Job),
      Prosa.Model.Task.Concept.job_task j = tsk →
        Prosa.Model.Task.Offset.valid_offset arr_seq tsk →
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
            Prosa.Model.Task.Arrivals.job_index arr_seq j = 0 →
              Prosa.Behavior.Job.job_arrival j = Prosa.Model.Task.Offset.task_offset tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Offset_first_job_arrival
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Offset_TaskOffset Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall (tsk : Task) (j : Job),
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_10 Task
            inst_3
            inst_13 j)
         tsk ->
       Prosa_Model_Task_Offset_valid_offset Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j ->
       @eq Nat
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_10
            inst_17
            inst_13 arr_seq j)
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) ->
       @eq Prosa_Behavior_Time_instant
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_10
            inst_17 j)
         (Prosa_Model_Task_Offset_TaskOffset_task_offset Task
            inst_3
            inst_6 tsk)
```
