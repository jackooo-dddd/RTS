# `jitter_arr_seq_mapping_valid`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.definitions.delay_propagation.jitter_arr_seq_mapping_valid`
- Lean: `Prosa.Analysis.Definitions.DelayPropagation.jitter_arr_seq_mapping_valid`
- Certificate: `jitter_arr_seq_mapping_valid_correspondence`

## Official Rocq

```coq
jitter_arr_seq_mapping_valid :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {original_arrival : JobArrival Job}
  {H1 : TaskJitter Task} {H2 : JobJitter Job} (ts : TaskSet (Equality.sort Task))
  (arr_seq : arrival_sequence Job),
@valid_jitter_bounds Task H1 Job H0 H2 ts ->
@valid_arr_seq_propagation_mapping Task Job Job H0 original_arrival
  (@release_as_arrival Job original_arrival H2) id (@task_jitter Task H1) arr_seq
  ((@cons (Equality.sort Job))^~ [::]) (@job_jitter Job H2) ts

jitter_arr_seq_mapping_valid is not universe polymorphic
Arguments jitter_arr_seq_mapping_valid {Task Job H0 original_arrival H1 H2} ts arr_seq _
jitter_arr_seq_mapping_valid is opaque
Expands to: Constant prosa.analysis.definitions.delay_propagation.jitter_arr_seq_mapping_valid
Declared in library prosa.analysis.definitions.delay_propagation, line 190, characters 9-37
@jitter_arr_seq_mapping_valid
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (original_arrival : JobArrival Job)
         (H1 : TaskJitter Task) (H2 : JobJitter Job) (ts : TaskSet (Equality.sort Task))
         (arr_seq : arrival_sequence Job),
       @valid_jitter_bounds Task H1 Job H0 H2 ts ->
       @valid_arr_seq_propagation_mapping Task Job Job H0 original_arrival
         (@release_as_arrival Job original_arrival H2) id (@task_jitter Task H1) arr_seq
         ((@cons (Equality.sort Job))^~ [::]) (@job_jitter Job H2) ts
```

## Lean

```lean
@Prosa.Analysis.Definitions.DelayPropagation.jitter_arr_seq_mapping_valid : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (original_arrival : Prosa.Behavior.Job.JobArrival Job)
  [inst_3 : Prosa.Model.Task.Jitter.TaskJitter Task] [inst_4 : Prosa.Model.Readiness.Jitter.JobJitter Job]
  (ts : Prosa.Model.Task.Concept.TaskSet Task) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Jitter.valid_jitter_bounds ts →
    Prosa.Analysis.Definitions.DelayPropagation.valid_arr_seq_propagation_mapping original_arrival
      { job_arrival := fun j => Prosa.Behavior.Job.job_arrival j + Prosa.Model.Readiness.Jitter.job_jitter j } id
      Prosa.Model.Task.Jitter.task_jitter arr_seq (fun j => [j]) Prosa.Model.Readiness.Jitter.job_jitter ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DelayPropagation_jitter_arr_seq_mapping_valid
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (original_arrival : Prosa_Behavior_Job_JobArrival Job
                               inst_7)
         (inst_16 : 
          Prosa_Model_Task_Jitter_TaskJitter Task
            inst_3)
         (inst_19 : 
          Prosa_Model_Readiness_Jitter_JobJitter Job
            inst_7)
         (ts : Prosa_Model_Task_Concept_TaskSet Task)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Model_Task_Jitter_valid_jitter_bounds Task
         inst_3
         inst_16 Job
         inst_7
         inst_10
         inst_19 ts ->
       Prosa_Analysis_Definitions_DelayPropagation_valid_arr_seq_propagation_mapping Task
         inst_3 Job Job
         inst_7
         inst_7
         inst_10 original_arrival
         (Prosa_Behavior_Job_JobArrival_mk Job
            inst_7
            (fun j : Job =>
             HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_7
                  original_arrival j)
               (Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job
                  inst_7
                  inst_19 j)))
         (id Job)
         (Prosa_Model_Task_Jitter_TaskJitter_task_jitter Task
            inst_3
            inst_16)
         arr_seq (fun j : Job => List_cons Job j (List_nil Job))
         (Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job
            inst_7
            inst_19)
         ts
```
