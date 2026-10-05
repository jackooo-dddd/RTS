# `jitter_arrives_in_iff`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.jitter.jitter_arrives_in_iff`
- Lean: `Prosa.Analysis.Facts.Jitter.jitter_arrives_in_iff`
- Certificate: `jitter_arrives_in_iff_correspondence`

## Official Rocq

```coq
jitter_arrives_in_iff :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {original_arrival : JobArrival Job}
  {H0 : TaskJitter Task} {H1 : JobJitter Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job original_arrival arr_seq ->
forall ts : seq (Equality.sort Task),
@valid_jitter_bounds Task H0 Job H H1 ts ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j <-> @arrives_in Job (@release_sequence Job original_arrival H1 arr_seq) j

jitter_arrives_in_iff is not universe polymorphic
Arguments jitter_arrives_in_iff {Task Job H original_arrival H0 H1} arr_seq H_valid_arrival_sequence
  ts%seq_scope H_valid_jitter j
jitter_arrives_in_iff is opaque
Expands to: Constant prosa.analysis.facts.jitter.jitter_arrives_in_iff
Declared in library prosa.analysis.facts.jitter, line 47, characters 12-33
@jitter_arrives_in_iff
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (original_arrival : JobArrival Job)
         (H0 : TaskJitter Task) (H1 : JobJitter Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job original_arrival arr_seq ->
       forall ts : seq (Equality.sort Task),
       @valid_jitter_bounds Task H0 Job H H1 ts ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j <-> @arrives_in Job (@release_sequence Job original_arrival H1 arr_seq) j
```

## Lean

```lean
@Prosa.Analysis.Facts.Jitter.jitter_arrives_in_iff : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (original_arrival : Prosa.Behavior.Job.JobArrival Job)
  [inst_3 : Prosa.Model.Task.Jitter.TaskJitter Task] [inst_4 : Prosa.Model.Readiness.Jitter.JobJitter Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Jitter.valid_jitter_bounds ts →
        ∀ (j : Job),
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j ↔
            Prosa.Behavior.Arrival_sequence.arrives_in
              (Prosa.Analysis.Definitions.DelayPropagation.release_sequence original_arrival arr_seq) j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Jitter_jitter_arrives_in_iff
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (original_arrival : Prosa_Behavior_Job_JobArrival Job
                               inst_7)
         (inst_16 : Prosa_Model_Task_Jitter_TaskJitter
                                                                                Task
                                                                                inst_3)
         (inst_19 : Prosa_Model_Readiness_Jitter_JobJitter
                                                                                Job
                                                                                inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7 original_arrival arr_seq ->
       forall ts : Prosa_Model_Task_Concept_TaskSet Task,
       Prosa_Model_Task_Jitter_valid_jitter_bounds Task
         inst_3
         inst_16 Job
         inst_7
         inst_10
         inst_19 ts ->
       forall j : Job,
       Iff
         (Prosa_Behavior_Arrival_sequence_arrives_in Job
            inst_7 arr_seq j)
         (Prosa_Behavior_Arrival_sequence_arrives_in Job
            inst_7
            (Prosa_Analysis_Definitions_DelayPropagation_release_sequence Job
               inst_7 original_arrival
               inst_19 arr_seq)
            j)
```
