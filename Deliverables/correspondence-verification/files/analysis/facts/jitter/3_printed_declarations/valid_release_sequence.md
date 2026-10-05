# `valid_release_sequence`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.jitter.valid_release_sequence`
- Lean: `Prosa.Analysis.Facts.Jitter.valid_release_sequence`
- Certificate: `valid_release_sequence_correspondence`

## Official Rocq

```coq
valid_release_sequence :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {original_arrival : JobArrival Job}
  {H0 : TaskJitter Task} {H1 : JobJitter Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job original_arrival arr_seq ->
forall ts : seq (Equality.sort Task),
@valid_jitter_bounds Task H0 Job H H1 ts ->
@valid_arrival_sequence Job (@release_as_arrival Job original_arrival H1)
  (@release_sequence Job original_arrival H1 arr_seq)

valid_release_sequence is not universe polymorphic
Arguments valid_release_sequence {Task Job H original_arrival H0 H1} arr_seq H_valid_arrival_sequence
  ts%seq_scope H_valid_jitter
valid_release_sequence is opaque
Expands to: Constant prosa.analysis.facts.jitter.valid_release_sequence
Declared in library prosa.analysis.facts.jitter, line 58, characters 12-34
@valid_release_sequence
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (original_arrival : JobArrival Job)
         (H0 : TaskJitter Task) (H1 : JobJitter Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job original_arrival arr_seq ->
       forall ts : seq (Equality.sort Task),
       @valid_jitter_bounds Task H0 Job H H1 ts ->
       @valid_arrival_sequence Job (@release_as_arrival Job original_arrival H1)
         (@release_sequence Job original_arrival H1 arr_seq)
```

## Lean

```lean
@Prosa.Analysis.Facts.Jitter.valid_release_sequence : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (original_arrival : Prosa.Behavior.Job.JobArrival Job)
  [inst_3 : Prosa.Model.Task.Jitter.TaskJitter Task] [inst_4 : Prosa.Model.Readiness.Jitter.JobJitter Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Jitter.valid_jitter_bounds ts →
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence
          (Prosa.Analysis.Definitions.DelayPropagation.release_sequence original_arrival arr_seq)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Jitter_valid_release_sequence
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
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         (Prosa_Analysis_Facts_Jitter_release_as_arrival Job
            inst_7 original_arrival
            inst_19)
         (Prosa_Analysis_Definitions_DelayPropagation_release_sequence Job
            inst_7 original_arrival
            inst_19 arr_seq)
```
