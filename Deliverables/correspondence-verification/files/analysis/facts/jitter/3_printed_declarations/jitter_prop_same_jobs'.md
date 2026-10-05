# `jitter_prop_same_jobs'`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.jitter.jitter_prop_same_jobs'`
- Lean: `Prosa.Analysis.Facts.Jitter.jitter_prop_same_jobs'`
- Certificate: `jitter_prop_same_jobs'_correspondence`

## Official Rocq

```coq
jitter_prop_same_jobs' :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {original_arrival : JobArrival Job}
  {H0 : TaskJitter Task} {H1 : JobJitter Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job original_arrival arr_seq ->
forall ts : seq (Equality.sort Task),
@valid_jitter_bounds Task H0 Job H H1 ts ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_come_from_arrival_sequence Job PState sched (@release_sequence Job original_arrival H1 arr_seq)

jitter_prop_same_jobs' is not universe polymorphic
Arguments jitter_prop_same_jobs' {Task Job H original_arrival H0 H1} arr_seq H_valid_arrival_sequence
  ts%seq_scope H_valid_jitter {PState} sched _ j t _
jitter_prop_same_jobs' is opaque
Expands to: Constant prosa.analysis.facts.jitter.jitter_prop_same_jobs'
Declared in library prosa.analysis.facts.jitter, line 109, characters 8-30
@jitter_prop_same_jobs'
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (original_arrival : JobArrival Job)
         (H0 : TaskJitter Task) (H1 : JobJitter Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job original_arrival arr_seq ->
       forall ts : seq (Equality.sort Task),
       @valid_jitter_bounds Task H0 Job H H1 ts ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_come_from_arrival_sequence Job PState sched (@release_sequence Job original_arrival H1 arr_seq)
```

## Lean

```lean
@Prosa.Analysis.Facts.Jitter.jitter_prop_same_jobs' : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (original_arrival : Prosa.Behavior.Job.JobArrival Job)
  [inst_3 : Prosa.Model.Task.Jitter.TaskJitter Task] [inst_4 : Prosa.Model.Readiness.Jitter.JobJitter Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Jitter.valid_jitter_bounds ts →
        ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job) (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched
              (Prosa.Analysis.Definitions.DelayPropagation.release_sequence original_arrival arr_seq)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Jitter_jitter_prop_same_jobs'
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
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState sched
         (Prosa_Analysis_Definitions_DelayPropagation_release_sequence Job
            inst_7 original_arrival
            inst_19 arr_seq)
```
