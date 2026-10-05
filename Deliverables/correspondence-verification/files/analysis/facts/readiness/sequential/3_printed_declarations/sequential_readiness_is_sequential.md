# `sequential_readiness_is_sequential`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.readiness.sequential.sequential_readiness_is_sequential`
- Lean: `Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_is_sequential`
- Certificate: `sequential_readiness_is_sequential_correspondence`

## Official Rocq

```coq
sequential_readiness_is_sequential :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job} 
  {H1 : JobCost Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@sequential_readiness Job H1 H0 PState (@sequential_readiness_instance Job Task H H0 H1 PState arr_seq) Task
  H arr_seq

sequential_readiness_is_sequential is not universe polymorphic
Arguments sequential_readiness_is_sequential {Job Task H H0 H1 PState} arr_seq sched j t _
sequential_readiness_is_sequential is opaque
Expands to: Constant prosa.analysis.facts.readiness.sequential.sequential_readiness_is_sequential
Declared in library prosa.analysis.facts.readiness.sequential, line 35, characters 7-41
@sequential_readiness_is_sequential
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job),
       @sequential_readiness Job H1 H0 PState
         (@sequential_readiness_instance Job Task H H0 H1 PState arr_seq) Task H arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_is_sequential : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Analysis.Definitions.Readiness.sequential_readiness
    (Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_instance arr_seq) arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Sequential_sequential_readiness_is_sequential
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Analysis_Definitions_Readiness_sequential_readiness Job
         inst_3
         inst_17
         inst_14 PState
         (Prosa_Analysis_Facts_Readiness_Sequential_sequential_readiness_instance Job
            inst_3 Task
            inst_7
            inst_10
            inst_14
            inst_17 PState arr_seq)
         Task inst_7
         inst_10 arr_seq
```
