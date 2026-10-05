# `sequential_tasks_from_readiness`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sequential.sequential_tasks_from_readiness`
- Lean: `Prosa.Analysis.Facts.Model.Sequential.sequential_tasks_from_readiness`
- Certificate: `sequential_tasks_from_readiness_correspondence`

## Official Rocq

```coq
sequential_tasks_from_readiness :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job} 
  {H1 : JobCost Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall {JR : @JobReady Job PState H1 H0},
@sequential_readiness Job H1 H0 PState JR Task H arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job H0 PState sched H1 JR arr_seq -> @sequential_tasks Job Task H H0 H1 PState arr_seq sched

sequential_tasks_from_readiness is not universe polymorphic
Arguments sequential_tasks_from_readiness {Job Task H H0 H1 PState} arr_seq H_arrival_times_are_consistent
  {JR} H_sequential sched H_valid_schedule j1 j2 t _ _ _ _ _
sequential_tasks_from_readiness is opaque
Expands to: Constant prosa.analysis.facts.model.sequential.sequential_tasks_from_readiness
Declared in library prosa.analysis.facts.model.sequential, line 94, characters 8-39
@sequential_tasks_from_readiness
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall JR : @JobReady Job PState H1 H0,
       @sequential_readiness Job H1 H0 PState JR Task H arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H0 PState sched H1 JR arr_seq ->
       @sequential_tasks Job Task H H0 H1 PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sequential.sequential_tasks_from_readiness : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (JR : Prosa.Behavior.Ready.JobReady Job PState),
      Prosa.Analysis.Definitions.Readiness.sequential_readiness JR arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sequential_sequential_tasks_from_readiness
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
       Prosa_Behavior_Arrival_sequence_consistent_arrival_times Job
         inst_3
         inst_14 arr_seq ->
       forall
         JR : Prosa_Behavior_Ready_JobReady Job
                inst_3 PState
                inst_17
                inst_14,
       Prosa_Analysis_Definitions_Readiness_sequential_readiness Job
         inst_3
         inst_17
         inst_14 PState JR Task
         inst_7
         inst_10 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_14 PState sched
         inst_17 JR arr_seq ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_10
         inst_14
         inst_17 PState arr_seq sched
```
