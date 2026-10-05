# `sequential_readiness_implies_work_bearing_readiness`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_work_bearing_readiness`
- Lean: `Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_implies_work_bearing_readiness`
- Certificate: `sequential_readiness_implies_work_bearing_readiness_correspondence`

## Official Rocq

```coq
sequential_readiness_implies_work_bearing_readiness :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} {H0 : JobArrival Job} 
  {H1 : JobCost Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@consistent_arrival_times Job H0 arr_seq ->
forall (sched : @schedule Job PState) {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@work_bearing_readiness Job H0 H1 PState (@sequential_readiness_instance Job Task H H0 H1 PState arr_seq)
  arr_seq sched (@FP_to_JLFP Job Task H FP)

sequential_readiness_implies_work_bearing_readiness is not universe polymorphic
Arguments sequential_readiness_implies_work_bearing_readiness {Job Task H H0 H1 PState} 
  arr_seq H_arrival_times_are_consistent sched {FP} H_priority_is_reflexive j t _ 
  _
sequential_readiness_implies_work_bearing_readiness is opaque
Expands to: Constant
            prosa.analysis.facts.readiness.sequential.sequential_readiness_implies_work_bearing_readiness
Declared in library prosa.analysis.facts.readiness.sequential, line 83, characters 8-59
@sequential_readiness_implies_work_bearing_readiness
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job),
       @consistent_arrival_times Job H0 arr_seq ->
       forall (sched : @schedule Job PState) (FP : FP_policy Task),
       @reflexive_task_priorities Task FP ->
       @work_bearing_readiness Job H0 H1 PState
         (@sequential_readiness_instance Job Task H H0 H1 PState arr_seq) arr_seq sched
         (@FP_to_JLFP Job Task H FP)
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_implies_work_bearing_readiness : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.consistent_arrival_times arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
      Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
        Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Sequential_sequential_readiness_implies_work_bearing_readiness
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
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_7),
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_7 FP ->
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_14
         inst_17 PState
         (Prosa_Analysis_Facts_Readiness_Sequential_sequential_readiness_instance Job
            inst_3 Task
            inst_7
            inst_10
            inst_14
            inst_17 PState arr_seq)
         arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_3 Task
            inst_7
            inst_10 FP)
```
