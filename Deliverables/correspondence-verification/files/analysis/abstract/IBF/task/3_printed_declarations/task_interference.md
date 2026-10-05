# `task_interference`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.IBF.task.task_interference`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.task_interference`
- Certificate: `task_interference_correspondence`

## Official Rocq

```coq
task_interference :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> Interference Job -> Equality.sort Job -> instant -> bool

task_interference is not universe polymorphic
Arguments task_interference {Job Task H PState} arr_seq sched {H2} j t
task_interference is transparent
Expands to: Constant prosa.analysis.abstract.IBF.task.task_interference
Declared in library prosa.analysis.abstract.IBF.task, line 57, characters 13-30
@task_interference
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> Interference Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
task_interference =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (H2 : Interference Job)
  (j : Equality.sort Job) =>
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> Interference Job -> Equality.sort Job -> instant -> bool

Arguments task_interference {Job Task H PState} arr_seq sched {H2} j t
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.task_interference : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Analysis.Abstract.Definitions.Interference Job] → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Abstract.IBF.Task.task_interference.{u_1, u_2, u_3, u_4} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Analysis.Abstract.Definitions.Interference Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    [Prosa.Analysis.Abstract.Definitions.Interference Job] j t =>
  Prosa.Analysis.Abstract.Definitions.cond_interference (Prosa.Analysis.Abstract.IBF.Task.nonself arr_seq sched) j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_task_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Abstract_IBF_Task_task_interference@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.max__u_1+1_u_3+2_u_4+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0
Lean.u_4+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                              Job
                                                                              inst_3
                                                                              Task
                                                                              inst_7)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_20 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                              Job
                                                                              inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Prosa_Analysis_Abstract_Definitions_cond_interference Job
  inst_3
  inst_20
  (Prosa_Analysis_Abstract_IBF_Task_nonself Job
     inst_3 Task
     inst_7
     inst_10 PState arr_seq sched)
  j t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Abstract_IBF_Task_task_interference Job
  inst_3 Task
  inst_7
  inst_10 PState arr_seq 
  sched inst_20 j 
  t
```
