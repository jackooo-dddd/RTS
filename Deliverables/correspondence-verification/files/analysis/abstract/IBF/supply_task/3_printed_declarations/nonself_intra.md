# `nonself_intra`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.IBF.supply_task.nonself_intra`
- Lean: `Prosa.Analysis.Abstract.IBF.SupplyTask.nonself_intra`
- Certificate: `nonself_intra_correspondence`

## Official Rocq

```coq
nonself_intra :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

nonself_intra is not universe polymorphic
Arguments nonself_intra {Job Task H PState} arr_seq sched j t
nonself_intra is transparent
Expands to: Constant prosa.analysis.abstract.IBF.supply_task.nonself_intra
Declared in library prosa.analysis.abstract.IBF.supply_task, line 46, characters 13-26
@nonself_intra
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
nonself_intra =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t : instant) =>
@nonself Job Task H PState arr_seq sched j t && @has_supply Job PState sched t
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments nonself_intra {Job Task H PState} arr_seq sched j t
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.SupplyTask.nonself_intra : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Abstract.IBF.SupplyTask.nonself_intra.{u_1, u_2, u_3, u_4} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    j t =>
  Prosa.Analysis.Abstract.IBF.Task.nonself arr_seq sched j t && Prosa.Model.Processor.Supply.has_supply sched t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_SupplyTask_nonself_intra
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
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Abstract_IBF_SupplyTask_nonself_intra@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.max__u_1+1_u_3+2_u_4+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0
Lean.u_4+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_3 Task
     inst_7)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Bool_and
  (Prosa_Analysis_Abstract_IBF_Task_nonself Job
     inst_3 Task
     inst_7
     inst_10 PState arr_seq sched j t)
  (Prosa_Model_Processor_Supply_has_supply Job
     inst_3 PState sched t)
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
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Abstract_IBF_SupplyTask_nonself_intra Job
  inst_3 Task
  inst_7
  inst_10 PState arr_seq 
  sched j t
```
