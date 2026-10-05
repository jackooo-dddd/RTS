# `sequential_tasks`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.sequentiality.sequential_tasks`
- Lean: `Prosa.Model.Task.Sequentiality.sequential_tasks`
- Certificate: `sequential_tasks_correspondence`

## Official Rocq

```coq
sequential_tasks :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job -> forall {PState : ProcessorState Job}, arrival_sequence Job -> @schedule Job PState -> Prop

sequential_tasks is not universe polymorphic
Arguments sequential_tasks {Job Task H H0 H1 PState} arr_seq sched
sequential_tasks is transparent
Expands to: Constant prosa.model.task.sequentiality.sequential_tasks
Declared in library prosa.model.task.sequentiality, line 30, characters 13-29
@sequential_tasks
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job, arrival_sequence Job -> @schedule Job PState -> Prop
```

Body:

```coq
sequential_tasks =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : JobArrival Job) 
  (H1 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) =>
forall (j1 j2 : Equality.sort Job) (t : instant),
@arrives_in Job arr_seq j1 ->
@arrives_in Job arr_seq j2 ->
is_true (@same_task Job Task H j1 j2) ->
is_true (@job_arrival Job H0 j1 < @job_arrival Job H0 j2) ->
is_true (@scheduled_at Job PState sched j2 t) -> is_true (@completed_by Job PState sched H1 j1 t)
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job}, arrival_sequence Job -> @schedule Job PState -> Prop

Arguments sequential_tasks {Job Task H H0 H1 PState} arr_seq sched
```

## Lean

```lean
@Prosa.Model.Task.Sequentiality.sequential_tasks : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop
def Prosa.Model.Task.Sequentiality.sequential_tasks.{u_1, u_2, u_3, u_4} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched =>
  ∀ (j1 j2 : Job) (t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j2 →
        Prosa.Model.Task.Concept.same_task j1 j2 = true →
          Prosa.Behavior.Job.job_arrival j1 < Prosa.Behavior.Job.job_arrival j2 →
            Prosa.Behavior.Service.scheduled_at sched j2 t = true →
              Prosa.Behavior.Service.completed_by sched j1 t = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Sequentiality_sequential_tasks
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Model_Task_Sequentiality_sequential_tasks@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
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
  (inst_14 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3)
  (inst_17 : Prosa_Behavior_Job_JobCost Job
                                                                            inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall (j1 j2 : Job) (t : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j1 ->
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j2 ->
@eq Bool
  (Prosa_Model_Task_Concept_same_task Job inst_3
     Task inst_7
     inst_10 j1 j2)
  Bool_true ->
LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_3
     inst_14 j1)
  (Prosa_Behavior_Job_JobArrival_job_arrival Job
     inst_3
     inst_14 j2) ->
@eq Bool
  (Prosa_Behavior_Service_scheduled_at Job
     inst_3 PState sched j2 t)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_completed_by Job
     inst_3 PState sched
     inst_17 j1 t)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Behavior_Job_JobCost Job inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Model_Task_Sequentiality_sequential_tasks Job
  inst_3 Task
  inst_7
  inst_10
  inst_14
  inst_17 PState arr_seq 
  sched
```
