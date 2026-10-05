# `task_tardiness_is_bounded`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.tardiness.task_tardiness_is_bounded`
- Lean: `Prosa.Analysis.Definitions.Tardiness.task_tardiness_is_bounded`
- Certificate: `task_tardiness_is_bounded_correspondence`

## Official Rocq

```coq
task_tardiness_is_bounded :
forall {Task : TaskType},
TaskDeadline Task ->
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> Equality.sort Task -> nat -> Prop

task_tardiness_is_bounded is not universe polymorphic
Arguments task_tardiness_is_bounded {Task H Job H0 H1 H2 PState} arr_seq sched tsk B%nat_scope
task_tardiness_is_bounded is transparent
Expands to: Constant prosa.analysis.definitions.tardiness.task_tardiness_is_bounded
Declared in library prosa.analysis.definitions.tardiness, line 37, characters 13-38
@task_tardiness_is_bounded
     : forall Task : TaskType,
       TaskDeadline Task ->
       forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Task -> nat -> Prop
```

Body:

```coq
task_tardiness_is_bounded =
fun (Task : TaskType) (H : TaskDeadline Task) (Job : JobType) (H0 : JobArrival Job) 
  (H1 : JobCost Job) (H2 : JobTask Job Task) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (B : nat) =>
@task_response_time_bound Task Job H0 H1 H2 PState arr_seq sched tsk (@task_deadline Task H tsk + B)
     : forall {Task : TaskType},
       TaskDeadline Task ->
       forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Task -> nat -> Prop

Arguments task_tardiness_is_bounded {Task H Job H0 H1 H2 PState} arr_seq sched tsk B%nat_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Tardiness.task_tardiness_is_bounded : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskDeadline Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              [Prosa.Model.Task.Concept.JobTask Job Task] →
                {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Tardiness.task_tardiness_is_bounded.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskDeadline Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              [Prosa.Model.Task.Concept.JobTask Job Task] →
                {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskDeadline Task] {Job} [DecidableEq Job]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    {PState} arr_seq sched tsk B =>
  Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched tsk
    (Prosa.Model.Task.Concept.task_deadline tsk + B)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Tardiness_task_tardiness_is_bounded
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_10 PState ->
       Task -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Tardiness_task_tardiness_is_bounded@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskDeadline
                                                                                Task
                                                                                inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_10)
  (inst_16 : Prosa_Behavior_Job_JobCost
                                                                                Job
                                                                                inst_10)
  (inst_19 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_10
                                                                                Task
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_10 PState)
  (tsk : Task) (B : Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
  inst_3 Job
  inst_10
  inst_13
  inst_16
  inst_19 PState arr_seq sched tsk
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
     (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
        inst_3
        inst_6 tsk)
     B)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_10 PState ->
       Task -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Analysis_Definitions_Tardiness_task_tardiness_is_bounded Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_16
  inst_19 PState 
  arr_seq sched tsk R
```
