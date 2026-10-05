# `task_service_during`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.task_schedule.task_service_during`
- Lean: `Prosa.Analysis.Definitions.TaskSchedule.task_service_during`
- Certificate: `task_service_during_correspondence`

## Official Rocq

```coq
task_service_during :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
arrival_sequence Job ->
forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Task -> instant -> instant -> nat

task_service_during is not universe polymorphic
Arguments task_service_during {Task Job H0} arr_seq {PState} sched tsk t1 t2
task_service_during is transparent
Expands to: Constant prosa.analysis.definitions.task_schedule.task_service_during
Declared in library prosa.analysis.definitions.task_schedule, line 47, characters 13-32
@task_service_during
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       arrival_sequence Job ->
       forall PState : ProcessorState Job,
       @schedule Job PState -> Equality.sort Task -> instant -> instant -> nat
```

Body:

```coq
task_service_during =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (PState : ProcessorState Job) (sched : @schedule Job PState) (tsk : Equality.sort Task) 
  (t1 t2 : instant) =>
\sum_(t1 <= t < t2) @task_service_at Task Job H0 arr_seq PState sched tsk t
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       arrival_sequence Job ->
       forall {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Task -> instant -> instant -> nat

Arguments task_service_during {Task Job H0} arr_seq {PState} sched tsk t1 t2
```

## Lean

```lean
@Prosa.Analysis.Definitions.TaskSchedule.task_service_during : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                Task → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work
def Prosa.Analysis.Definitions.TaskSchedule.task_service_during.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                Task → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    tsk t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2, Prosa.Analysis.Definitions.TaskSchedule.task_service_at arr_seq sched tsk t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_TaskSchedule_task_service_during
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Task -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Analysis_Definitions_TaskSchedule_task_service_during@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : 
   DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7
     Task
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7
             PState)
  (tsk : Task) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_foldr_inst3 Nat Prosa_Behavior_Job_work Nat_add
  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (List_map_inst3 Prosa_Behavior_Time_instant Nat
     (fun t : Prosa_Behavior_Time_instant =>
      Prosa_Analysis_Definitions_TaskSchedule_task_service_at Task
        inst_3
        Job
        inst_7
        inst_10
        PState arr_seq sched tsk t)
     (List_range' t1
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Task -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Job_work

Arguments Prosa_Analysis_Definitions_TaskSchedule_task_service_during Task
  inst_3 Job
  inst_7
  inst_10 PState 
  arr_seq sched tsk t1 t
```
