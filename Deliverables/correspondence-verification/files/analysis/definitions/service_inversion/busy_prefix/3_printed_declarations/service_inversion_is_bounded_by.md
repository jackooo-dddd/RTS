# `service_inversion_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_is_bounded_by`
- Lean: `Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_is_bounded_by`
- Certificate: `service_inversion_is_bounded_by_correspondence`

## Official Rocq

```coq
service_inversion_is_bounded_by :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> JLFP_policy Job -> Equality.sort Task -> (duration -> duration) -> Prop

service_inversion_is_bounded_by is not universe polymorphic
Arguments service_inversion_is_bounded_by {Task Job H0 H1 H2 PState} arr_seq sched {H3} tsk B%function_scope
service_inversion_is_bounded_by is transparent
Expands to: Constant prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_is_bounded_by
Declared in library prosa.analysis.definitions.service_inversion.busy_prefix, line 48, characters 13-44
@service_inversion_is_bounded_by
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Task -> (duration -> duration) -> Prop
```

Body:

```coq
service_inversion_is_bounded_by =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job) 
  (H2 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H3 : JLFP_policy Job) (tsk : Equality.sort Task) =>
       (@JLFP_to_JLDP Job H3) (@busy_interval_prefix Job H1 H2 PState arr_seq sched H3) tsk]
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Task -> (duration -> duration) -> Prop

Arguments service_inversion_is_bounded_by {Task Job H0 H1 H2 PState} arr_seq sched {H3} tsk B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_is_bounded_by : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState →
                    [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                      Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_is_bounded_by.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Behavior.Job.JobCost Job] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState →
                    [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                      Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] tsk B =>
  Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_is_bounded_by arr_seq sched
    (Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched) tsk B
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_10 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_10 ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by@{u_1 u_2 u_3 u_4
Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0
Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : 
   DecidableEq Job)
  (inst_13 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_10 Task
     inst_3)
  (inst_17 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_10)
  (inst_20 : 
   Prosa_Behavior_Job_JobCost Job
     inst_10)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_10
             PState)
  (inst_29 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_10)
  (tsk : Task) (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by Task
  inst_3 Job
  inst_10
  inst_13
  inst_17
  inst_20 PState arr_seq
  sched
  (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
     inst_10
     inst_29)
  (Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
     inst_10
     inst_17
     inst_20 PState
     arr_seq sched
     inst_29)
  tsk B
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_10 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_10 ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by 
  Task inst_3 
  Job inst_10
  inst_13
  inst_17
  inst_20 
  PState arr_seq sched
  inst_29 
  tsk B%_function_scope
```
