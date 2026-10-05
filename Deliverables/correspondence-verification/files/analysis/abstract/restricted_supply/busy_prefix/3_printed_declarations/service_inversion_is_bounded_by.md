# `service_inversion_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_is_bounded_by`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.BusyPrefix.service_inversion_is_bounded_by`
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
@schedule Job PState ->
Interference Job ->
InterferingWorkload Job -> JLFP_policy Job -> Equality.sort Task -> (duration -> duration) -> Prop

service_inversion_is_bounded_by is not universe polymorphic
Arguments service_inversion_is_bounded_by {Task Job H0 H1 H2 PState} arr_seq sched 
  {H3 H4 H5} tsk B%function_scope
service_inversion_is_bounded_by is transparent
Expands to: Constant prosa.analysis.abstract.restricted_supply.busy_prefix.service_inversion_is_bounded_by
Declared in library prosa.analysis.abstract.restricted_supply.busy_prefix, line 54, characters 13-44
@service_inversion_is_bounded_by
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       Interference Job ->
       InterferingWorkload Job -> JLFP_policy Job -> Equality.sort Task -> (duration -> duration) -> Prop
```

Body:

```coq
service_inversion_is_bounded_by =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job) 
  (H2 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H3 : Interference Job) (H4 : InterferingWorkload Job)
  (H5 : JLFP_policy Job) (tsk : Equality.sort Task) =>
       (@JLFP_to_JLDP Job H5) (@busy_interval_prefix Job H1 H2 PState sched H3 H4) tsk]
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       Interference Job ->
       InterferingWorkload Job -> JLFP_policy Job -> Equality.sort Task -> (duration -> duration) -> Prop

Arguments service_inversion_is_bounded_by {Task Job H0 H1 H2 PState} arr_seq sched 
  {H3 H4 H5} tsk B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.BusyPrefix.service_inversion_is_bounded_by : {Task :
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
                    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                          Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop
```

Body:

```lean
def Prosa.Analysis.Abstract.RestrictedSupply.BusyPrefix.service_inversion_is_bounded_by.{u_1, u_2, u_3, u_4} : {Task :
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
                    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                        [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                          Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Analysis.Abstract.Definitions.Interference Job] [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] tsk B =>
  Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_is_bounded_by arr_seq sched
    (Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched) tsk B
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BusyPrefix_service_inversion_is_bounded_by
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_7 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_7 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_RestrictedSupply_BusyPrefix_service_inversion_is_bounded_by@{u_1 u_2 u_3 u_4
Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0
Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : 
   DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (inst_14 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_7)
  (inst_17 : 
   Prosa_Behavior_Job_JobCost Job
     inst_7)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (inst_26 : 
   Prosa_Analysis_Abstract_Definitions_Interference Job
     inst_7)
  (inst_29 : 
   Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
     inst_7)
  (inst_32 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_7)
  (tsk : Task) (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by Task
  inst_3 Job
  inst_7
  inst_10
  inst_14
  inst_17 PState arr_seq
  sched
  (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
     inst_7
     inst_32)
  (Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
     inst_7
     inst_26
     inst_29
     inst_14
     inst_17 PState sched)
  tsk B
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_7 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_7 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Analysis_Abstract_RestrictedSupply_BusyPrefix_service_inversion_is_bounded_by 
  Task inst_3 
  Job inst_7
  inst_10
  inst_14
  inst_17 
  PState arr_seq sched
  inst_26
  inst_29
  inst_32 
  tsk B%_function_scope
```
