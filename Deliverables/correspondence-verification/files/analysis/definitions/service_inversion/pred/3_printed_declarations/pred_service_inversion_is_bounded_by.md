# `pred_service_inversion_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_is_bounded_by`
- Lean: `Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_is_bounded_by`
- Certificate: `pred_service_inversion_is_bounded_by_correspondence`

## Official Rocq

```coq
pred_service_inversion_is_bounded_by :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
JLDP_policy Job ->
(Equality.sort Job -> instant -> instant -> Prop) -> Equality.sort Task -> (duration -> duration) -> Prop

pred_service_inversion_is_bounded_by is not universe polymorphic
Arguments pred_service_inversion_is_bounded_by {Task Job H0 H1 H2 PState} arr_seq 
  sched {H3} P%function_scope tsk B%function_scope
pred_service_inversion_is_bounded_by is transparent
Expands to: Constant prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_is_bounded_by
Declared in library prosa.analysis.definitions.service_inversion.pred, line 105, characters 13-49
@pred_service_inversion_is_bounded_by
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       JLDP_policy Job ->
       (Equality.sort Job -> instant -> instant -> Prop) ->
       Equality.sort Task -> (duration -> duration) -> Prop
```

Body:

```coq
pred_service_inversion_is_bounded_by =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job) 
  (H2 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H3 : JLDP_policy Job) (P : Equality.sort Job -> instant -> instant -> Prop)
  (tsk : Equality.sort Task) (B : duration -> duration) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (0 < @job_cost Job H2 j) ->
@pred_service_inversion_of_job_is_bounded_by Job H1 PState arr_seq sched H3 P j B
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       JLDP_policy Job ->
       (Equality.sort Job -> instant -> instant -> Prop) ->
       Equality.sort Task -> (duration -> duration) -> Prop

Arguments pred_service_inversion_is_bounded_by {Task Job H0 H1 H2 PState} arr_seq 
  sched {H3} P%function_scope tsk B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_is_bounded_by : {Task :
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
                    [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
                      (Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop) →
                        Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_is_bounded_by.{u_1, u_2, u_3, u_4} : {Task :
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
                    [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
                      (Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop) →
                        Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLDP_policy Job] P tsk B =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        0 < Prosa.Behavior.Job.job_cost j →
          Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_of_job_is_bounded_by arr_seq sched P j
            B
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by
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
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_7 ->
       (Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp) ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by@{u_1 u_2 u_3 u_4
Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0
Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
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
   Prosa_Model_Priority_Definitions_JLDP_policy Job
     inst_7)
  (P : Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp) 
  (tsk : Task) (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_7 arr_seq j ->
@eq Bool
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_7 Task
     inst_3
     inst_10 tsk j)
  Bool_true ->
LT_lt_inst1 Prosa_Behavior_Job_work instLTNat (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_7
     inst_17 j) ->
Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by Job
  inst_7
  inst_14 PState arr_seq sched
  inst_26 P j B
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
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_7 ->
       (Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp) ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by 
  Task inst_3 
  Job inst_7
  inst_10
  inst_14
  inst_17 
  PState arr_seq sched inst_26
  P%_function_scope tsk B%_function_scope
```
