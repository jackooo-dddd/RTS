# `GEL`

- Kind (Rocq): Instance
- Rocq: `prosa.model.priority.gel.GEL`
- Lean: `Prosa.Model.Priority.Gel.GEL`
- Certificate: `GEL_correspondence`

## Official Rocq

```coq
GEL :
forall (Job : JobType) (Task : TaskType),
PriorityPoint Task -> JobArrival Job -> JobTask Job Task -> JLFP_policy Job

GEL is not universe polymorphic
Arguments GEL Job Task {H H0 H1} _ _
GEL is transparent
Expands to: Constant prosa.model.priority.gel.GEL
Declared in library prosa.model.priority.gel, line 43, characters 0-230
GEL
     : forall (Job : JobType) (Task : TaskType),
       PriorityPoint Task -> JobArrival Job -> JobTask Job Task -> JLFP_policy Job
```

Body:

```coq
GEL =
fun (Job : JobType) (Task : TaskType) (H : PriorityPoint Task) (H0 : JobArrival Job) 
  (H1 : JobTask Job Task) (j1 j2 : Equality.sort Job) =>
@order.Order.le ssrnum.ring_display
  (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
     ssrint.ssrint_int__canonical__Num_POrderedZmodule)
  (@job_priority_point Job Task H1 H H0 j1) (@job_priority_point Job Task H1 H H0 j2)
     : forall (Job : JobType) (Task : TaskType),
       PriorityPoint Task -> JobArrival Job -> JobTask Job Task -> JLFP_policy Job

Arguments GEL Job Task {H H0 H1} _ _
```

## Lean

```lean
Prosa.Model.Priority.Gel.GEL : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] →
    (Task : Prosa.Model.Task.Concept.TaskType) →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] → Prosa.Model.Priority.Definitions.JLFP_policy Job
```

Body:

```lean
@[reducible] def Prosa.Model.Priority.Gel.GEL.{u_1, u_2} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] →
    (Task : Prosa.Model.Task.Concept.TaskType) →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Priority.Gel.PriorityPoint Task] →
          [Prosa.Behavior.Job.JobArrival Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] → Prosa.Model.Priority.Definitions.JLFP_policy Job :=
fun Job [DecidableEq Job] Task [DecidableEq Task] [Prosa.Model.Priority.Gel.PriorityPoint Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Model.Task.Concept.JobTask Job Task] =>
  {
    hep_job := fun j1 j2 =>
      decide (Prosa.Model.Priority.Gel.job_priority_point j1 ≤ Prosa.Model.Priority.Gel.job_priority_point j2) }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Gel_GEL
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3
```

Body:

```coq
Prosa_Model_Priority_Gel_GEL@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Priority_Gel_PriorityPoint
                                                                      Task
                                                                      inst_7)
  (inst_13 : Prosa_Behavior_Job_JobArrival Job
                                                                      inst_3)
  (inst_16 : Prosa_Model_Task_Concept_JobTask Job
                                                                      inst_3
                                                                      Task
                                                                      inst_7) =>
Prosa_Model_Priority_Definitions_JLFP_policy_mk Job
  inst_3
  (fun j1 j2 : Job =>
   Decidable_decide
     (LE_le_inst1 Int Int_instLEInt
        (Prosa_Model_Priority_Gel_job_priority_point Job
           inst_3 Task
           inst_7
           inst_16
           inst_10
           inst_13 j1)
        (Prosa_Model_Priority_Gel_job_priority_point Job
           inst_3 Task
           inst_7
           inst_16
           inst_10
           inst_13 j2))
     (Int_decLe
        (Prosa_Model_Priority_Gel_job_priority_point Job
           inst_3 Task
           inst_7
           inst_16
           inst_10
           inst_13 j1)
        (Prosa_Model_Priority_Gel_job_priority_point Job
           inst_3 Task
           inst_7
           inst_16
           inst_10
           inst_13 j2)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3

Arguments Prosa_Model_Priority_Gel_GEL Job inst_3 
  Task inst_7
  inst_10
  inst_13
  inst_16
```
