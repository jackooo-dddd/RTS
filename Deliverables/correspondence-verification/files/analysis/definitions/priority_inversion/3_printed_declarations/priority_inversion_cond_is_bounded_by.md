# `priority_inversion_cond_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.priority_inversion.priority_inversion_cond_is_bounded_by`
- Lean: `Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond_is_bounded_by`
- Certificate: `priority_inversion_cond_is_bounded_by_correspondence`

## Official Rocq

```coq
priority_inversion_cond_is_bounded_by :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
JLFP_policy Job -> Equality.sort Task -> pred (Equality.sort Job) -> (duration -> duration) -> Prop

priority_inversion_cond_is_bounded_by is not universe polymorphic
Arguments priority_inversion_cond_is_bounded_by {Task Job H0 H1 H2 PState} arr_seq 
  sched {H3} tsk P B%function_scope
priority_inversion_cond_is_bounded_by is transparent
Expands to: Constant prosa.analysis.definitions.priority_inversion.priority_inversion_cond_is_bounded_by
Declared in library prosa.analysis.definitions.priority_inversion, line 129, characters 13-50
@priority_inversion_cond_is_bounded_by
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Equality.sort Task -> pred (Equality.sort Job) -> (duration -> duration) -> Prop
```

Body:

```coq
priority_inversion_cond_is_bounded_by =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job) 
  (H2 : JobCost Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H3 : JLFP_policy Job) (tsk : Equality.sort Task)
  (P : pred (Equality.sort Job)) (B : duration -> duration) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (0 < @job_cost Job H2 j) ->
@priority_inversion_of_job_cond_is_bounded_by Job H1 H2 PState arr_seq sched H3 j P B
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Equality.sort Task -> pred (Equality.sort Job) -> (duration -> duration) -> Prop

Arguments priority_inversion_cond_is_bounded_by {Task Job H0 H1 H2 PState} arr_seq 
  sched {H3} tsk P B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond_is_bounded_by : {Task :
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
                      Task → (Job → Bool) → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond_is_bounded_by.{u_1, u_2, u_3, u_4} : {Task :
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
                      Task → (Job → Bool) → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] tsk P B =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        0 < Prosa.Behavior.Job.job_cost j →
          Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_cond_is_bounded_by arr_seq sched j P B
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond_is_bounded_by
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
       Task -> (Job -> Bool) -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond_is_bounded_by@{u_1 u_2 u_3 u_4
Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0
Lean.u_1+2.0 Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
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
             inst_10 PState)
  (inst_29 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_10)
  (tsk : Task) (P : Job -> Bool) (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_10 arr_seq j ->
@eq Bool
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_10 Task
     inst_3
     inst_13 tsk j)
  Bool_true ->
LT_lt_inst1 Prosa_Behavior_Job_work instLTNat (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_10
     inst_20 j) ->
Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_cond_is_bounded_by Job
  inst_10
  inst_17
  inst_20 PState arr_seq sched
  inst_29 j P B
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
       Task -> (Job -> Bool) -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond_is_bounded_by 
  Task inst_3 
  Job inst_10
  inst_13
  inst_17
  inst_20 
  PState arr_seq sched inst_29 
  tsk (P B)%_function_scope
```
