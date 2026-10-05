# `job_respects_task_rtc`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.parameters.job_respects_task_rtc`
- Lean: `Prosa.Model.Task.Preemption.Parameters.job_respects_task_rtc`
- Certificate: `job_respects_task_rtc_correspondence`

## Official Rocq

```coq
job_respects_task_rtc :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobCost Job ->
JobPreemptable Job -> TaskRunToCompletionThreshold Task -> arrival_sequence Job -> Equality.sort Task -> Prop

job_respects_task_rtc is not universe polymorphic
Arguments job_respects_task_rtc {Task Job H0 H1 H2 H3} arr_seq tsk
job_respects_task_rtc is transparent
Expands to: Constant prosa.model.task.preemption.parameters.job_respects_task_rtc
Declared in library prosa.model.task.preemption.parameters, line 170, characters 13-34
@job_respects_task_rtc
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobCost Job ->
       JobPreemptable Job ->
       TaskRunToCompletionThreshold Task -> arrival_sequence Job -> Equality.sort Task -> Prop
```

Body:

```coq
job_respects_task_rtc =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobCost Job) 
  (H2 : JobPreemptable Job) (H3 : TaskRunToCompletionThreshold Task) (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) -> is_true (@job_rtct Job H1 H2 j <= @task_rtct Task H3 tsk)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobCost Job ->
       JobPreemptable Job ->
       TaskRunToCompletionThreshold Task -> arrival_sequence Job -> Equality.sort Task -> Prop

Arguments job_respects_task_rtc {Task Job H0 H1 H2 H3} arr_seq tsk
```

## Lean

```lean
@Prosa.Model.Task.Preemption.Parameters.job_respects_task_rtc : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
              [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.Parameters.job_respects_task_rtc.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
              [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Preemption.Parameter.JobPreemptable Job]
    [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] arr_seq tsk =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        Prosa.Model.Preemption.Parameter.job_rtct j ≤ Prosa.Model.Task.Preemption.Parameters.task_rtct tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_job_respects_task_rtc
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_job_respects_task_rtc@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (inst_14 : 
   Prosa_Behavior_Job_JobCost Job inst_7)
  (inst_17 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_7)
  (inst_20 : 
   Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (tsk : Task) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_7 arr_seq j ->
@eq Bool
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_7 Task
     inst_3
     inst_10 tsk j)
  Bool_true ->
LE_le_inst1 Nat instLENat
  (Prosa_Model_Preemption_Parameter_job_rtct Job
     inst_7
     inst_14
     inst_17 j)
  (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
     inst_3
     inst_20 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> SProp

Arguments Prosa_Model_Task_Preemption_Parameters_job_respects_task_rtc Task
  inst_3 Job
  inst_7
  inst_10
  inst_14
  inst_17
  inst_20 arr_seq 
  tsk
```
