# `valid_task_run_to_completion_threshold`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.parameters.valid_task_run_to_completion_threshold`
- Lean: `Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold`
- Certificate: `valid_task_run_to_completion_threshold_correspondence`

## Official Rocq

```coq
valid_task_run_to_completion_threshold :
forall {Task : TaskType},
TaskCost Task ->
forall {Job : JobType},
JobTask Job Task ->
JobCost Job ->
JobPreemptable Job -> TaskRunToCompletionThreshold Task -> arrival_sequence Job -> Equality.sort Task -> Prop

valid_task_run_to_completion_threshold is not universe polymorphic
Arguments valid_task_run_to_completion_threshold {Task H Job H0 H1 H2 H3} arr_seq tsk
valid_task_run_to_completion_threshold is transparent
Expands to: Constant prosa.model.task.preemption.parameters.valid_task_run_to_completion_threshold
Declared in library prosa.model.task.preemption.parameters, line 178, characters 13-51
@valid_task_run_to_completion_threshold
     : forall Task : TaskType,
       TaskCost Task ->
       forall Job : JobType,
       JobTask Job Task ->
       JobCost Job ->
       JobPreemptable Job ->
       TaskRunToCompletionThreshold Task -> arrival_sequence Job -> Equality.sort Task -> Prop
```

Body:

```coq
valid_task_run_to_completion_threshold =
fun (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobCost Job) (H2 : JobPreemptable Job) (H3 : TaskRunToCompletionThreshold Task)
  (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) =>
is_true (@task_rtc_bounded_by_cost Task H H3 tsk) /\ @job_respects_task_rtc Task Job H0 H1 H2 H3 arr_seq tsk
     : forall {Task : TaskType},
       TaskCost Task ->
       forall {Job : JobType},
       JobTask Job Task ->
       JobCost Job ->
       JobPreemptable Job ->
       TaskRunToCompletionThreshold Task -> arrival_sequence Job -> Equality.sort Task -> Prop

Arguments valid_task_run_to_completion_threshold {Task H Job H0 H1 H2 H3} arr_seq tsk
```

## Lean

```lean
@Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobCost Job] →
              [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
                [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobCost Job] →
              [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
                [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobCost Job]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job]
    [Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task] arr_seq tsk =>
  Prosa.Model.Task.Preemption.Parameters.task_rtc_bounded_by_cost tsk = true ∧
    Prosa.Model.Task.Preemption.Parameters.job_respects_task_rtc arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_10 ->
       Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_10 Task
     inst_3)
  (inst_17 : 
   Prosa_Behavior_Job_JobCost Job inst_10)
  (inst_20 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_10)
  (inst_23 : 
   Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
     inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (tsk : Task) =>
And
  (@eq Bool
     (Prosa_Model_Task_Preemption_Parameters_task_rtc_bounded_by_cost Task
        inst_3
        inst_6
        inst_23 tsk)
     Bool_true)
  (Prosa_Model_Task_Preemption_Parameters_job_respects_task_rtc Task
     inst_3 Job
     inst_10
     inst_13
     inst_17
     inst_20
     inst_23 arr_seq tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_10 ->
       Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Task -> SProp

Arguments Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold 
  Task inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17
  inst_20
  inst_23 arr_seq 
  tsk
```
