# `model_with_bounded_nonpreemptive_segments`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.parameters.model_with_bounded_nonpreemptive_segments`
- Lean: `Prosa.Model.Task.Preemption.Parameters.model_with_bounded_nonpreemptive_segments`
- Certificate: `model_with_bounded_nonpreemptive_segments_correspondence`

## Official Rocq

```coq
model_with_bounded_nonpreemptive_segments :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobCost Job -> TaskMaxNonpreemptiveSegment Task -> JobPreemptable Job -> arrival_sequence Job -> Prop

model_with_bounded_nonpreemptive_segments is not universe polymorphic
Arguments model_with_bounded_nonpreemptive_segments {Task Job H H0 H1 H2} arr_seq
model_with_bounded_nonpreemptive_segments is transparent
Expands to: Constant prosa.model.task.preemption.parameters.model_with_bounded_nonpreemptive_segments
Declared in library prosa.model.task.preemption.parameters, line 109, characters 13-54
@model_with_bounded_nonpreemptive_segments
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobCost Job -> TaskMaxNonpreemptiveSegment Task -> JobPreemptable Job -> arrival_sequence Job -> Prop
```

Body:

```coq
model_with_bounded_nonpreemptive_segments =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobCost Job)
  (H1 : TaskMaxNonpreemptiveSegment Task) (H2 : JobPreemptable Job) (arr_seq : arrival_sequence Job) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_respects_max_nonpreemptive_segment Task Job H H0 H1 H2 j) /\
@nonpreemptive_regions_have_bounded_length Job H0 H2 j
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobCost Job -> TaskMaxNonpreemptiveSegment Task -> JobPreemptable Job -> arrival_sequence Job -> Prop

Arguments model_with_bounded_nonpreemptive_segments {Task Job H H0 H1 H2} arr_seq
```

## Lean

```lean
@Prosa.Model.Task.Preemption.Parameters.model_with_bounded_nonpreemptive_segments : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
              [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.Parameters.model_with_bounded_nonpreemptive_segments.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
              [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] arr_seq =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Task.Preemption.Parameters.job_respects_max_nonpreemptive_segment j = true ∧
        Prosa.Model.Task.Preemption.Parameters.nonpreemptive_regions_have_bounded_length j
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
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
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (inst_20 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_7 arr_seq j ->
And
  (@eq Bool
     (Prosa_Model_Task_Preemption_Parameters_job_respects_max_nonpreemptive_segment Task
        inst_3 Job
        inst_7
        inst_10
        inst_14
        inst_17
        inst_20 j)
     Bool_true)
  (Prosa_Model_Task_Preemption_Parameters_nonpreemptive_regions_have_bounded_length Job
     inst_7
     inst_14
     inst_20 j)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
         inst_3 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       SProp

Arguments Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments 
  Task inst_3 
  Job inst_7
  inst_10
  inst_14
  inst_17
  inst_20 arr_seq
```
