# `valid_model_with_bounded_nonpreemptive_segments`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.preemption.parameters.valid_model_with_bounded_nonpreemptive_segments`
- Lean: `Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments`
- Certificate: `valid_model_with_bounded_nonpreemptive_segments_correspondence`

## Official Rocq

```coq
valid_model_with_bounded_nonpreemptive_segments :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobCost Job ->
TaskMaxNonpreemptiveSegment Task ->
JobPreemptable Job ->
forall {PState : ProcessorState Job}, arrival_sequence Job -> @schedule Job PState -> Prop

valid_model_with_bounded_nonpreemptive_segments is not universe polymorphic
Arguments valid_model_with_bounded_nonpreemptive_segments {Task Job H H0 H1 H2 PState} arr_seq sched
valid_model_with_bounded_nonpreemptive_segments is transparent
Expands to: Constant prosa.model.task.preemption.parameters.valid_model_with_bounded_nonpreemptive_segments
Declared in library prosa.model.task.preemption.parameters, line 118, characters 13-60
@valid_model_with_bounded_nonpreemptive_segments
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobCost Job ->
       TaskMaxNonpreemptiveSegment Task ->
       JobPreemptable Job ->
       forall PState : ProcessorState Job, arrival_sequence Job -> @schedule Job PState -> Prop
```

Body:

```coq
valid_model_with_bounded_nonpreemptive_segments =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobCost Job)
  (H1 : TaskMaxNonpreemptiveSegment Task) (H2 : JobPreemptable Job) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) =>
@valid_preemption_model Job H0 H2 PState arr_seq sched /\
@model_with_bounded_nonpreemptive_segments Task Job H H0 H1 H2 arr_seq
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobCost Job ->
       TaskMaxNonpreemptiveSegment Task ->
       JobPreemptable Job ->
       forall {PState : ProcessorState Job}, arrival_sequence Job -> @schedule Job PState -> Prop

Arguments valid_model_with_bounded_nonpreemptive_segments {Task Job H H0 H1 H2 PState} arr_seq sched
```

## Lean

```lean
@Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
              [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
                {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop
```

Body:

```lean
def Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task] →
              [Prosa.Model.Preemption.Parameter.JobPreemptable Job] →
                {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState} arr_seq sched =>
  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched ∧
    Prosa.Model.Task.Preemption.Parameters.model_with_bounded_nonpreemptive_segments arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments
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
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       SProp
```

Body:

```coq
Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments@{u_1 u_2 u_3 u_4
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
   Prosa_Behavior_Job_JobCost Job inst_7)
  (inst_17 : 
   Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
     inst_3)
  (inst_20 : 
   Prosa_Model_Preemption_Parameter_JobPreemptable Job
     inst_7)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState) =>
And
  (Prosa_Model_Preemption_Parameter_valid_preemption_model Job
     inst_7
     inst_14
     inst_20 PState arr_seq sched)
  (Prosa_Model_Task_Preemption_Parameters_model_with_bounded_nonpreemptive_segments Task
     inst_3 Job
     inst_7
     inst_10
     inst_14
     inst_17
     inst_20 arr_seq)
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
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       SProp

Arguments Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments 
  Task inst_3 
  Job inst_7
  inst_10
  inst_14
  inst_17
  inst_20 PState 
  arr_seq sched
```
