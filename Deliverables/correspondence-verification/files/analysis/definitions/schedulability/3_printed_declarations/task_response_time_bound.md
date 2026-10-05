# `task_response_time_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.schedulability.task_response_time_bound`
- Lean: `Prosa.Analysis.Definitions.Schedulability.task_response_time_bound`
- Certificate: `task_response_time_bound_correspondence`

## Official Rocq

```coq
task_response_time_bound :
forall {Task : TaskType} {Job : JobType},
JobArrival Job ->
JobCost Job ->
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> Equality.sort Task -> duration -> Prop

task_response_time_bound is not universe polymorphic
Arguments task_response_time_bound {Task Job H H0 H2 PState} arr_seq sched tsk R
task_response_time_bound is transparent
Expands to: Constant prosa.analysis.definitions.schedulability.task_response_time_bound
Declared in library prosa.analysis.definitions.schedulability, line 37, characters 13-37
@task_response_time_bound
     : forall (Task : TaskType) (Job : JobType),
       JobArrival Job ->
       JobCost Job ->
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Task -> duration -> Prop
```

Body:

```coq
task_response_time_bound =
fun (Task : TaskType) (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H2 : JobTask Job Task)
  (PState : ProcessorState Job) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (tsk : Equality.sort Task) (R : duration) =>
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H2 tsk j) -> is_true (@job_response_time_bound Job PState sched H0 H j R)
     : forall {Task : TaskType} {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Task -> duration -> Prop

Arguments task_response_time_bound {Task Job H H0 H2 PState} arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Analysis.Definitions.Schedulability.task_response_time_bound : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Schedulability.task_response_time_bound.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
                Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                  Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.duration → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched tsk R =>
  ∀ (j : Job),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        Prosa.Behavior.Service.job_response_time_bound sched j R = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Schedulability_task_response_time_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
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
       Task -> Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Schedulability_task_response_time_bound@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_7)
  (inst_13 : 
   Prosa_Behavior_Job_JobCost Job
     inst_7)
  (inst_19 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (tsk : Task) (R : Prosa_Behavior_Time_duration) =>
forall j : Job,
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_7 arr_seq j ->
@eq Bool
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_7 Task
     inst_3
     inst_19 tsk j)
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Service_job_response_time_bound Job
     inst_7 PState sched
     inst_13
     inst_10 j R)
  Bool_true
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_7 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
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
       Task -> Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
  inst_3 Job
  inst_7
  inst_10
  inst_13
  inst_19 
  PState arr_seq sched tsk R
```
