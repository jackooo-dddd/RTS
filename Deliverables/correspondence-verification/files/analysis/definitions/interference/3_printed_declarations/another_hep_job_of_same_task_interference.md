# `another_hep_job_of_same_task_interference`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.interference.another_hep_job_of_same_task_interference`
- Lean: `Prosa.Analysis.Definitions.Interference.another_hep_job_of_same_task_interference`
- Certificate: `another_hep_job_of_same_task_interference_correspondence`

## Official Rocq

```coq
another_hep_job_of_same_task_interference :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

another_hep_job_of_same_task_interference is not universe polymorphic
Arguments another_hep_job_of_same_task_interference {Task Job jt PState} arr_seq sched {JLFP} j t
another_hep_job_of_same_task_interference is transparent
Expands to: Constant prosa.analysis.definitions.interference.another_hep_job_of_same_task_interference
Declared in library prosa.analysis.definitions.interference, line 99, characters 15-56
@another_hep_job_of_same_task_interference
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
another_hep_job_of_same_task_interference =
fun (Task : TaskType) (Job : JobType) (jt : JobTask Job Task) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job)
  (j : Equality.sort Job) (t : instant) =>
@has (Equality.sort Job)
  (fun jhp : Equality.sort Job =>
   @another_hep_job_of_same_task Task Job jt JLFP jhp j && @receives_service_at Job PState sched jhp t)
  (@arrivals_up_to Job arr_seq t)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

Arguments another_hep_job_of_same_task_interference {Task Job jt PState} arr_seq sched {JLFP} j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.Interference.another_hep_job_of_same_task_interference : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.Interference.another_hep_job_of_same_task_interference.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t =>
  (Prosa.Behavior.Arrival_sequence.arrivals_up_to arr_seq t).any fun jhp =>
    Prosa.Model.Priority.Definitions.another_hep_job_of_same_task jhp j &&
      Prosa.Behavior.Service.receives_service_at sched jhp t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Interference_another_hep_job_of_same_task_interference
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
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
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_Interference_another_hep_job_of_same_task_interference@{u_1 u_2 u_3 u_4
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
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (inst_20 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_7)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
List_any Job
  (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job
     inst_7 arr_seq t)
  (fun jhp : Job =>
   Bool_and
     (Prosa_Model_Priority_Definitions_another_hep_job_of_same_task Task
        inst_3 Job
        inst_7
        inst_10
        inst_20 jhp j)
     (Prosa_Behavior_Service_receives_service_at Job
        inst_7 PState sched jhp t))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
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
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_Interference_another_hep_job_of_same_task_interference 
  Task inst_3 
  Job inst_7
  inst_10 PState 
  arr_seq sched inst_20 
  j t
```
