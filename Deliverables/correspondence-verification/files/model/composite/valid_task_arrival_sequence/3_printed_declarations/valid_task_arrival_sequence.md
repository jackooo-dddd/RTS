# `valid_task_arrival_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence`
- Lean: `Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence`
- Certificate: `valid_task_arrival_sequence_correspondence`

## Official Rocq

```coq
valid_task_arrival_sequence :
forall {Task : TaskType},
TaskCost Task ->
MaxArrivals Task ->
forall {Job : JobType},
JobTask Job Task -> JobCost Job -> JobArrival Job -> seq (Equality.sort Task) -> arrival_sequence Job -> Prop

valid_task_arrival_sequence is not universe polymorphic
Arguments valid_task_arrival_sequence {Task H H0 Job H1 H2 H3} ts%seq_scope arr_seq
valid_task_arrival_sequence is transparent
Expands to: Constant prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence
Declared in library prosa.model.composite.valid_task_arrival_sequence, line 34, characters 13-40
@valid_task_arrival_sequence
     : forall Task : TaskType,
       TaskCost Task ->
       MaxArrivals Task ->
       forall Job : JobType,
       JobTask Job Task ->
       JobCost Job -> JobArrival Job -> seq (Equality.sort Task) -> arrival_sequence Job -> Prop
```

Body:

```coq
valid_task_arrival_sequence =
fun (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType) 
  (H1 : JobTask Job Task) (H2 : JobCost Job) (H3 : JobArrival Job) (ts : seq (Equality.sort Task))
  (arr_seq : arrival_sequence Job) =>
@valid_arrival_sequence Job H3 arr_seq /\
@arrivals_have_valid_job_costs Task H Job H1 H2 arr_seq /\
@all_jobs_from_taskset Task Job H1 arr_seq ts /\
@taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts /\
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0)
     : forall {Task : TaskType},
       TaskCost Task ->
       MaxArrivals Task ->
       forall {Job : JobType},
       JobTask Job Task ->
       JobCost Job -> JobArrival Job -> seq (Equality.sort Task) -> arrival_sequence Job -> Prop

Arguments valid_task_arrival_sequence {Task H H0 Job H1 H2 H3} ts%seq_scope arr_seq
```

## Lean

```lean
@Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobCost Job] →
                [Prosa.Behavior.Job.JobArrival Job] →
                  List Task → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskCost Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobCost Job] →
                [Prosa.Behavior.Job.JobArrival Job] →
                  List Task → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskCost Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] ts
    arr_seq =>
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq ∧
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq ∧
      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts ∧
        Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts ∧
          Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals
```

## Lean, imported into Rocq

```coq
Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_13 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       List Task ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       SProp
```

Body:

```coq
Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Concept_TaskCost Task
     inst_3)
  (inst_9 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_13 : DecidableEq Job)
  (inst_16 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_13 Task
     inst_3)
  (inst_20 : 
   Prosa_Behavior_Job_JobCost Job
     inst_13)
  (inst_23 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_13)
  (ts : List Task)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_13) =>
And
  (Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
     inst_13
     inst_23 arr_seq)
  (And
     (Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
        inst_3
        inst_6 Job
        inst_13
        inst_16
        inst_20 arr_seq)
     (And
        (Prosa_Model_Task_Concept_all_jobs_from_taskset Task
           inst_3 Job
           inst_13
           inst_16 arr_seq ts)
        (And
           (Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
              inst_3 Job
              inst_13
              inst_16 arr_seq
              inst_9 ts)
           (Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
              inst_3 ts
              (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
                 inst_3
                 inst_9)))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Concept_TaskCost Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_13 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       List Task ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       SProp

Arguments Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence 
  Task inst_3
  inst_6
  inst_9 
  Job inst_13
  inst_16
  inst_20
  inst_23 
  ts arr_seq
```
