# `respects_min_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.curves.respects_min_arrivals`
- Lean: `Prosa.Model.Task.Arrival.Curves.respects_min_arrivals`
- Certificate: `respects_min_arrivals_correspondence`

## Official Rocq

```coq
respects_min_arrivals :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> (duration -> nat) -> Prop

respects_min_arrivals is not universe polymorphic
Arguments respects_min_arrivals {Task Job H} arr_seq tsk min_arrivals%function_scope
respects_min_arrivals is transparent
Expands to: Constant prosa.model.task.arrival.curves.respects_min_arrivals
Declared in library prosa.model.task.arrival.curves, line 75, characters 13-34
@respects_min_arrivals
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> (duration -> nat) -> Prop
```

Body:

```coq
respects_min_arrivals =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (min_arrivals : duration -> nat) =>
forall t1 t2 : instant,
is_true (t1 <= t2) ->
is_true (min_arrivals (t2 - t1) <= @number_of_task_arrivals Job Task H arr_seq tsk t1 t2)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> (duration -> nat) -> Prop

Arguments respects_min_arrivals {Task Job H} arr_seq tsk min_arrivals%function_scope
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Curves.respects_min_arrivals : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → (Prosa.Behavior.Time.duration → ℕ) → Prop
def Prosa.Model.Task.Arrival.Curves.respects_min_arrivals.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → (Prosa.Behavior.Time.duration → ℕ) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq tsk
    min_arrivals =>
  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
    t1 ≤ t2 → min_arrivals (t2 - t1) ≤ Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_respects_min_arrivals
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> (Prosa_Behavior_Time_duration -> Nat) -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Curves_respects_min_arrivals@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                             Job
                                                                             inst_7
                                                                             Task
                                                                             inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (tsk : Task) (min_arrivals : Prosa_Behavior_Time_duration -> Nat) =>
forall t1 t2 : Prosa_Behavior_Time_instant,
LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
LE_le_inst1 Nat instLENat
  (min_arrivals
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1))
  (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
     inst_7 Task
     inst_3
     inst_10 arr_seq tsk t1 t2)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> (Prosa_Behavior_Time_duration -> Nat) -> SProp

Arguments Prosa_Model_Task_Arrival_Curves_respects_min_arrivals Task
  inst_3 Job
  inst_7
  inst_10 arr_seq tsk
  num_arrivals%_function_scope
```
