# `respects_max_separation`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.curves.respects_max_separation`
- Lean: `Prosa.Model.Task.Arrival.Curves.respects_max_separation`
- Certificate: `respects_max_separation_correspondence`

## Official Rocq

```coq
respects_max_separation :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> (nat -> duration) -> Prop

respects_max_separation is not universe polymorphic
Arguments respects_max_separation {Task Job H} arr_seq tsk max_separation%function_scope
respects_max_separation is transparent
Expands to: Constant prosa.model.task.arrival.curves.respects_max_separation
Declared in library prosa.model.task.arrival.curves, line 95, characters 13-36
@respects_max_separation
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> (nat -> duration) -> Prop
```

Body:

```coq
respects_max_separation =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (max_separation : nat -> duration) =>
forall t1 t2 : nat,
is_true (t1 <= t2) ->
is_true (t2 - t1 <= max_separation (@number_of_task_arrivals Job Task H arr_seq tsk t1 t2))
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> arrival_sequence Job -> Equality.sort Task -> (nat -> duration) -> Prop

Arguments respects_max_separation {Task Job H} arr_seq tsk max_separation%function_scope
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Curves.respects_max_separation : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → (ℕ → Prosa.Behavior.Time.duration) → Prop
def Prosa.Model.Task.Arrival.Curves.respects_max_separation.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Task → (ℕ → Prosa.Behavior.Time.duration) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq tsk
    max_separation =>
  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
    t1 ≤ t2 → t2 - t1 ≤ max_separation (Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_respects_max_separation
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> (Nat -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Curves_respects_max_separation@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
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
  (tsk : Task) (max_separation : Nat -> Prosa_Behavior_Time_duration) =>
forall t1 t2 : Prosa_Behavior_Time_instant,
LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
LE_le_inst1 Prosa_Behavior_Time_instant instLENat
  (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
     (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
  (max_separation
     (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
        inst_7 Task
        inst_3
        inst_10 arr_seq tsk t1 t2))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> (Nat -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Model_Task_Arrival_Curves_respects_max_separation Task
  inst_3 Job
  inst_7
  inst_10 arr_seq tsk
  min_separation%_function_scope
```
