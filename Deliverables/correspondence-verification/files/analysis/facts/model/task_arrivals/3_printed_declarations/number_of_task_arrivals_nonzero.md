# `number_of_task_arrivals_nonzero`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.task_arrivals.number_of_task_arrivals_nonzero`
- Lean: `Prosa.Analysis.Facts.Model.TaskArrivals.number_of_task_arrivals_nonzero`
- Certificate: `number_of_task_arrivals_nonzero_correspondence`

## Official Rocq

```coq
number_of_task_arrivals_nonzero :
forall {Job : JobType} {Task : TaskType} {H : JobTask Job Task} (arr_seq : arrival_sequence Job)
  (tsk : Equality.sort Task) (t1 t2 : instant),
is_true (0 < @number_of_task_arrivals Job Task H arr_seq tsk t1 t2) -> is_true (t1 < t2)

number_of_task_arrivals_nonzero is not universe polymorphic
Arguments number_of_task_arrivals_nonzero {Job Task H} arr_seq tsk t1 t2 _
number_of_task_arrivals_nonzero is opaque
Expands to: Constant prosa.analysis.facts.model.task_arrivals.number_of_task_arrivals_nonzero
Declared in library prosa.analysis.facts.model.task_arrivals, line 197, characters 12-43
@number_of_task_arrivals_nonzero
     : forall (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (tsk : Equality.sort Task) (t1 t2 : instant),
       is_true (0 < @number_of_task_arrivals Job Task H arr_seq tsk t1 t2) -> is_true (t1 < t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskArrivals.number_of_task_arrivals_nonzero : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task) (t1 t2 : Prosa.Behavior.Time.instant),
  0 < Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t1 t2 → t1 < t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskArrivals_number_of_task_arrivals_nonzero
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (tsk : Task) (t1 t2 : Prosa_Behavior_Time_instant),
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
            inst_3 Task
            inst_7
            inst_10 arr_seq tsk t1 t2) ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t2
```
