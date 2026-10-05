# `other_ep_task`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.priority.jlfp_with_fp.other_ep_task`
- Lean: `Prosa.Analysis.Facts.Priority.JlfpWithFp.other_ep_task`
- Certificate: `other_ep_task_correspondence`

## Official Rocq

```coq
other_ep_task : forall {Task : TaskType}, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool

other_ep_task is not universe polymorphic
Arguments other_ep_task {Task FP} tsk tsk_o
other_ep_task is transparent
Expands to: Constant prosa.analysis.facts.priority.jlfp_with_fp.other_ep_task
Declared in library prosa.analysis.facts.priority.jlfp_with_fp, line 40, characters 13-26
@other_ep_task
     : forall Task : TaskType, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool
```

Body:

```coq
other_ep_task =
fun (Task : TaskType) (FP : FP_policy Task) (tsk tsk_o : Equality.sort Task) =>
@ep_task Task FP tsk tsk_o && (tsk_o != tsk)
     : forall {Task : TaskType}, FP_policy Task -> Equality.sort Task -> Equality.sort Task -> bool

Arguments other_ep_task {Task FP} tsk tsk_o
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.JlfpWithFp.other_ep_task : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Task → Task → Bool
```

Body:

```lean
def Prosa.Analysis.Facts.Priority.JlfpWithFp.other_ep_task.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [FP : Prosa.Model.Priority.Definitions.FP_policy Task] → Task → Task → Bool :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Definitions.FP_policy Task] tsk tsk_o =>
  Prosa.Model.Priority.Definitions.ep_task tsk tsk_o && decide (tsk_o ≠ tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_JlfpWithFp_other_ep_task
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Task -> Bool
```

Body:

```coq
Prosa_Analysis_Facts_Priority_JlfpWithFp_other_ep_task@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (tsk tsk_o : Task) =>
Bool_and
  (Prosa_Model_Priority_Definitions_ep_task Task
     inst_3 FP tsk tsk_o)
  (Decidable_decide (Ne Task tsk_o tsk)
     (instDecidableNot (@eq Task tsk_o tsk)
        (inst_3 tsk_o tsk)))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Task -> Task -> Bool

Arguments Prosa_Analysis_Facts_Priority_JlfpWithFp_other_ep_task Task
  inst_3 self a____at____internal__hyg0
  a____at____internal__hyg0
```
