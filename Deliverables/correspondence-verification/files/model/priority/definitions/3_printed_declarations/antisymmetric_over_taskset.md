# `antisymmetric_over_taskset`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.definitions.antisymmetric_over_taskset`
- Lean: `Prosa.Model.Priority.Definitions.antisymmetric_over_taskset`
- Certificate: `pd_antisymmetric_over_taskset_certificate`

## Official Rocq

```coq
antisymmetric_over_taskset : forall {Task : TaskType}, FP_policy Task -> seq (Equality.sort Task) -> Prop

antisymmetric_over_taskset is not universe polymorphic
Arguments antisymmetric_over_taskset {Task} FP ts%seq_scope
antisymmetric_over_taskset is transparent
Expands to: Constant prosa.model.priority.definitions.antisymmetric_over_taskset
Declared in library prosa.model.priority.definitions, line 144, characters 15-41
@antisymmetric_over_taskset
     : forall Task : TaskType, FP_policy Task -> seq (Equality.sort Task) -> Prop
```

Body:

```coq
antisymmetric_over_taskset =
fun (Task : TaskType) (FP : FP_policy Task) => [eta @antisymmetric_over_list Task (@hep_task Task FP)]
     : forall {Task : TaskType}, FP_policy Task -> seq (Equality.sort Task) -> Prop

Arguments antisymmetric_over_taskset {Task} FP ts%seq_scope
```

## Lean

```lean
@Prosa.Model.Priority.Definitions.antisymmetric_over_taskset : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → Prosa.Model.Priority.Definitions.FP_policy Task → List Task → Prop
def Prosa.Model.Priority.Definitions.antisymmetric_over_taskset.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → Prosa.Model.Priority.Definitions.FP_policy Task → List Task → Prop :=
fun {Task} [DecidableEq Task] FP ts =>
  Prosa.Util.Rel.antisymmetric_over_list Prosa.Model.Priority.Definitions.hep_task ts
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Definitions_antisymmetric_over_taskset
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       List Task -> SProp
```

Body:

```coq
Prosa_Model_Priority_Definitions_antisymmetric_over_taskset@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (ts : List Task) =>
Prosa_Util_Rel_antisymmetric_over_list Task
  inst_3
  (Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
     inst_3 FP)
  ts
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       List Task -> SProp

Arguments Prosa_Model_Priority_Definitions_antisymmetric_over_taskset Task
  inst_3 FP ts
```
