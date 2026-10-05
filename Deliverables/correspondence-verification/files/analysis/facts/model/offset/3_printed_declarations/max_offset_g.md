# `max_offset_g`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.offset.max_offset_g`
- Lean: `Prosa.Analysis.Facts.Model.Offset.max_offset_g`
- Certificate: `max_offset_g_correspondence`

## Official Rocq

```coq
max_offset_g :
forall {Task : TaskType} {H : TaskOffset Task} (tsk : Equality.sort Task) (ts : TaskSet (Equality.sort Task)),
is_true (tsk \in ts) -> is_true (@task_offset Task H tsk <= @max_task_offset Task H ts)

max_offset_g is not universe polymorphic
Arguments max_offset_g {Task H} tsk ts _
max_offset_g is opaque
Expands to: Constant prosa.analysis.facts.model.offset.max_offset_g
Declared in library prosa.analysis.facts.model.offset, line 53, characters 8-20
@max_offset_g
     : forall (Task : TaskType) (H : TaskOffset Task) (tsk : Equality.sort Task)
         (ts : TaskSet (Equality.sort Task)),
       is_true (tsk \in ts) -> is_true (@task_offset Task H tsk <= @max_task_offset Task H ts)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Offset.max_offset_g : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task] (tsk : Task) (ts : Prosa.Model.Task.Concept.TaskSet Task),
  decide (tsk ∈ ts) = true → Prosa.Model.Task.Offset.task_offset tsk ≤ Prosa.Model.Task.Offset.max_task_offset ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Offset_max_offset_g
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Offset_TaskOffset Task
            inst_3)
         (tsk : Task) (ts : Prosa_Model_Task_Concept_TaskSet Task),
       @eq Bool
         (Decidable_decide
            (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Model_Task_Offset_TaskOffset_task_offset Task
            inst_3
            inst_6 tsk)
         (Prosa_Model_Task_Offset_max_task_offset Task
            inst_3
            inst_6 ts)
```
