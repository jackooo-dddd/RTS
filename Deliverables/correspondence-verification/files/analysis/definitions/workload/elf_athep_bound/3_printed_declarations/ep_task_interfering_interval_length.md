# `ep_task_interfering_interval_length`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.workload.elf_athep_bound.ep_task_interfering_interval_length`
- Lean: `Prosa.Analysis.Definitions.Workload.ElfAthepBound.ep_task_interfering_interval_length`
- Certificate: `ep_task_interfering_interval_length_correspondence`

## Official Rocq

```coq
ep_task_interfering_interval_length :
forall {Task : TaskType},
gel.PriorityPoint Task ->
Equality.sort Task ->
Equality.sort Task ->
duration ->
ssralg.GRing.Nmodule.sort
  (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
     ssrint.ssrint_int__canonical__GRing_PzSemiRing)

ep_task_interfering_interval_length is not universe polymorphic
Arguments ep_task_interfering_interval_length {Task H1} tsk tsk_o A
ep_task_interfering_interval_length is transparent
Expands to: Constant prosa.analysis.definitions.workload.elf_athep_bound.ep_task_interfering_interval_length
Declared in library prosa.analysis.definitions.workload.elf_athep_bound, line 29, characters 13-48
@ep_task_interfering_interval_length
     : forall Task : TaskType,
       gel.PriorityPoint Task ->
       Equality.sort Task ->
       Equality.sort Task ->
       duration ->
       ssralg.GRing.Nmodule.sort
         (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
            ssrint.ssrint_int__canonical__GRing_PzSemiRing)
```

Body:

```coq
ep_task_interfering_interval_length =
fun (Task : TaskType) (H1 : gel.PriorityPoint Task) (tsk tsk_o : Equality.sort Task) (A : duration) =>
@ssralg.GRing.add
  (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
     ssrint.ssrint_int__canonical__GRing_PzSemiRing)
  (@ssralg.GRing.add
     (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
        ssrint.ssrint_int__canonical__GRing_PzSemiRing)
     (@ssralg.GRing.natmul
        (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
           ssrint.ssrint_int__canonical__GRing_PzSemiRing)
        (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) (A + 1))
     (@gel.task_priority_point Task H1 tsk))
  (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule (@gel.task_priority_point Task H1 tsk_o))
     : forall {Task : TaskType},
       gel.PriorityPoint Task ->
       Equality.sort Task ->
       Equality.sort Task ->
       duration ->
       ssralg.GRing.Nmodule.sort
         (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
            ssrint.ssrint_int__canonical__GRing_PzSemiRing)

Arguments ep_task_interfering_interval_length {Task H1} tsk tsk_o A
```

## Lean

```lean
@Prosa.Analysis.Definitions.Workload.ElfAthepBound.ep_task_interfering_interval_length : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Priority.Gel.PriorityPoint Task] → Task → Task → Prosa.Behavior.Time.duration → ℤ
```

Body:

```lean
def Prosa.Analysis.Definitions.Workload.ElfAthepBound.ep_task_interfering_interval_length.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Priority.Gel.PriorityPoint Task] → Task → Task → Prosa.Behavior.Time.duration → ℤ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] tsk tsk_o A =>
  ↑(A + 1) + Prosa.Model.Priority.Gel.task_priority_point tsk - Prosa.Model.Priority.Gel.task_priority_point tsk_o
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       Task -> Task -> Prosa_Behavior_Time_duration -> Int
```

Body:

```coq
Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Priority_Gel_PriorityPoint Task
     inst_3)
  (tsk tsk_o : Task) (A : Prosa_Behavior_Time_duration) =>
HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
  (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
     (Nat_cast_inst1 Int instNatCastInt
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
           (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
        inst_3
        inst_6 tsk))
  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
     inst_3
     inst_6 tsk_o)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       Task -> Task -> Prosa_Behavior_Time_duration -> Int

Arguments Prosa_Analysis_Definitions_Workload_ElfAthepBound_ep_task_interfering_interval_length 
  Task inst_3
  inst_6 
  tsk tsk_o A
```
