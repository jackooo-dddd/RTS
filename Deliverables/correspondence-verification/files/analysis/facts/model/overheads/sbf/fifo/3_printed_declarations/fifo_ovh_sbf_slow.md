# `fifo_ovh_sbf_slow`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.model.overheads.sbf.fifo.fifo_ovh_sbf_slow`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Fifo.fifo_ovh_sbf_slow`
- Certificate: `fifo_ovh_sbf_slow_correspondence`

## Official Rocq

```coq
fifo_ovh_sbf_slow :
forall {Task : TaskType},
MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> duration -> SupplyBoundFunction

fifo_ovh_sbf_slow is not universe polymorphic
Arguments fifo_ovh_sbf_slow {Task H} ts%seq_scope DB CSB CRPDB _
fifo_ovh_sbf_slow is transparent
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.fifo.fifo_ovh_sbf_slow
Declared in library prosa.analysis.facts.model.overheads.sbf.fifo, line 49, characters 13-30
@fifo_ovh_sbf_slow
     : forall Task : TaskType,
       MaxArrivals Task ->
       seq (Equality.sort Task) -> duration -> duration -> duration -> SupplyBoundFunction
```

Body:

```coq
fifo_ovh_sbf_slow =
fun (Task : TaskType) (H : MaxArrivals Task) (ts : seq (Equality.sort Task)) (DB CSB CRPDB Δ : duration) =>
Δ - slowed (@fifo_blackout_bound Task H ts DB CSB CRPDB) Δ
     : forall {Task : TaskType},
       MaxArrivals Task ->
       seq (Equality.sort Task) -> duration -> duration -> duration -> SupplyBoundFunction

Arguments fifo_ovh_sbf_slow {Task H} ts%seq_scope DB CSB CRPDB _
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Fifo.fifo_ovh_sbf_slow : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
      List Task →
        Prosa.Behavior.Time.duration →
          Prosa.Behavior.Time.duration →
            Prosa.Behavior.Time.duration → Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction
```

Body:

```lean
def Prosa.Analysis.Facts.Model.Overheads.Sbf.Fifo.fifo_ovh_sbf_slow.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
      List Task →
        Prosa.Behavior.Time.duration →
          Prosa.Behavior.Time.duration →
            Prosa.Behavior.Time.duration → Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts DB CSB CRPDB =>
  {
    supply_bound_function := fun Δ =>
      Δ -
        Prosa.Util.UnitGrowth.slowed (Prosa.Analysis.Facts.Model.Overheads.Sbf.Fifo.fifo_blackout_bound ts DB CSB CRPDB)
          Δ }
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_ovh_sbf_slow
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction
```

Body:

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_ovh_sbf_slow@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (DB CSB CRPDB : Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
  (fun _UU0394_ : Prosa_Behavior_Time_duration =>
   HSub_hSub_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) _UU0394_
     (Prosa_Util_UnitGrowth_slowed
        (Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_blackout_bound Task
           inst_3
           inst_6 ts DB CSB CRPDB)
        _UU0394_))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction

Arguments Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_ovh_sbf_slow Task
  inst_3
  inst_6 
  ts DB CSB CRPDB
```
