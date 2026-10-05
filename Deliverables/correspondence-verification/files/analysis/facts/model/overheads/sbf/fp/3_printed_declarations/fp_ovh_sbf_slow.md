# `fp_ovh_sbf_slow`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.model.overheads.sbf.fp.fp_ovh_sbf_slow`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_ovh_sbf_slow`
- Certificate: `fp_ovh_sbf_slow_correspondence`

## Official Rocq

```coq
fp_ovh_sbf_slow :
forall {Task : TaskType},
FP_policy Task ->
MaxArrivals Task ->
seq (Equality.sort Task) -> duration -> duration -> duration -> Equality.sort Task -> SupplyBoundFunction

fp_ovh_sbf_slow is not universe polymorphic
Arguments fp_ovh_sbf_slow {Task FP H} ts%seq_scope DB CSB CRPDB tsk _
fp_ovh_sbf_slow is transparent
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.fp.fp_ovh_sbf_slow
Declared in library prosa.analysis.facts.model.overheads.sbf.fp, line 55, characters 13-28
@fp_ovh_sbf_slow
     : forall Task : TaskType,
       FP_policy Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) ->
       duration -> duration -> duration -> Equality.sort Task -> SupplyBoundFunction
```

Body:

```coq
fp_ovh_sbf_slow =
fun (Task : TaskType) (FP : FP_policy Task) (H : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (DB CSB CRPDB : duration) (tsk : Equality.sort Task) (Δ : duration) =>
Δ - slowed (@fp_blackout_bound Task FP H ts DB CSB CRPDB tsk) Δ
     : forall {Task : TaskType},
       FP_policy Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) ->
       duration -> duration -> duration -> Equality.sort Task -> SupplyBoundFunction

Arguments fp_ovh_sbf_slow {Task FP H} ts%seq_scope DB CSB CRPDB tsk _
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_ovh_sbf_slow : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task →
          Prosa.Behavior.Time.duration →
            Prosa.Behavior.Time.duration →
              Prosa.Behavior.Time.duration → Task → Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction
```

Body:

```lean
def Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_ovh_sbf_slow.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task →
          Prosa.Behavior.Time.duration →
            Prosa.Behavior.Time.duration →
              Prosa.Behavior.Time.duration → Task → Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Definitions.FP_policy Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts DB CSB CRPDB tsk =>
  {
    supply_bound_function := fun Δ =>
      Δ -
        Prosa.Util.UnitGrowth.slowed (Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_blackout_bound ts DB CSB CRPDB tsk)
          Δ }
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_ovh_sbf_slow
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Task -> Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction
```

Body:

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_ovh_sbf_slow@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (inst_8 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (DB CSB CRPDB : Prosa_Behavior_Time_duration) (tsk : Task) =>
Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_mk
  (fun _UU0394_ : Prosa_Behavior_Time_duration =>
   HSub_hSub_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
     (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) _UU0394_
     (Prosa_Util_UnitGrowth_slowed
        (Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_blackout_bound Task
           inst_3 FP
           inst_8 ts DB CSB CRPDB
           tsk)
        _UU0394_))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Task -> Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction

Arguments Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_ovh_sbf_slow Task
  inst_3 
  FP inst_8 
  ts DB CSB CRPDB tsk
```
