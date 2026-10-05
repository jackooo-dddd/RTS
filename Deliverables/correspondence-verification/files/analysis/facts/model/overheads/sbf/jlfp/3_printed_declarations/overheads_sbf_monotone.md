# `overheads_sbf_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_monotone`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.overheads_sbf_monotone`
- Certificate: `overheads_sbf_monotone_correspondence`

## Official Rocq

```coq
overheads_sbf_monotone :
forall {Task : TaskType} {H : MaxArrivals Task} (ts : seq (Equality.sort Task)) (DB CSB CRPDB : duration),
sbf_is_monotone (@jlfp_ovh_sbf_slow Task H ts DB CSB CRPDB)

overheads_sbf_monotone is not universe polymorphic
Arguments overheads_sbf_monotone {Task H} ts%seq_scope DB CSB CRPDB x y _
overheads_sbf_monotone is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.jlfp.overheads_sbf_monotone
Declared in library prosa.analysis.facts.model.overheads.sbf.jlfp, line 132, characters 8-30
@overheads_sbf_monotone
     : forall (Task : TaskType) (H : MaxArrivals Task) (ts : seq (Equality.sort Task))
         (DB CSB CRPDB : duration),
       sbf_is_monotone (@jlfp_ovh_sbf_slow Task H ts DB CSB CRPDB)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.overheads_sbf_monotone : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (ts : List Task)
  (DB CSB CRPDB : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone
    Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Jlfp_overheads_sbf_monotone
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (ts : List Task) (DB CSB CRPDB : Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            (Prosa_Analysis_Facts_Model_Overheads_Sbf_Jlfp_jlfp_ovh_sbf_slow Task
               inst_3
               inst_6 ts DB CSB
               CRPDB))
```
