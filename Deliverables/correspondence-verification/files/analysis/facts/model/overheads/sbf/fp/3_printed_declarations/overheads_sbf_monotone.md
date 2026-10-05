# `overheads_sbf_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_monotone`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.overheads_sbf_monotone`
- Certificate: `overheads_sbf_monotone_correspondence`

## Official Rocq

```coq
overheads_sbf_monotone :
forall {Task : TaskType} {H : MaxArrivals Task} {FP : FP_policy Task} (ts : seq (Equality.sort Task))
  (DB CSB CRPDB : duration) (tsk : Equality.sort Task),
sbf_is_monotone (@fp_ovh_sbf_slow Task FP H ts DB CSB CRPDB tsk)

overheads_sbf_monotone is not universe polymorphic
Arguments overheads_sbf_monotone {Task H FP} ts%seq_scope DB CSB CRPDB tsk x y _
overheads_sbf_monotone is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_monotone
Declared in library prosa.analysis.facts.model.overheads.sbf.fp, line 137, characters 8-30
@overheads_sbf_monotone
     : forall (Task : TaskType) (H : MaxArrivals Task) (FP : FP_policy Task) (ts : seq (Equality.sort Task))
         (DB CSB CRPDB : duration) (tsk : Equality.sort Task),
       sbf_is_monotone (@fp_ovh_sbf_slow Task FP H ts DB CSB CRPDB tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.overheads_sbf_monotone : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (ts : List Task) (DB CSB CRPDB : Prosa.Behavior.Time.duration)
  (tsk : Task),
  Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone
    Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_overheads_sbf_monotone
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (ts : List Task) (DB CSB CRPDB : Prosa_Behavior_Time_duration) (tsk : Task),
       Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            (Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_ovh_sbf_slow Task
               inst_3 FP
               inst_6 ts DB CSB
               CRPDB tsk))
```
