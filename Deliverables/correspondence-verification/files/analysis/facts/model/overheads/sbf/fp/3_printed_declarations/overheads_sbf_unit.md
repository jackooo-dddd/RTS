# `overheads_sbf_unit`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_unit`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.overheads_sbf_unit`
- Certificate: `overheads_sbf_unit_correspondence`

## Official Rocq

```coq
overheads_sbf_unit :
forall {Task : TaskType} {H : MaxArrivals Task} {FP : FP_policy Task} (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H) ->
forall (DB CSB CRPDB : duration) (tsk : Equality.sort Task),
unit_supply_bound_function (@fp_ovh_sbf_slow Task FP H ts DB CSB CRPDB tsk)

overheads_sbf_unit is not universe polymorphic
Arguments overheads_sbf_unit {Task H FP} ts%seq_scope H_valid_arrival_curve DB CSB CRPDB tsk δ
overheads_sbf_unit is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.fp.overheads_sbf_unit
Declared in library prosa.analysis.facts.model.overheads.sbf.fp, line 166, characters 8-26
@overheads_sbf_unit
     : forall (Task : TaskType) (H : MaxArrivals Task) (FP : FP_policy Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H) ->
       forall (DB CSB CRPDB : duration) (tsk : Equality.sort Task),
       unit_supply_bound_function (@fp_ovh_sbf_slow Task FP H ts DB CSB CRPDB tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.overheads_sbf_unit : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (DB CSB CRPDB : Prosa.Behavior.Time.duration) (tsk : Task),
      Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_overheads_sbf_unit
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_6) ->
       forall (DB CSB CRPDB : Prosa_Behavior_Time_duration) (tsk : Task),
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            (Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_ovh_sbf_slow Task
               inst_3 FP
               inst_6 ts DB CSB
               CRPDB tsk))
```
