# `fp_blackout_bound_monotone`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound_monotone`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_blackout_bound_monotone`
- Certificate: `fp_blackout_bound_monotone_correspondence`

## Official Rocq

```coq
fp_blackout_bound_monotone :
forall {Task : TaskType} {H : MaxArrivals Task} {FP : FP_policy Task} (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H) ->
forall (DB CSB CRPDB : duration) (tsk : Equality.sort Task),
@monotone nat leq (@fp_blackout_bound Task FP H ts DB CSB CRPDB tsk)

fp_blackout_bound_monotone is not universe polymorphic
Arguments fp_blackout_bound_monotone {Task H FP} ts%seq_scope H_valid_arrival_curve DB CSB CRPDB tsk x y _
fp_blackout_bound_monotone is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound_monotone
Declared in library prosa.analysis.facts.model.overheads.sbf.fp, line 151, characters 9-35
@fp_blackout_bound_monotone
     : forall (Task : TaskType) (H : MaxArrivals Task) (FP : FP_policy Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H) ->
       forall (DB CSB CRPDB : duration) (tsk : Equality.sort Task),
       @monotone nat leq (@fp_blackout_bound Task FP H ts DB CSB CRPDB tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_blackout_bound_monotone : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (DB CSB CRPDB : Prosa.Behavior.Time.duration) (tsk : Task),
      Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))
        (Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_blackout_bound ts DB CSB CRPDB tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_blackout_bound_monotone
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
       Prosa_Util_Rel_monotone_inst1 Prosa_Behavior_Time_duration
         (fun x y : Prosa_Behavior_Time_duration =>
          Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat x y) (Nat_decLe x y))
         (Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_blackout_bound Task
            inst_3 FP
            inst_6 ts DB CSB CRPDB
            tsk)
```
