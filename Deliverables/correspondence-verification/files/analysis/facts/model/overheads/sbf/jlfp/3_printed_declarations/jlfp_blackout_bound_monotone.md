# `jlfp_blackout_bound_monotone`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound_monotone`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_blackout_bound_monotone`
- Certificate: `jlfp_blackout_bound_monotone_correspondence`

## Official Rocq

```coq
jlfp_blackout_bound_monotone :
forall {Task : TaskType} {H : MaxArrivals Task} (ts : seq (Equality.sort Task)),
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H) ->
forall DB CSB CRPDB : duration, @monotone nat leq (@jlfp_blackout_bound Task H ts DB CSB CRPDB)

jlfp_blackout_bound_monotone is not universe polymorphic
Arguments jlfp_blackout_bound_monotone {Task H} ts%seq_scope H_valid_arrival_curve DB CSB CRPDB x y _
jlfp_blackout_bound_monotone is opaque
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound_monotone
Declared in library prosa.analysis.facts.model.overheads.sbf.jlfp, line 145, characters 9-37
@jlfp_blackout_bound_monotone
     : forall (Task : TaskType) (H : MaxArrivals Task) (ts : seq (Equality.sort Task)),
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H) ->
       forall DB CSB CRPDB : duration, @monotone nat leq (@jlfp_blackout_bound Task H ts DB CSB CRPDB)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_blackout_bound_monotone : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (ts : List Task),
  Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
    ∀ (DB CSB CRPDB : Prosa.Behavior.Time.duration),
      Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y))
        (Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_blackout_bound ts DB CSB CRPDB)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Jlfp_jlfp_blackout_bound_monotone
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (ts : List Task),
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_6) ->
       forall DB CSB CRPDB : Prosa_Behavior_Time_duration,
       Prosa_Util_Rel_monotone_inst1 Prosa_Behavior_Time_duration
         (fun x y : Prosa_Behavior_Time_duration =>
          Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat x y) (Nat_decLe x y))
         (Prosa_Analysis_Facts_Model_Overheads_Sbf_Jlfp_jlfp_blackout_bound Task
            inst_3
            inst_6 ts DB CSB
            CRPDB)
```
