# `sbf_respected_simplified`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.definitions.sbf.plain.sbf_respected_simplified`
- Lean: `Prosa.Analysis.Definitions.Sbf.Plain.sbf_respected_simplified`
- Certificate: `plain_sbf_respected_simplified_statement_correspondence`

## Official Rocq

```coq
sbf_respected_simplified :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {SBF : SupplyBoundFunction},
@supply_bound_function_respected Job PState arr_seq sched SBF ->
forall (j : Equality.sort Job) (t1 t2 : instant),
@arrives_in Job arr_seq j ->
is_true (t1 <= t2) -> is_true (SBF (t2 - t1) <= @supply_during Job PState sched t1 t2)

sbf_respected_simplified is not universe polymorphic
Arguments sbf_respected_simplified {Job PState} arr_seq sched {SBF} _ j t1 t2 _ _
sbf_respected_simplified is opaque
Expands to: Constant prosa.analysis.definitions.sbf.plain.sbf_respected_simplified
Declared in library prosa.analysis.definitions.sbf.plain, line 39, characters 9-33
@sbf_respected_simplified
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (SBF : SupplyBoundFunction),
       @supply_bound_function_respected Job PState arr_seq sched SBF ->
       forall (j : Equality.sort Job) (t1 t2 : instant),
       @arrives_in Job arr_seq j ->
       is_true (t1 <= t2) -> is_true (SBF (t2 - t1) <= @supply_during Job PState sched t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Plain.sbf_respected_simplified : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  {SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction},
  Prosa.Analysis.Definitions.Sbf.Plain.supply_bound_function_respected arr_seq sched
      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
    ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        t1 ≤ t2 →
          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function (t2 - t1) ≤
            Prosa.Model.Processor.Supply.supply_during sched t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Plain_sbf_respected_simplified
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction),
       Prosa_Analysis_Definitions_Sbf_Plain_supply_bound_function_respected Job
         inst_3 PState arr_seq sched
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1))
         (Prosa_Model_Processor_Supply_supply_during Job
            inst_3 PState sched t1 t2)
```
