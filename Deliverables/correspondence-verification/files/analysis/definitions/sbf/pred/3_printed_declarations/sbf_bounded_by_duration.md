# `sbf_bounded_by_duration`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.definitions.sbf.pred.sbf_bounded_by_duration`
- Lean: `Prosa.Analysis.Definitions.Sbf.Pred.sbf_bounded_by_duration`
- Certificate: `pred_sbf_bounded_by_duration_statement_correspondence`

## Official Rocq

```coq
sbf_bounded_by_duration :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (P : Equality.sort Job -> instant -> instant -> Prop)
  {SBF : SupplyBoundFunction},
@valid_pred_sbf Job PState arr_seq sched P SBF ->
unit_supply_bound_function SBF -> forall δ : duration, is_true (SBF δ <= δ)

sbf_bounded_by_duration is not universe polymorphic
Arguments sbf_bounded_by_duration {Job PState} arr_seq sched P%function_scope {SBF} _ _ δ
sbf_bounded_by_duration is opaque
Expands to: Constant prosa.analysis.definitions.sbf.pred.sbf_bounded_by_duration
Declared in library prosa.analysis.definitions.sbf.pred, line 70, characters 9-32
@sbf_bounded_by_duration
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (P : Equality.sort Job -> instant -> instant -> Prop)
         (SBF : SupplyBoundFunction),
       @valid_pred_sbf Job PState arr_seq sched P SBF ->
       unit_supply_bound_function SBF -> forall δ : duration, is_true (SBF δ <= δ)
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Pred.sbf_bounded_by_duration : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (P : Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop)
  {SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction},
  Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf arr_seq sched P
      Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
    Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
      ∀ (δ : Prosa.Behavior.Time.duration),
        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function δ ≤ δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Pred_sbf_bounded_by_duration
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp)
         (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction),
       Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job
         inst_3 PState arr_seq sched P
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall _UU03b4_ : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU03b4_) _UU03b4_
```
