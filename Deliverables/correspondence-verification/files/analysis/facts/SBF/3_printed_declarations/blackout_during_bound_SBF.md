# `blackout_during_bound_SBF`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.SBF.blackout_during_bound_SBF`
- Lean: `Prosa.Analysis.Facts.SBF.blackout_during_bound_SBF`
- Certificate: `blackout_during_bound_SBF_correspondence`

## Official Rocq

```coq
blackout_during_bound_SBF :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (P : Equality.sort Job -> instant -> instant -> Prop) {SBF : SupplyBoundFunction},
@valid_pred_sbf Job PState arr_seq sched P SBF ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
forall t1 t2 : instant,
P j t1 t2 ->
forall Δ : duration,
is_true (t1 + Δ <= t2) -> is_true (@blackout_during Job PState sched t1 (t1 + Δ) <= Δ - SBF Δ)

blackout_during_bound_SBF is not universe polymorphic
Arguments blackout_during_bound_SBF {Job PState} H_unit_supply_proc_model arr_seq 
  sched P%function_scope {SBF} H_valid_SBF j H_arrives_in t1 t2 H_P_interval Δ H_subinterval
blackout_during_bound_SBF is opaque
Expands to: Constant prosa.analysis.facts.SBF.blackout_during_bound_SBF
Declared in library prosa.analysis.facts.SBF, line 84, characters 10-35
@blackout_during_bound_SBF
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
         (P : Equality.sort Job -> instant -> instant -> Prop) (SBF : SupplyBoundFunction),
       @valid_pred_sbf Job PState arr_seq sched P SBF ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       forall t1 t2 : instant,
       P j t1 t2 ->
       forall Δ : duration,
       is_true (t1 + Δ <= t2) -> is_true (@blackout_during Job PState sched t1 (t1 + Δ) <= Δ - SBF Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.SBF.blackout_during_bound_SBF : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (P : Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop)
      {SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction},
      Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf arr_seq sched P
          Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
        ∀ (j : Job),
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
            ∀ (t1 t2 : Prosa.Behavior.Time.instant),
              P j t1 t2 →
                ∀ (Δ : Prosa.Behavior.Time.duration),
                  t1 + Δ ≤ t2 →
                    Prosa.Model.Processor.Supply.blackout_during sched t1 (t1 + Δ) ≤
                      Δ - Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_SBF_blackout_during_bound_SBF
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp)
         (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction),
       Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job
         inst_3 PState arr_seq sched P
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       P j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
         t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Processor_Supply_blackout_during Job
            inst_3 PState sched t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
               _UU0394_))
         (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work Prosa_Behavior_Time_duration
            (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) _UU0394_
            (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF _UU0394_))
```
