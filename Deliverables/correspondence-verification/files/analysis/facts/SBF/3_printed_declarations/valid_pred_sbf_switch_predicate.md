# `valid_pred_sbf_switch_predicate`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.SBF.valid_pred_sbf_switch_predicate`
- Lean: `Prosa.Analysis.Facts.SBF.valid_pred_sbf_switch_predicate`
- Certificate: `valid_pred_sbf_switch_predicate_correspondence`

## Official Rocq

```coq
valid_pred_sbf_switch_predicate :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {SBF : SupplyBoundFunction}
  (P1 P2 : Equality.sort Job -> instant -> instant -> Prop),
(forall (j : Equality.sort Job) (t1 t2 : instant), @arrives_in Job arr_seq j -> P2 j t1 t2 -> P1 j t1 t2) ->
@valid_pred_sbf Job PState arr_seq sched P1 SBF -> @valid_pred_sbf Job PState arr_seq sched P2 SBF

valid_pred_sbf_switch_predicate is not universe polymorphic
Arguments valid_pred_sbf_switch_predicate {Job PState} arr_seq sched {SBF}
  (P1 P2 H_p2_implies_p1)%function_scope _
valid_pred_sbf_switch_predicate is opaque
Expands to: Constant prosa.analysis.facts.SBF.valid_pred_sbf_switch_predicate
Declared in library prosa.analysis.facts.SBF, line 44, characters 10-41
@valid_pred_sbf_switch_predicate
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (SBF : SupplyBoundFunction)
         (P1 P2 : Equality.sort Job -> instant -> instant -> Prop),
       (forall (j : Equality.sort Job) (t1 t2 : instant),
        @arrives_in Job arr_seq j -> P2 j t1 t2 -> P1 j t1 t2) ->
       @valid_pred_sbf Job PState arr_seq sched P1 SBF -> @valid_pred_sbf Job PState arr_seq sched P2 SBF
```

## Lean

```lean
@Prosa.Analysis.Facts.SBF.valid_pred_sbf_switch_predicate : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  {SBF : Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction}
  (P1 P2 : Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop),
  (∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j → P2 j t1 t2 → P1 j t1 t2) →
    Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf arr_seq sched P1
        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function →
      Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf arr_seq sched P2
        Prosa.Analysis.Definitions.Sbf.SupplyBoundFunction.supply_bound_function
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_SBF_valid_pred_sbf_switch_predicate
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (SBF : Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction)
         (P1 P2 : Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp),
       (forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_3 arr_seq j ->
        P2 j t1 t2 -> P1 j t1 t2) ->
       Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job
         inst_3 PState arr_seq sched P1
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF) ->
       Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job
         inst_3 PState arr_seq sched P2
         (Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function SBF)
```
