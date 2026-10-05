# `pred_sbf_respected`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.pred.pred_sbf_respected`
- Lean: `Prosa.Analysis.Definitions.Sbf.Pred.pred_sbf_respected`
- Certificate: `pred_sbf_respected_correspondence`

## Official Rocq

```coq
pred_sbf_respected :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> (Equality.sort Job -> instant -> instant -> Prop) -> (duration -> work) -> Prop

pred_sbf_respected is not universe polymorphic
Arguments pred_sbf_respected {Job PState} arr_seq sched (P SBF)%function_scope
pred_sbf_respected is transparent
Expands to: Constant prosa.analysis.definitions.sbf.pred.pred_sbf_respected
Declared in library prosa.analysis.definitions.sbf.pred, line 36, characters 13-31
@pred_sbf_respected
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job ->
       @schedule Job PState ->
       (Equality.sort Job -> instant -> instant -> Prop) -> (duration -> work) -> Prop
```

Body:

```coq
pred_sbf_respected =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (P : Equality.sort Job -> instant -> instant -> Prop)
  (SBF : duration -> work) =>
forall (j : Equality.sort Job) (t1 t2 : instant),
@arrives_in Job arr_seq j ->
P j t1 t2 ->
forall t : instant, is_true (t1 <= t <= t2) -> is_true (SBF (t - t1) <= @supply_during Job PState sched t1 t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       (Equality.sort Job -> instant -> instant -> Prop) -> (duration -> work) -> Prop

Arguments pred_sbf_respected {Job PState} arr_seq sched (P SBF)%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Pred.pred_sbf_respected : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          (Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop) →
            (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
def Prosa.Analysis.Definitions.Sbf.Pred.pred_sbf_respected.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          (Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop) →
            (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched P SBF =>
  ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
      P j t1 t2 →
        ∀ (t : Prosa.Behavior.Time.instant),
          t1 ≤ t ∧ t ≤ t2 → SBF (t - t1) ≤ Prosa.Model.Processor.Supply.supply_during sched t1 t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       (Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp) ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (P : Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp)
  (SBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) =>
forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arr_seq j ->
P j t1 t2 ->
forall t : Prosa_Behavior_Time_instant,
And (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t)
  (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t2) ->
LE_le_inst1 Prosa_Behavior_Job_work instLENat
  (SBF
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t t1))
  (Prosa_Model_Processor_Supply_supply_during Job
     inst_3 PState sched t1 t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       (Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp) ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected Job
  inst_3 PState 
  arr_seq sched (P SBF)%_function_scope
```
