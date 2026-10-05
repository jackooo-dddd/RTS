# `valid_pred_sbf`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.pred.valid_pred_sbf`
- Lean: `Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf`
- Certificate: `pred_valid_pred_sbf_correspondence`

## Official Rocq

```coq
valid_pred_sbf :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> (Equality.sort Job -> instant -> instant -> Prop) -> (duration -> work) -> Prop

valid_pred_sbf is not universe polymorphic
Arguments valid_pred_sbf {Job PState} arr_seq sched (P SBF)%function_scope
valid_pred_sbf is transparent
Expands to: Constant prosa.analysis.definitions.sbf.pred.valid_pred_sbf
Declared in library prosa.analysis.definitions.sbf.pred, line 47, characters 13-27
@valid_pred_sbf
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job ->
       @schedule Job PState ->
       (Equality.sort Job -> instant -> instant -> Prop) -> (duration -> work) -> Prop
```

Body:

```coq
valid_pred_sbf =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (P : Equality.sort Job -> instant -> instant -> Prop)
  (SBF : duration -> work) =>
SBF 0 = 0 /\ @pred_sbf_respected Job PState arr_seq sched P SBF
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       (Equality.sort Job -> instant -> instant -> Prop) -> (duration -> work) -> Prop

Arguments valid_pred_sbf {Job PState} arr_seq sched (P SBF)%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          (Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop) →
            (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
def Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          (Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop) →
            (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched P SBF =>
  SBF 0 = 0 ∧ Prosa.Analysis.Definitions.Sbf.Pred.pred_sbf_respected arr_seq sched P SBF
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf
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
Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
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
And
  (@eq Prosa_Behavior_Job_work (SBF (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
  (Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected Job
     inst_3 PState arr_seq sched P SBF)
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

Arguments Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf Job
  inst_3 PState 
  arr_seq sched (P SBF)%_function_scope
```
