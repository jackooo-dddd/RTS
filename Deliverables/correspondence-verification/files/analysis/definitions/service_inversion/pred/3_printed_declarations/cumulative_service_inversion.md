# `cumulative_service_inversion`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service_inversion.pred.cumulative_service_inversion`
- Lean: `Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion`
- Certificate: `cumulative_service_inversion_correspondence`

## Official Rocq

```coq
cumulative_service_inversion :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> JLDP_policy Job -> Equality.sort Job -> instant -> instant -> nat

cumulative_service_inversion is not universe polymorphic
Arguments cumulative_service_inversion {Job PState} arr_seq sched {H3} j t1 t2
cumulative_service_inversion is transparent
Expands to: Constant prosa.analysis.definitions.service_inversion.pred.cumulative_service_inversion
Declared in library prosa.analysis.definitions.service_inversion.pred, line 51, characters 13-41
@cumulative_service_inversion
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job ->
       @schedule Job PState -> JLDP_policy Job -> Equality.sort Job -> instant -> instant -> nat
```

Body:

```coq
cumulative_service_inversion =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H3 : JLDP_policy Job) (j : Equality.sort Job) (t1 t2 : instant) =>
\sum_(t1 <= t < t2) nat_of_bool (@service_inversion Job PState arr_seq sched H3 j t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLDP_policy Job -> Equality.sort Job -> instant -> instant -> nat

Arguments cumulative_service_inversion {Job PState} arr_seq sched {H3} j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
            Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
            Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched [Prosa.Model.Priority.Definitions.JLDP_policy Job] j t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2, (Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion arr_seq sched j t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (inst_12 : 
   Prosa_Model_Priority_Definitions_JLDP_policy Job
     inst_3)
  (j : Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_foldr_inst3 Nat Nat Nat_add (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (List_map_inst3 Prosa_Behavior_Time_instant Nat
     (fun t : Prosa_Behavior_Time_instant =>
      Bool_toNat
        (Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion Job
           inst_3
           PState arr_seq sched
           inst_12
           j t))
     (List_range' t1
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion 
  Job inst_3 
  PState arr_seq sched inst_15
  j t1 t2
```
