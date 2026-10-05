# `cumulative_priority_inversion_cond`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.priority_inversion.cumulative_priority_inversion_cond`
- Lean: `Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion_cond`
- Certificate: `cumulative_priority_inversion_cond_correspondence`

## Official Rocq

```coq
cumulative_priority_inversion_cond :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> instant -> instant -> nat

cumulative_priority_inversion_cond is not universe polymorphic
Arguments cumulative_priority_inversion_cond {Job PState} arr_seq sched {H2} j P t1 t2
cumulative_priority_inversion_cond is transparent
Expands to: Constant prosa.analysis.definitions.priority_inversion.cumulative_priority_inversion_cond
Declared in library prosa.analysis.definitions.priority_inversion, line 62, characters 13-47
@cumulative_priority_inversion_cond
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> instant -> instant -> nat
```

Body:

```coq
cumulative_priority_inversion_cond =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H2 : JLFP_policy Job) (j : Equality.sort Job)
  (P : pred (Equality.sort Job)) (t1 t2 : instant) =>
\sum_(t1 <= t < t2) nat_of_bool (@priority_inversion_cond Job PState arr_seq sched H2 j P t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> instant -> instant -> nat

Arguments cumulative_priority_inversion_cond {Job PState} arr_seq sched {H2} j P t1 t2
```

## Lean

```lean
@Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion_cond : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
            Job → (Job → Bool) → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion_cond.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
            Job → (Job → Bool) → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job] j P t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2,
    (Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond arr_seq sched j P t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_cond
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> (Job -> Bool) -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_cond@{u_1 u_2 u_3 Lean.u_1+1.0
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
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (j : Job) (P : Job -> Bool) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_foldr_inst3 Nat Nat Nat_add (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (List_map_inst3 Prosa_Behavior_Time_instant Nat
     (fun t : Prosa_Behavior_Time_instant =>
      Bool_toNat
        (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond Job
           inst_3
           PState arr_seq sched
           inst_12
           j P t))
     (List_range' t1
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> (Job -> Bool) -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_cond 
  Job inst_7 
  PState arr_seq sched inst_26 
  j P%_function_scope t1 t2
```
