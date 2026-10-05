# `priority_inversion_cond`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.priority_inversion.priority_inversion_cond`
- Lean: `Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond`
- Certificate: `priority_inversion_cond_correspondence`

## Official Rocq

```coq
priority_inversion_cond :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> instant -> bool

priority_inversion_cond is not universe polymorphic
Arguments priority_inversion_cond {Job PState} arr_seq sched {H2} j P t
priority_inversion_cond is transparent
Expands to: Constant prosa.analysis.definitions.priority_inversion.priority_inversion_cond
Declared in library prosa.analysis.definitions.priority_inversion, line 47, characters 13-36
@priority_inversion_cond
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> instant -> bool
```

Body:

```coq
priority_inversion_cond =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H2 : JLFP_policy Job) (j : Equality.sort Job)
  (P : pred (Equality.sort Job)) (t : instant) =>
(j \notin @scheduled_jobs_at Job PState arr_seq sched t) &&
@has (Equality.sort Job) (fun jlp : Equality.sort Job => ~~ @hep_job Job H2 jlp j && P jlp)
  (@scheduled_jobs_at Job PState arr_seq sched t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Equality.sort Job -> pred (Equality.sort Job) -> instant -> bool

Arguments priority_inversion_cond {Job PState} arr_seq sched {H2} j P t
```

## Lean

```lean
@Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → (Job → Bool) → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_cond.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
            Job → (Job → Bool) → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job] j P t =>
  !decide (j ∈ Prosa.Model.Schedule.Scheduled.scheduled_jobs_at arr_seq sched t) &&
    (Prosa.Model.Schedule.Scheduled.scheduled_jobs_at arr_seq sched t).any fun jlp =>
      !Prosa.Model.Priority.Definitions.hep_job jlp j && P jlp
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> (Job -> Bool) -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (inst_26 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_7)
  (j : Job) (P : Job -> Bool) (t : Prosa_Behavior_Time_instant) =>
Bool_and
  (Bool_not
     (Decidable_decide
        (Membership_mem Job (List Job) (List_instMembership Job)
           (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
              inst_7 PState
              arr_seq sched t)
           j)
        (List_instDecidableMemOfLawfulBEq Job
           (instBEqOfDecidableEq Job
              inst_7)
           (instLawfulBEq Job
              inst_7)
           j
           (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
              inst_7 PState
              arr_seq sched t))))
  (List_any Job
     (Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job
        inst_7 PState arr_seq
        sched t)
     (fun jlp : Job =>
      Bool_and
        (Bool_not
           (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
              inst_7
              inst_26 jlp j))
        (P jlp)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_7 ->
       Job -> (Job -> Bool) -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond Job
  inst_7 
  PState arr_seq sched inst_26 
  j P%_function_scope t
```
