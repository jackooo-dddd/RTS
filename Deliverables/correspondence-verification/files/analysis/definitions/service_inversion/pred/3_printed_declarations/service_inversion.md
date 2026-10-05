# `service_inversion`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service_inversion.pred.service_inversion`
- Lean: `Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion`
- Certificate: `service_inversion_correspondence`

## Official Rocq

```coq
service_inversion :
forall {Job : JobType} {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> JLDP_policy Job -> Equality.sort Job -> instant -> bool

service_inversion is not universe polymorphic
Arguments service_inversion {Job PState} arr_seq sched {H3} j t
service_inversion is transparent
Expands to: Constant prosa.analysis.definitions.service_inversion.pred.service_inversion
Declared in library prosa.analysis.definitions.service_inversion.pred, line 45, characters 13-30
@service_inversion
     : forall (Job : JobType) (PState : ProcessorState Job),
       arrival_sequence Job ->
       @schedule Job PState -> JLDP_policy Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
service_inversion =
fun (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H3 : JLDP_policy Job) (j : Equality.sort Job) (t : instant) =>
(j \notin @served_jobs_at Job PState arr_seq sched t) &&
@has (Equality.sort Job) (fun jlp : Equality.sort Job => ~~ @hep_job_at Job H3 t jlp j)
  (@served_jobs_at Job PState arr_seq sched t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLDP_policy Job -> Equality.sort Job -> instant -> bool

Arguments service_inversion {Job PState} arr_seq sched {H3} j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLDP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
        Prosa.Behavior.Schedule.schedule PState →
          [Prosa.Model.Priority.Definitions.JLDP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} arr_seq sched [Prosa.Model.Priority.Definitions.JLDP_policy Job] j t =>
  !decide (j ∈ Prosa.Analysis.Definitions.Service.served_jobs_at arr_seq sched t) &&
    (Prosa.Analysis.Definitions.Service.served_jobs_at arr_seq sched t).any fun jlp =>
      !Prosa.Model.Priority.Definitions.hep_job_at t jlp j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion
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
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_15 : 
   Prosa_Model_Priority_Definitions_JLDP_policy Job
     inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Bool_and
  (Bool_not
     (Decidable_decide
        (Membership_mem Job (List Job) (List_instMembership Job)
           (Prosa_Analysis_Definitions_Service_served_jobs_at Job
              inst_3 PState
              arr_seq sched t)
           j)
        (List_instDecidableMemOfLawfulBEq Job
           (instBEqOfDecidableEq Job
              inst_3)
           (instLawfulBEq Job
              inst_3)
           j
           (Prosa_Analysis_Definitions_Service_served_jobs_at Job
              inst_3 PState
              arr_seq sched t))))
  (List_any Job
     (Prosa_Analysis_Definitions_Service_served_jobs_at Job
        inst_3 PState arr_seq
        sched t)
     (fun jlp : Job =>
      Bool_not
        (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
           inst_3
           inst_15 t jlp j)))
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
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion Job
  inst_3 
  PState arr_seq sched inst_15
  j t
```
