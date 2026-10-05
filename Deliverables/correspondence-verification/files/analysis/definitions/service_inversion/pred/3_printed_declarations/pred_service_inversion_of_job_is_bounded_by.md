# `pred_service_inversion_of_job_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_of_job_is_bounded_by`
- Lean: `Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_of_job_is_bounded_by`
- Certificate: `pred_service_inversion_of_job_is_bounded_by_correspondence`

## Official Rocq

```coq
pred_service_inversion_of_job_is_bounded_by :
forall {Job : JobType},
JobArrival Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState ->
JLDP_policy Job ->
(Equality.sort Job -> instant -> instant -> Prop) -> Equality.sort Job -> (duration -> duration) -> Prop

pred_service_inversion_of_job_is_bounded_by is not universe polymorphic
Arguments pred_service_inversion_of_job_is_bounded_by {Job H1 PState} arr_seq sched 
  {H3} P%function_scope j B%function_scope
pred_service_inversion_of_job_is_bounded_by is transparent
Expands to: Constant
            prosa.analysis.definitions.service_inversion.pred.pred_service_inversion_of_job_is_bounded_by
Declared in library prosa.analysis.definitions.service_inversion.pred, line 63, characters 13-56
@pred_service_inversion_of_job_is_bounded_by
     : forall Job : JobType,
       JobArrival Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState ->
       JLDP_policy Job ->
       (Equality.sort Job -> instant -> instant -> Prop) ->
       Equality.sort Job -> (duration -> duration) -> Prop
```

Body:

```coq
pred_service_inversion_of_job_is_bounded_by =
fun (Job : JobType) (H1 : JobArrival Job) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (H3 : JLDP_policy Job) (P : Equality.sort Job -> instant -> instant -> Prop)
  (j : Equality.sort Job) (B : duration -> duration) =>
forall t1 t2 : instant,
P j t1 t2 ->
is_true (@cumulative_service_inversion Job PState arr_seq sched H3 j t1 t2 <= B (@job_arrival Job H1 j - t1))
     : forall {Job : JobType},
       JobArrival Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState ->
       JLDP_policy Job ->
       (Equality.sort Job -> instant -> instant -> Prop) ->
       Equality.sort Job -> (duration -> duration) -> Prop

Arguments pred_service_inversion_of_job_is_bounded_by {Job H1 PState} arr_seq sched 
  {H3} P%function_scope j B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_of_job_is_bounded_by : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule PState →
            [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
              (Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop) →
                Job → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_of_job_is_bounded_by.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
          Prosa.Behavior.Schedule.schedule PState →
            [Prosa.Model.Priority.Definitions.JLDP_policy Job] →
              (Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Prop) →
                Job → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLDP_policy Job] P j B =>
  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
    P j t1 t2 →
      Prosa.Analysis.Definitions.ServiceInversion.Pred.cumulative_service_inversion arr_seq sched j t1 t2 ≤
        B (Prosa.Behavior.Job.job_arrival j - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       (Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp) ->
       Job -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by@{u_1 u_2 u_3
Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_15 : 
   Prosa_Model_Priority_Definitions_JLDP_policy Job
     inst_3)
  (P : Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp) 
  (j : Job) (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
forall t1 t2 : Prosa_Behavior_Time_instant,
P j t1 t2 ->
LE_le_inst1 Nat instLENat
  (Prosa_Analysis_Definitions_ServiceInversion_Pred_cumulative_service_inversion Job
     inst_3 PState arr_seq
     sched inst_15 j t1 t2)
  (B
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        t1))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLDP_policy Job
         inst_3 ->
       (Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> SProp) ->
       Job -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by 
  Job inst_3
  inst_6 
  PState arr_seq sched inst_15
  P%_function_scope j B%_function_scope
```
