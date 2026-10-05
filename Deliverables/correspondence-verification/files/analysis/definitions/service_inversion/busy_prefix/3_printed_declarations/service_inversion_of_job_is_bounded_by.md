# `service_inversion_of_job_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_of_job_is_bounded_by`
- Lean: `Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_of_job_is_bounded_by`
- Certificate: `service_inversion_of_job_is_bounded_by_correspondence`

## Official Rocq

```coq
service_inversion_of_job_is_bounded_by :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job ->
@schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> (duration -> duration) -> Prop

service_inversion_of_job_is_bounded_by is not universe polymorphic
Arguments service_inversion_of_job_is_bounded_by {Job H1 H2 PState} arr_seq sched {H3} j B%function_scope
service_inversion_of_job_is_bounded_by is transparent
Expands to: Constant
            prosa.analysis.definitions.service_inversion.busy_prefix.service_inversion_of_job_is_bounded_by
Declared in library prosa.analysis.definitions.service_inversion.busy_prefix, line 40, characters 13-51
@service_inversion_of_job_is_bounded_by
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> (duration -> duration) -> Prop
```

Body:

```coq
service_inversion_of_job_is_bounded_by =
fun (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (H3 : JLFP_policy Job)
  (j : Equality.sort Job) =>
       (@busy_interval_prefix Job H1 H2 PState arr_seq sched H3) j]
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> (duration -> duration) -> Prop

Arguments service_inversion_of_job_is_bounded_by {Job H1 H2 PState} arr_seq sched {H3} j B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_of_job_is_bounded_by : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule PState →
              [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                Job → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix.service_inversion_of_job_is_bounded_by.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            Prosa.Behavior.Schedule.schedule PState →
              [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                Job → (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState} arr_seq sched
    [Prosa.Model.Priority.Definitions.JLFP_policy Job] j B =>
  Prosa.Analysis.Definitions.ServiceInversion.Pred.pred_service_inversion_of_job_is_bounded_by arr_seq sched
    (Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched) j B
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_of_job_is_bounded_by
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_10 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_10 ->
       Job -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_of_job_is_bounded_by@{u_1 u_2 u_3
Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : 
   DecidableEq Job)
  (inst_17 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_10)
  (inst_20 : 
   Prosa_Behavior_Job_JobCost Job
     inst_10)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_10
             PState)
  (inst_29 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_10)
  (j : Job) (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by Job
  inst_10
  inst_17 PState arr_seq
  sched
  (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
     inst_10
     inst_29)
  (Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
     inst_10
     inst_17
     inst_20 PState
     arr_seq sched
     inst_29)
  j B
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job
         inst_10 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_10,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_10 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_10 ->
       Job -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_of_job_is_bounded_by 
  Job inst_10
  inst_17
  inst_20 
  PState arr_seq sched
  inst_29 
  j B%_function_scope
```
