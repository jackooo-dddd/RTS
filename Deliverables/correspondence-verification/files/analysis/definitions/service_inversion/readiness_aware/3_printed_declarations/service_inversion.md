# `service_inversion`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion`
- Lean: `Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion`
- Certificate: `service_inversion_correspondence`

## Official Rocq

```coq
service_inversion :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@JobReady Job PState H0 H ->
arrival_sequence Job -> @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

service_inversion is not universe polymorphic
Arguments service_inversion {Job H H0 PState JobReady0} arr_seq sched {H1} j t
service_inversion is transparent
Expands to: Constant prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion
Declared in library prosa.analysis.definitions.service_inversion.readiness_aware, line 43, characters 15-32
@service_inversion
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @JobReady Job PState H0 H ->
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
service_inversion =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (JobReady0 : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (H1 : JLFP_policy Job) (j : Equality.sort Job) =>
let readiness_oblivious_service_inversion :=
  @pred.service_inversion Job PState arr_seq sched (@JLFP_to_JLDP Job H1) in
fun t : instant =>
@some_hep_job_ready Job H H0 PState JobReady0 arr_seq sched H1 j t &&
readiness_oblivious_service_inversion j t
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
       @JobReady Job PState H0 H ->
       arrival_sequence Job ->
       @schedule Job PState -> JLFP_policy Job -> Equality.sort Job -> instant -> bool

Arguments service_inversion {Job H H0 PState JobReady0} arr_seq sched {H1} j t
```

## Lean

```lean
@Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Model.Priority.Definitions.JLFP_policy Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Behavior.Ready.JobReady Job PState] arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job] j t =>
  Prosa.Analysis.Definitions.ReadinessInterference.some_hep_job_ready arr_seq sched j t &&
    Prosa.Analysis.Definitions.ServiceInversion.Pred.service_inversion arr_seq sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (inst_6 : 
   Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (inst_9 : 
   Prosa_Behavior_Job_JobCost Job
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (inst_14 : 
   Prosa_Behavior_Ready_JobReady Job
     inst_3 PState
     inst_9
     inst_6)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (inst_22 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Bool_and
  (Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready Job
     inst_3
     inst_6
     inst_9 PState
     inst_14 arr_seq
     sched inst_22 j
     t)
  (Prosa_Analysis_Definitions_ServiceInversion_Pred_service_inversion Job
     inst_3 PState
     arr_seq sched
     (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
        inst_3
        inst_22)
     j t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion 
  Job inst_3
  inst_6
  inst_9 
  PState inst_14 
  arr_seq sched inst_22 
  j t
```
