# `service_inversion_is_bounded`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion_is_bounded`
- Lean: `Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion_is_bounded`
- Certificate: `service_inversion_is_bounded_correspondence`

## Official Rocq

```coq
service_inversion_is_bounded :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@JobReady Job PState H0 H ->
arrival_sequence Job ->
@schedule Job PState ->
JLFP_policy Job -> Interference Job -> InterferingWorkload Job -> (duration -> duration) -> Prop

service_inversion_is_bounded is not universe polymorphic
Arguments service_inversion_is_bounded {Job H H0 PState JobReady0} arr_seq sched {H1 H2 H3} B%function_scope
service_inversion_is_bounded is transparent
Expands to: Constant
            prosa.analysis.definitions.service_inversion.readiness_aware.service_inversion_is_bounded
Declared in library prosa.analysis.definitions.service_inversion.readiness_aware, line 64, characters 15-43
@service_inversion_is_bounded
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @JobReady Job PState H0 H ->
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Interference Job -> InterferingWorkload Job -> (duration -> duration) -> Prop
```

Body:

```coq
service_inversion_is_bounded =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (JobReady0 : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (H1 : JLFP_policy Job) (H2 : Interference Job) (H3 : InterferingWorkload Job) (B : duration -> duration) =>
forall (j : Equality.sort Job) (t1 t2 : instant),
@busy_interval_prefix Job H H0 PState sched H2 H3 j t1 t2 ->
is_true
  (@cumulative_service_inversion Job H H0 PState JobReady0 arr_seq sched H1 j t1 t2 <=
   B (@job_arrival Job H j - t1))
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
       @JobReady Job PState H0 H ->
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job -> Interference Job -> InterferingWorkload Job -> (duration -> duration) -> Prop

Arguments service_inversion_is_bounded {Job H H0 PState JobReady0} arr_seq sched {H1 H2 H3} B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion_is_bounded : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                  [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                      (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion_is_bounded.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobArrival Job] →
      [inst_2 : Prosa.Behavior.Job.JobCost Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState →
                [Prosa.Model.Priority.Definitions.JLFP_policy Job] →
                  [Prosa.Analysis.Abstract.Definitions.Interference Job] →
                    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
                      (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Behavior.Ready.JobReady Job PState] arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job]
    [Prosa.Analysis.Abstract.Definitions.Interference Job] [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
    B =>
  ∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
    Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
      Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.cumulative_service_inversion arr_seq sched j t1 t2 ≤
        B (Prosa.Behavior.Job.job_arrival j - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion_is_bounded
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
         inst_3
         PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3
         PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion_is_bounded@{u_1 u_2 u_3
Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0
Lean.u_3+2.0} =
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
  (inst_25 : 
   Prosa_Analysis_Abstract_Definitions_Interference Job
     inst_3)
  (inst_28 : 
   Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
     inst_3)
  (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
  inst_3
  inst_25
  inst_28
  inst_6
  inst_9 PState
  sched j t1 t2 ->
LE_le_inst1 Nat instLENat
  (Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_cumulative_service_inversion Job
     inst_3
     inst_6
     inst_9 PState
     inst_14 arr_seq
     sched inst_22 j
     t1 t2)
  (B
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        t1))
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
         inst_3
         PState
         inst_9
         inst_6 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3
         PState ->
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> SProp

Arguments Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion_is_bounded 
  Job inst_3
  inst_6
  inst_9 
  PState inst_14
  arr_seq sched
  inst_22
  inst_25
  inst_28
  B%_function_scope
```
