# `readiness_interference_is_bounded`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.readiness_interference.readiness_interference_is_bounded`
- Lean: `Prosa.Analysis.Definitions.ReadinessInterference.readiness_interference_is_bounded`
- Certificate: `readiness_interference_is_bounded_correspondence`

## Official Rocq

```coq
readiness_interference_is_bounded :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@JobReady Job PState H0 H ->
arrival_sequence Job ->
@schedule Job PState ->
JLFP_policy Job -> Interference Job -> InterferingWorkload Job -> (duration -> duration -> duration) -> Prop

readiness_interference_is_bounded is not universe polymorphic
Arguments readiness_interference_is_bounded {Job H H0 PState JobReady0} arr_seq sched 
  {JLFP H2 H3} B%function_scope
readiness_interference_is_bounded is transparent
Expands to: Constant prosa.analysis.definitions.readiness_interference.readiness_interference_is_bounded
Declared in library prosa.analysis.definitions.readiness_interference, line 80, characters 15-48
@readiness_interference_is_bounded
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @JobReady Job PState H0 H ->
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job ->
       Interference Job -> InterferingWorkload Job -> (duration -> duration -> duration) -> Prop
```

Body:

```coq
readiness_interference_is_bounded =
fun (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
  (JobReady0 : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  (JLFP : JLFP_policy Job) (H2 : Interference Job) (H3 : InterferingWorkload Job)
  (B : duration -> duration -> duration) =>
forall (j : Equality.sort Job) (t1 t2 Δ : nat),
is_true (t1 + Δ <= t2) ->
@busy_interval_prefix Job H H0 PState sched H2 H3 j t1 t2 ->
is_true
  (@cumulative_readiness_interference Job H H0 PState JobReady0 arr_seq sched JLFP j t1 (t1 + Δ) <=
   B (@job_arrival Job H j - t1) Δ)
     : forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
       @JobReady Job PState H0 H ->
       arrival_sequence Job ->
       @schedule Job PState ->
       JLFP_policy Job ->
       Interference Job -> InterferingWorkload Job -> (duration -> duration -> duration) -> Prop

Arguments readiness_interference_is_bounded {Job H H0 PState JobReady0} arr_seq sched 
  {JLFP H2 H3} B%function_scope
```

## Lean

```lean
@Prosa.Analysis.Definitions.ReadinessInterference.readiness_interference_is_bounded : {Job :
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
                      (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
                        Prop
def Prosa.Analysis.Definitions.ReadinessInterference.readiness_interference_is_bounded.{u_1, u_2, u_3} : {Job :
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
                      (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
                        Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job] {PState}
    [Prosa.Behavior.Ready.JobReady Job PState] arr_seq sched [Prosa.Model.Priority.Definitions.JLFP_policy Job]
    [Prosa.Analysis.Abstract.Definitions.Interference Job] [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
    B =>
  ∀ (j : Job) (t1 t2 Δ : Prosa.Behavior.Time.instant),
    t1 + Δ ≤ t2 →
      Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
        Prosa.Analysis.Definitions.ReadinessInterference.cumulative_readiness_interference arr_seq sched j t1 (t1 + Δ) ≤
          B (Prosa.Behavior.Job.job_arrival j - t1) Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_ReadinessInterference_readiness_interference_is_bounded
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
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_ReadinessInterference_readiness_interference_is_bounded@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
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
             inst_3 PState)
  (inst_22 : 
   Prosa_Model_Priority_Definitions_JLFP_policy Job
     inst_3)
  (inst_25 : 
   Prosa_Analysis_Abstract_Definitions_Interference Job
     inst_3)
  (inst_28 : 
   Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
     inst_3)
  (B : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) =>
forall (j : Job) (t1 t2 _UU0394_ : Prosa_Behavior_Time_instant),
LE_le_inst1 Prosa_Behavior_Time_instant instLENat
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_)
  t2 ->
Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
  inst_3
  inst_25
  inst_28
  inst_6
  inst_9 PState sched j t1 t2 ->
LE_le_inst1 Nat instLENat
  (Prosa_Analysis_Definitions_ReadinessInterference_cumulative_readiness_interference Job
     inst_3
     inst_6
     inst_9 PState
     inst_14 arr_seq sched
     inst_22 j t1
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1 _UU0394_))
  (B
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        t1)
     _UU0394_)
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
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       SProp

Arguments Prosa_Analysis_Definitions_ReadinessInterference_readiness_interference_is_bounded 
  Job inst_3
  inst_6
  inst_9 
  PState inst_14 
  arr_seq sched inst_22
  inst_25
  inst_28 
  B%_function_scope
```
