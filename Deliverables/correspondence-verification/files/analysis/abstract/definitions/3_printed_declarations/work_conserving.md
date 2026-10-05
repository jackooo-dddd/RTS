# `work_conserving`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.work_conserving`
- Lean: `Prosa.Analysis.Abstract.Definitions.work_conserving`
- Certificate: `ad_work_conserving_correspondence`

## Official Rocq

```coq
work_conserving :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> Interference Job -> InterferingWorkload Job -> Prop

work_conserving is not universe polymorphic
Arguments work_conserving {Job H0 H1 PState} arr_seq sched {H2 H3}
work_conserving is transparent
Expands to: Constant prosa.analysis.abstract.definitions.work_conserving
Declared in library prosa.analysis.abstract.definitions, line 216, characters 15-30
@work_conserving
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       arrival_sequence Job -> @schedule Job PState -> Interference Job -> InterferingWorkload Job -> Prop
```

Body:

```coq
work_conserving =
fun (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (H2 : Interference Job)
  (H3 : InterferingWorkload Job) =>
forall (j : Equality.sort Job) (t1 t2 : instant) (t : nat),
@arrives_in Job arr_seq j ->
is_true (0 < @job_cost Job H1 j) ->
@busy_interval_prefix Job H0 H1 PState sched H2 H3 j t1 t2 ->
is_true (t1 <= t < t2) ->
~ is_true (@interference Job H2 j t) <-> is_true (@receives_service_at Job PState sched j t)
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> Interference Job -> InterferingWorkload Job -> Prop

Arguments work_conserving {Job H0 H1 PState} arr_seq sched {H2 H3}
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.work_conserving : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop
def Prosa.Analysis.Abstract.Definitions.work_conserving.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job]
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] {PState} arrSeq sched =>
  ∀ (j : Job) (t1 t2 t : Prosa.Behavior.Time.instant),
    Prosa.Behavior.Arrival_sequence.arrives_in arrSeq j →
      Prosa.Behavior.Job.job_cost j > 0 →
        Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
          t1 ≤ t ∧ t < t2 →
            (¬Prosa.Analysis.Abstract.Definitions.interference j t = true ↔
              Prosa.Behavior.Service.receives_service_at sched j t = true)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_work_conserving
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_work_conserving@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_3)
  (inst_12 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_15 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arrSeq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall (j : Job) (t1 t2 t : Prosa_Behavior_Time_instant),
Prosa_Behavior_Arrival_sequence_arrives_in Job
  inst_3 arrSeq j ->
GT_gt_inst1 Prosa_Behavior_Job_work instLTNat
  (Prosa_Behavior_Job_JobCost_job_cost Job
     inst_3
     inst_15 j)
  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)) ->
Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState sched j t1 t2 ->
And (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t)
  (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) ->
Iff
  (Not
     (@eq Bool
        (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
           inst_3
           inst_6 j t)
        Bool_true))
  (@eq Bool
     (Prosa_Behavior_Service_receives_service_at Job
        inst_3 PState sched j t)
     Bool_true)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Analysis_Abstract_Definitions_work_conserving Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState 
  arrSeq sched
```
