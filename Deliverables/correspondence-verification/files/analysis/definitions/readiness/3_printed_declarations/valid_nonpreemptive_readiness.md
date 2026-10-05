# `valid_nonpreemptive_readiness`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.readiness.valid_nonpreemptive_readiness`
- Lean: `Prosa.Analysis.Definitions.Readiness.valid_nonpreemptive_readiness`
- Certificate: `valid_nonpreemptive_readiness_correspondence`

## Official Rocq

```coq
valid_nonpreemptive_readiness :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job},
@JobReady Job PState H H0 -> JobPreemptable Job -> @schedule Job PState -> Prop

valid_nonpreemptive_readiness is not universe polymorphic
Arguments valid_nonpreemptive_readiness {Job H H0 PState} ReadinessModel {H1} sched
valid_nonpreemptive_readiness is transparent
Expands to: Constant prosa.analysis.definitions.readiness.valid_nonpreemptive_readiness
Declared in library prosa.analysis.definitions.readiness, line 45, characters 13-42
@valid_nonpreemptive_readiness
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job),
       @JobReady Job PState H H0 -> JobPreemptable Job -> @schedule Job PState -> Prop
```

Body:

```coq
valid_nonpreemptive_readiness =
fun (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
  (ReadinessModel : @JobReady Job PState H H0) (H1 : JobPreemptable Job) (sched : @schedule Job PState) =>
forall (j : Equality.sort Job) (t : instant),
is_true (~~ @job_preemptable Job H1 j (@service Job PState sched j t)) ->
is_true (@job_ready Job PState H H0 ReadinessModel sched j t)
     : forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job},
       @JobReady Job PState H H0 -> JobPreemptable Job -> @schedule Job PState -> Prop

Arguments valid_nonpreemptive_readiness {Job H H0 PState} ReadinessModel {H1} sched
```

## Lean

```lean
@Prosa.Analysis.Definitions.Readiness.valid_nonpreemptive_readiness : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Ready.JobReady Job PState →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Prosa.Behavior.Schedule.schedule PState → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Readiness.valid_nonpreemptive_readiness.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
          Prosa.Behavior.Ready.JobReady Job PState →
            [Prosa.Model.Preemption.Parameter.JobPreemptable Job] → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] {PState} ReadinessModel
    [Prosa.Model.Preemption.Parameter.JobPreemptable Job] sched =>
  ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
    (!Prosa.Model.Preemption.Parameter.job_preemptable j (Prosa.Behavior.Service.service sched j t)) = true →
      Prosa.Behavior.Ready.job_ready sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Readiness_valid_nonpreemptive_readiness
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_6
         inst_9 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Readiness_valid_nonpreemptive_readiness@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (ReadinessModel : Prosa_Behavior_Ready_JobReady Job
                      inst_3 PState
                      inst_6
                      inst_9)
  (inst_17 : Prosa_Model_Preemption_Parameter_JobPreemptable
                                                                                Job
                                                                                inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
forall (j : Job) (t : Prosa_Behavior_Time_instant),
@eq Bool
  (Bool_not
     (Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job
        inst_3
        inst_17 j
        (Prosa_Behavior_Service_service Job
           inst_3 PState sched j t)))
  Bool_true ->
@eq Bool
  (Prosa_Behavior_Ready_JobReady_job_ready Job
     inst_3 PState
     inst_6
     inst_9 ReadinessModel sched j t)
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_6
         inst_9 ->
       Prosa_Model_Preemption_Parameter_JobPreemptable Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Analysis_Definitions_Readiness_valid_nonpreemptive_readiness Job
  inst_3
  inst_6
  inst_9 PState 
  ReadinessModel inst_17 
  sched
```
