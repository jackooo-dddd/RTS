# `backlogged`

- Kind (Rocq): Definition
- Rocq: `prosa.behavior.ready.backlogged`
- Lean: `Prosa.Behavior.Ready.backlogged`
- Certificate: ``

## Official Rocq

```coq
backlogged :
forall {Job : JobType} {PState : ProcessorState Job} {jc : JobCost Job} {ja : JobArrival Job},
@JobReady Job PState jc ja -> @schedule Job PState -> Equality.sort Job -> instant -> bool

backlogged is not universe polymorphic
Arguments backlogged {Job PState jc ja jr} sched j t
backlogged is transparent
Expands to: Constant prosa.behavior.ready.backlogged
Declared in library prosa.behavior.ready, line 34, characters 13-23
@backlogged
     : forall (Job : JobType) (PState : ProcessorState Job) (jc : JobCost Job) (ja : JobArrival Job),
       @JobReady Job PState jc ja -> @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
backlogged =
fun (Job : JobType) (PState : ProcessorState Job) (jc : JobCost Job) (ja : JobArrival Job)
  (jr : @JobReady Job PState jc ja) (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t : instant) =>
@job_ready Job PState jc ja jr sched j t && ~~ @scheduled_at Job PState sched j t
     : forall {Job : JobType} {PState : ProcessorState Job} {jc : JobCost Job} {ja : JobArrival Job},
       @JobReady Job PState jc ja -> @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments backlogged {Job PState jc ja jr} sched j t
```

## Lean

```lean
@Prosa.Behavior.Ready.backlogged : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      [inst_1 : Prosa.Behavior.Job.JobCost Job] →
        [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Behavior.Ready.backlogged.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      [inst_1 : Prosa.Behavior.Job.JobCost Job] →
        [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Ready.JobReady Job PState] →
            Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Ready.JobReady Job PState] sched j t =>
  Prosa.Behavior.Ready.job_ready sched j t && !Prosa.Behavior.Service.scheduled_at sched j t
```

## Lean, imported into Rocq

```coq
ImportedReady.Prosa_Behavior_Ready_backlogged
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_8 : ImportedReady.Prosa_Behavior_Job_JobCost
                                                                        Job
                                                                        inst_3)
         (inst_11 : ImportedReady.Prosa_Behavior_Job_JobArrival
                                                                         Job
                                                                         inst_3),
       ImportedReady.Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_8
         inst_11 ->
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedReady.Prosa_Behavior_Time_instant -> ImportedReady.Bool
```

Body:

```coq
ImportedReady.Prosa_Behavior_Ready_backlogged@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedReady.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedReady.DecidableEq Job)
  (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (inst_8 : 
   ImportedReady.Prosa_Behavior_Job_JobCost Job
     inst_3)
  (inst_11 : 
   ImportedReady.Prosa_Behavior_Job_JobArrival Job
     inst_3)
  (inst_14 : 
   ImportedReady.Prosa_Behavior_Ready_JobReady Job
     inst_3
     PState
     inst_8
     inst_11)
  (sched : ImportedReady.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (j : Job) (t : ImportedReady.Prosa_Behavior_Time_instant) =>
ImportedReady.Bool_and
  (ImportedReady.Prosa_Behavior_Ready_JobReady_job_ready Job
     inst_3
     PState
     inst_8
     inst_11
     inst_14
     sched j t)
  (ImportedReady.Bool_not
     (ImportedReady.Prosa_Behavior_Service_scheduled_at Job
        inst_3
        PState sched j t))
     : forall (Job : ImportedReady.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedReady.DecidableEq Job)
         (PState : ImportedReady.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_8 : ImportedReady.Prosa_Behavior_Job_JobCost
                                                                        Job
                                                                        inst_3)
         (inst_11 : ImportedReady.Prosa_Behavior_Job_JobArrival
                                                                         Job
                                                                         inst_3),
       ImportedReady.Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_8
         inst_11 ->
       ImportedReady.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> ImportedReady.Prosa_Behavior_Time_instant -> ImportedReady.Bool

Arguments ImportedReady.Prosa_Behavior_Ready_backlogged Job
  inst_3 PState
  inst_8
  inst_11 self a____at____internal__hyg0
  a____at____internal__hyg0 t
```
