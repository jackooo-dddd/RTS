# `basic_readiness_compliance`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.readiness.basic.basic_readiness_compliance`
- Lean: `Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_compliance`
- Certificate: `basic_readiness_compliance_correspondence`

## Official Rocq

```coq
basic_readiness_compliance :
forall {Job : JobType} {PState : ProcessorState Job} {H : JobArrival Job} {H0 : JobCost Job}
  (sched : @schedule Job PState),
@jobs_must_arrive_to_execute Job H PState sched ->
@completed_jobs_dont_execute Job PState sched H0 ->
@jobs_must_be_ready_to_execute Job H PState sched H0 (@basic_ready_instance Job PState H H0)

basic_readiness_compliance is not universe polymorphic
Arguments basic_readiness_compliance {Job PState H H0} sched _ _ j t _
basic_readiness_compliance is opaque
Expands to: Constant prosa.analysis.facts.readiness.basic.basic_readiness_compliance
Declared in library prosa.analysis.facts.readiness.basic, line 39, characters 8-34
@basic_readiness_compliance
     : forall (Job : JobType) (PState : ProcessorState Job) (H : JobArrival Job) 
         (H0 : JobCost Job) (sched : @schedule Job PState),
       @jobs_must_arrive_to_execute Job H PState sched ->
       @completed_jobs_dont_execute Job PState sched H0 ->
       @jobs_must_be_ready_to_execute Job H PState sched H0 (@basic_ready_instance Job PState H H0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_compliance : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    Prosa.Behavior.Ready.completed_jobs_dont_execute sched → Prosa.Behavior.Ready.jobs_must_be_ready_to_execute sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Basic_basic_readiness_compliance
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_8 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_11 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_8 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_11 ->
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job
         inst_3
         inst_8 PState sched
         inst_11
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_8
            inst_11)
```
