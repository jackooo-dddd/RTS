# `no_preemptions_equiv_nonpreemptive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.nonpreemptive.no_preemptions_equiv_nonpreemptive`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.no_preemptions_equiv_nonpreemptive`
- Certificate: `no_preemptions_equiv_nonpreemptive_correspondence`

## Official Rocq

```coq
no_preemptions_equiv_nonpreemptive :
forall {Job : JobType} {H0 : JobCost Job} {PState : ProcessorState Job} (sched : @schedule Job PState),
(forall (j : Equality.sort Job) (t : instant), is_true (~~ @preempted_at Job H0 PState sched j t)) <->
@nonpreemptive_schedule Job H0 PState sched

no_preemptions_equiv_nonpreemptive is not universe polymorphic
Arguments no_preemptions_equiv_nonpreemptive {Job H0 PState} sched
no_preemptions_equiv_nonpreemptive is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.nonpreemptive.no_preemptions_equiv_nonpreemptive
Declared in library prosa.analysis.facts.preemption.job.nonpreemptive, line 134, characters 8-42
@no_preemptions_equiv_nonpreemptive
     : forall (Job : JobType) (H0 : JobCost Job) (PState : ProcessorState Job) (sched : @schedule Job PState),
       (forall (j : Equality.sort Job) (t : instant), is_true (~~ @preempted_at Job H0 PState sched j t)) <->
       @nonpreemptive_schedule Job H0 PState sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.no_preemptions_equiv_nonpreemptive : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
  (∀ (j : Job) (t : Prosa.Behavior.Time.instant), (!Prosa.Model.Preemption.Parameter.preempted_at sched j t) = true) ↔
    Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Nonpreemptive_no_preemptions_equiv_nonpreemptive
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState),
       Iff
         (forall (j : Job) (t : Prosa_Behavior_Time_instant),
          @eq Bool
            (Bool_not
               (Prosa_Model_Preemption_Parameter_preempted_at Job
                  inst_3
                  inst_6
                  PState sched j t))
            Bool_true)
         (Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule Job
            inst_3
            inst_6 PState
            sched)
```
