# `valid_fully_preemptive_model`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.preemptive.valid_fully_preemptive_model`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Preemptive.valid_fully_preemptive_model`
- Certificate: `valid_fully_preemptive_model_correspondence`

## Official Rocq

```coq
valid_fully_preemptive_model :
forall {Job : JobType} {H0 : JobCost Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState),
@valid_preemption_model Job H0 (@fully_preemptive_job_model Job) PState arr_seq sched

valid_fully_preemptive_model is not universe polymorphic
Arguments valid_fully_preemptive_model {Job H0 PState} arr_seq sched j _
valid_fully_preemptive_model is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.preemptive.valid_fully_preemptive_model
Declared in library prosa.analysis.facts.preemption.job.preemptive, line 28, characters 8-36
@valid_fully_preemptive_model
     : forall (Job : JobType) (H0 : JobCost Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @valid_preemption_model Job H0 (@fully_preemptive_job_model Job) PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Preemptive.valid_fully_preemptive_model : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Preemptive_valid_fully_preemptive_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState),
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_6
         (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
            inst_3)
         PState arr_seq sched
```
