# `valid_fully_nonpreemptive_model`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.job.nonpreemptive.valid_fully_nonpreemptive_model`
- Lean: `Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.valid_fully_nonpreemptive_model`
- Certificate: `valid_fully_nonpreemptive_model_correspondence`

## Official Rocq

```coq
valid_fully_nonpreemptive_model :
forall {Job : JobType} {H0 : JobCost Job} (arr_seq : arrival_sequence Job) {PState : ProcessorState Job},
@unit_service_proc_model Job PState ->
forall sched : @schedule Job PState,
@nonpreemptive_schedule Job H0 PState sched ->
@completed_jobs_dont_execute Job PState sched H0 ->
@valid_preemption_model Job H0 (@fully_nonpreemptive_job_model Job H0) PState arr_seq sched

valid_fully_nonpreemptive_model is not universe polymorphic
Arguments valid_fully_nonpreemptive_model {Job H0} arr_seq {PState} H_unit_service 
  sched H_nonpreemptive_sched H_completed_jobs_dont_execute j _
valid_fully_nonpreemptive_model is opaque
Expands to: Constant prosa.analysis.facts.preemption.job.nonpreemptive.valid_fully_nonpreemptive_model
Declared in library prosa.analysis.facts.preemption.job.nonpreemptive, line 37, characters 8-39
@valid_fully_nonpreemptive_model
     : forall (Job : JobType) (H0 : JobCost Job) (arr_seq : arrival_sequence Job)
         (PState : ProcessorState Job),
       @unit_service_proc_model Job PState ->
       forall sched : @schedule Job PState,
       @nonpreemptive_schedule Job H0 PState sched ->
       @completed_jobs_dont_execute Job PState sched H0 ->
       @valid_preemption_model Job H0 (@fully_nonpreemptive_job_model Job H0) PState arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive.valid_fully_nonpreemptive_model : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule sched →
        Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
          Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_Job_Nonpreemptive_valid_fully_nonpreemptive_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3
                   PState,
       Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule Job
         inst_3
         inst_6 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_6 ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_6
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
            inst_3
            inst_6)
         PState arr_seq sched
```
