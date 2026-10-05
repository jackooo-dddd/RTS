# `scheduled_job_at_neq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.uniprocessor.scheduled_job_at_neq`
- Lean: `Prosa.Analysis.Facts.Model.Uniprocessor.scheduled_job_at_neq`
- Certificate: `scheduled_job_at_neq_statement_correspondence`

## Official Rocq

```coq
scheduled_job_at_neq :
forall {Job : JobType} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) (j j' : Equality.sort Job) (t : instant),
is_true (j != j') ->
is_true (@scheduled_at Job PState sched j t) -> is_true (~~ @scheduled_at Job PState sched j' t)

scheduled_job_at_neq is not universe polymorphic
Arguments scheduled_job_at_neq {Job PState} H_uni sched j j' t _ _
scheduled_job_at_neq is opaque
Expands to: Constant prosa.analysis.facts.model.uniprocessor.scheduled_job_at_neq
Declared in library prosa.analysis.facts.model.uniprocessor, line 19, characters 8-28
@scheduled_job_at_neq
     : forall (Job : JobType) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (j j' : Equality.sort Job) (t : instant),
       is_true (j != j') ->
       is_true (@scheduled_at Job PState sched j t) -> is_true (~~ @scheduled_at Job PState sched j' t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Uniprocessor.scheduled_job_at_neq : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j j' : Job) (t : Prosa.Behavior.Time.instant),
      decide (j ≠ j') = true →
        Prosa.Behavior.Service.scheduled_at sched j t = true → (!Prosa.Behavior.Service.scheduled_at sched j' t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Uniprocessor_scheduled_job_at_neq
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j j' : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide (Ne Job j j')
            (instDecidableNot (@eq Job j j')
               (inst_3 j j')))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched j' t))
         Bool_true
```
