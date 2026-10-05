# `no_ahep_interference_when_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.no_ahep_interference_when_scheduled`
- Lean: `Prosa.Analysis.Facts.Interference.no_ahep_interference_when_scheduled`
- Certificate: `no_ahep_interference_when_scheduled_correspondence`

## Official Rocq

```coq
no_ahep_interference_when_scheduled :
forall {Job : JobType} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {JLFP : JLFP_policy Job}
  (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job PState sched j t) ->
is_true (~~ @another_hep_job_interference Job PState arr_seq sched JLFP j t)

no_ahep_interference_when_scheduled is not universe polymorphic
Arguments no_ahep_interference_when_scheduled {Job PState} H_uniprocessor_proc_model 
  arr_seq sched {JLFP} j t H_j_sched
no_ahep_interference_when_scheduled is opaque
Expands to: Constant prosa.analysis.facts.interference.no_ahep_interference_when_scheduled
Declared in library prosa.analysis.facts.interference, line 271, characters 12-47
@no_ahep_interference_when_scheduled
     : forall (Job : JobType) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job)
         (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job PState sched j t) ->
       is_true (~~ @another_hep_job_interference Job PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.no_ahep_interference_when_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job) (t : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j t = true →
        (!Prosa.Analysis.Definitions.Interference.another_hep_job_interference arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_no_ahep_interference_when_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Interference_another_hep_job_interference Job
               inst_3 PState arr_seq sched
               JLFP j t))
         Bool_true
```
