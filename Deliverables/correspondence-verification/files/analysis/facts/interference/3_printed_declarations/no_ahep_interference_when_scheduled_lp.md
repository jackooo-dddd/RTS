# `no_ahep_interference_when_scheduled_lp`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.no_ahep_interference_when_scheduled_lp`
- Lean: `Prosa.Analysis.Facts.Interference.no_ahep_interference_when_scheduled_lp`
- Certificate: `no_ahep_interference_when_scheduled_lp_correspondence`

## Official Rocq

```coq
no_ahep_interference_when_scheduled_lp :
forall {Job : JobType} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) {JLFP : JLFP_policy Job}
  (j : Equality.sort Job) (t : instant) (j' : Equality.sort Job),
is_true (@scheduled_at Job PState sched j' t) ->
is_true (~~ @hep_job Job JLFP j' j) ->
is_true (~~ @another_hep_job_interference Job PState arr_seq sched JLFP j t)

no_ahep_interference_when_scheduled_lp is not universe polymorphic
Arguments no_ahep_interference_when_scheduled_lp {Job PState} H_uniprocessor_proc_model 
  arr_seq sched {JLFP} j t j' H_j'_sched H_j'_lp
no_ahep_interference_when_scheduled_lp is opaque
Expands to: Constant prosa.analysis.facts.interference.no_ahep_interference_when_scheduled_lp
Declared in library prosa.analysis.facts.interference, line 377, characters 12-50
@no_ahep_interference_when_scheduled_lp
     : forall (Job : JobType) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job)
         (j : Equality.sort Job) (t : instant) (j' : Equality.sort Job),
       is_true (@scheduled_at Job PState sched j' t) ->
       is_true (~~ @hep_job Job JLFP j' j) ->
       is_true (~~ @another_hep_job_interference Job PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.no_ahep_interference_when_scheduled_lp : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (j : Job) (t : Prosa.Behavior.Time.instant) (j' : Job),
      Prosa.Behavior.Service.scheduled_at sched j' t = true →
        (!Prosa.Model.Priority.Definitions.hep_job j' j) = true →
          (!Prosa.Analysis.Definitions.Interference.another_hep_job_interference arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_no_ahep_interference_when_scheduled_lp
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
         (j : Job) (t : Prosa_Behavior_Time_instant) (j' : Job),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j' t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
               inst_3 JLFP j' j))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Interference_another_hep_job_interference Job
               inst_3 PState arr_seq sched
               JLFP j t))
         Bool_true
```
