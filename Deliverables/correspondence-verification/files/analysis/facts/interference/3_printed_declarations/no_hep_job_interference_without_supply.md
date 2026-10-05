# `no_hep_job_interference_without_supply`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.interference.no_hep_job_interference_without_supply`
- Lean: `Prosa.Analysis.Facts.Interference.no_hep_job_interference_without_supply`
- Certificate: `no_hep_job_interference_without_supply_correspondence`

## Official Rocq

```coq
no_hep_job_interference_without_supply :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) {JLFP : JLFP_policy Job} (t : instant),
is_true (~~ @has_supply Job PState sched t) ->
forall j : Equality.sort Job, is_true (~~ @another_hep_job_interference Job PState arr_seq sched JLFP j t)

no_hep_job_interference_without_supply is not universe polymorphic
Arguments no_hep_job_interference_without_supply {Job PState} arr_seq sched {JLFP} t H_no_supply j
no_hep_job_interference_without_supply is opaque
Expands to: Constant prosa.analysis.facts.interference.no_hep_job_interference_without_supply
Declared in library prosa.analysis.facts.interference, line 149, characters 10-48
@no_hep_job_interference_without_supply
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (JLFP : JLFP_policy Job) (t : instant),
       is_true (~~ @has_supply Job PState sched t) ->
       forall j : Equality.sort Job,
       is_true (~~ @another_hep_job_interference Job PState arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Interference.no_hep_job_interference_without_supply : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job) (t : Prosa.Behavior.Time.instant),
  (!Prosa.Model.Processor.Supply.has_supply sched t) = true →
    ∀ (j : Job), (!Prosa.Analysis.Definitions.Interference.another_hep_job_interference arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Interference_no_hep_job_interference_without_supply
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Model_Processor_Supply_has_supply Job
               inst_3 PState sched t))
         Bool_true ->
       forall j : Job,
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_Interference_another_hep_job_interference Job
               inst_3 PState arr_seq sched
               JLFP j t))
         Bool_true
```
