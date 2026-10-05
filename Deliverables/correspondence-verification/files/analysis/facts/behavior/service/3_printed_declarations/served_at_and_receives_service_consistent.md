# `served_at_and_receives_service_consistent`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.behavior.service.served_at_and_receives_service_consistent`
- Lean: `Prosa.Analysis.Facts.Behavior.Service.served_at_and_receives_service_consistent`
- Certificate: `served_at_and_receives_service_consistent_correspondence`

## Official Rocq

```coq
served_at_and_receives_service_consistent :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
is_true (j \in @served_jobs_at Job PState arr_seq sched t) ->
is_true (@receives_service_at Job PState sched j t)

served_at_and_receives_service_consistent is not universe polymorphic
Arguments served_at_and_receives_service_consistent {Job PState} arr_seq sched j t _
served_at_and_receives_service_consistent is opaque
Expands to: Constant prosa.analysis.facts.behavior.service.served_at_and_receives_service_consistent
Declared in library prosa.analysis.facts.behavior.service, line 679, characters 8-49
@served_at_and_receives_service_consistent
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (j : Equality.sort Job) (t : instant),
       is_true (j \in @served_jobs_at Job PState arr_seq sched t) ->
       is_true (@receives_service_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Service.served_at_and_receives_service_consistent : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
  (j : Job) (t : Prosa.Behavior.Time.instant),
  decide (j ∈ Prosa.Analysis.Definitions.Service.served_jobs_at arr_seq sched t) = true →
    Prosa.Behavior.Service.receives_service_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Service_served_at_and_receives_service_consistent
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Analysis_Definitions_Service_served_jobs_at Job
                  inst_3 PState arr_seq
                  sched t)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_3)
               (instLawfulBEq Job inst_3)
               j
               (Prosa_Analysis_Definitions_Service_served_jobs_at Job
                  inst_3 PState arr_seq
                  sched t)))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at Job
            inst_3 PState sched j t)
         Bool_true
```
