# `swapped_jobs_come_from_arrival_sequence`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.swaps.swapped_jobs_come_from_arrival_sequence`
- Lean: `Prosa.Analysis.Facts.Transform.Swaps.swapped_jobs_come_from_arrival_sequence`
- Certificate: `swapped_jobs_come_from_arrival_sequence_correspondence`

## Official Rocq

```coq
swapped_jobs_come_from_arrival_sequence :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t1 t2 : instant) (arr_seq : arrival_sequence Job),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_come_from_arrival_sequence Job PState (@swapped Job PState sched t1 t2) arr_seq

swapped_jobs_come_from_arrival_sequence is not universe polymorphic
Arguments swapped_jobs_come_from_arrival_sequence {Job PState} sched t1 t2 arr_seq H_from_arr_seq j t _
swapped_jobs_come_from_arrival_sequence is opaque
Expands to: Constant prosa.analysis.facts.transform.swaps.swapped_jobs_come_from_arrival_sequence
Declared in library prosa.analysis.facts.transform.swaps, line 336, characters 8-47
@swapped_jobs_come_from_arrival_sequence
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t1 t2 : instant) (arr_seq : arrival_sequence Job),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_come_from_arrival_sequence Job PState (@swapped Job PState sched t1 t2) arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.Swaps.swapped_jobs_come_from_arrival_sequence : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : Prosa.Behavior.Time.instant)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
    Prosa.Behavior.Ready.jobs_come_from_arrival_sequence (Prosa.Analysis.Transform.Swap.swapped sched t1 t2) arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_Swaps_swapped_jobs_come_from_arrival_sequence
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Prosa_Behavior_Time_instant)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState
         (Prosa_Analysis_Transform_Swap_swapped Job
            inst_3 PState sched t1 t2)
         arr_seq
```
