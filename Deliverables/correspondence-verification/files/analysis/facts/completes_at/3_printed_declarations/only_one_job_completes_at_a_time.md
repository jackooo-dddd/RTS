# `only_one_job_completes_at_a_time`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.completes_at.only_one_job_completes_at_a_time`
- Lean: `Prosa.Analysis.Facts.CompletesAt.only_one_job_completes_at_a_time`
- Certificate: `only_one_job_completes_at_a_time_correspondence`

## Official Rocq

```coq
only_one_job_completes_at_a_time :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H arr_seq ->
forall (sched : @schedule Job PState) (P : pred (Equality.sort Job)) (t B : instant),
is_true (0 < t) ->
is_true
  (\sum_(j <- @arrivals_before Job arr_seq B | P j) nat_of_bool (@completes_at Job PState sched H0 j t) <= 1)

only_one_job_completes_at_a_time is not universe polymorphic
Arguments only_one_job_completes_at_a_time {Job H H0 PState} H_uniprocessor_proc_model 
  arr_seq H_valid_arrival_sequence sched P t B _
only_one_job_completes_at_a_time is opaque
Expands to: Constant prosa.analysis.facts.completes_at.only_one_job_completes_at_a_time
Declared in library prosa.analysis.facts.completes_at, line 64, characters 8-40
@only_one_job_completes_at_a_time
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H arr_seq ->
       forall (sched : @schedule Job PState) (P : pred (Equality.sort Job)) (t B : instant),
       is_true (0 < t) ->
       is_true
         (\sum_(j <- @arrivals_before Job arr_seq B | P j)
             nat_of_bool (@completes_at Job PState sched H0 j t) <=
          1)
```

## Lean

```lean
@Prosa.Analysis.Facts.CompletesAt.only_one_job_completes_at_a_time : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (P : Job → Bool) (t B : Prosa.Behavior.Time.instant),
          0 < t →
            (Prosa.Util.Sum.sumFiltered (Prosa.Behavior.Arrival_sequence.arrivals_before arr_seq B) P fun j =>
                (Prosa.Behavior.Service.completes_at sched j t).toNat) ≤
              1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_CompletesAt_only_one_job_completes_at_a_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (P : Job -> Bool) (t B : Prosa_Behavior_Time_instant),
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t ->
       LE_le_inst1 Nat instLENat
         (Prosa_Util_Sum_sumFiltered Job
            (Prosa_Behavior_Arrival_sequence_arrivals_before Job
               inst_3 arr_seq B)
            P
            (fun j : Job =>
             Bool_toNat
               (Prosa_Behavior_Service_completes_at Job
                  inst_3 PState sched
                  inst_9 j t)))
         (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
```
