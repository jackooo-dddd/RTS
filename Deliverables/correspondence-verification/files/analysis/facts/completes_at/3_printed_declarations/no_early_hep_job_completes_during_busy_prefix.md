# `no_early_hep_job_completes_during_busy_prefix`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.completes_at.no_early_hep_job_completes_during_busy_prefix`
- Lean: `Prosa.Analysis.Facts.CompletesAt.no_early_hep_job_completes_during_busy_prefix`
- Certificate: `no_early_hep_job_completes_during_busy_prefix_correspondence`

## Official Rocq

```coq
no_early_hep_job_completes_during_busy_prefix :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JLFP_policy Job}
  {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall (sched : @schedule Job PState) (j : Equality.sort Job) (t t1 t2 : instant),
@busy_interval_prefix Job H H0 PState arr_seq sched H1 j t1 t2 ->
is_true (t1 < t <= t2) ->
forall jhp : Equality.sort Job,
is_true (jhp \in @arrivals_before Job arr_seq t1) ->
is_true (@hep_job Job H1 jhp j) -> is_true (~~ @completes_at Job PState sched H0 jhp t)

no_early_hep_job_completes_during_busy_prefix is not universe polymorphic
Arguments no_early_hep_job_completes_during_busy_prefix {Job H H0 H1 PState} arr_seq 
  H_valid_arrival_sequence sched j t t1 t2 _ _ jhp _ _
no_early_hep_job_completes_during_busy_prefix is opaque
Expands to: Constant prosa.analysis.facts.completes_at.no_early_hep_job_completes_during_busy_prefix
Declared in library prosa.analysis.facts.completes_at, line 104, characters 8-53
@no_early_hep_job_completes_during_busy_prefix
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JLFP_policy Job)
         (PState : ProcessorState Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall (sched : @schedule Job PState) (j : Equality.sort Job) (t t1 t2 : instant),
       @busy_interval_prefix Job H H0 PState arr_seq sched H1 j t1 t2 ->
       is_true (t1 < t <= t2) ->
       forall jhp : Equality.sort Job,
       is_true (jhp \in @arrivals_before Job arr_seq t1) ->
       is_true (@hep_job Job H1 jhp j) -> is_true (~~ @completes_at Job PState sched H0 jhp t)
```

## Lean

```lean
@Prosa.Analysis.Facts.CompletesAt.no_early_hep_job_completes_during_busy_prefix : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Model.Priority.Definitions.JLFP_policy Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job) (t t1 t2 : Prosa.Behavior.Time.instant),
      Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
        (decide (t1 < t) && decide (t ≤ t2)) = true →
          ∀ (jhp : Job),
            decide (jhp ∈ Prosa.Behavior.Arrival_sequence.arrivals_before arr_seq t1) = true →
              Prosa.Model.Priority.Definitions.hep_job jhp j = true →
                (!Prosa.Behavior.Service.completes_at sched jhp t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_CompletesAt_no_early_hep_job_completes_during_busy_prefix
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job inst_3)
         (inst_12 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job) (t t1 t2 : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched
         inst_12 j t1 t2 ->
       @eq Bool
         (Bool_and
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t2) (Nat_decLe t t2)))
         Bool_true ->
       forall jhp : Job,
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Behavior_Arrival_sequence_arrivals_before Job
                  inst_3 arr_seq t1)
               jhp)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job inst_3)
               (instLawfulBEq Job inst_3) jhp
               (Prosa_Behavior_Arrival_sequence_arrivals_before Job
                  inst_3 arr_seq t1)))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
            inst_3
            inst_12 jhp j)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completes_at Job
               inst_3 PState sched
               inst_9 jhp t))
         Bool_true
```
