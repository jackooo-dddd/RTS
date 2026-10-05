# `contiguously_nps_start`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.transfer_schedulability.criterion.contiguously_nps_start`
- Lean: `Prosa.Results.TransferSchedulability.Criterion.contiguously_nps_start`
- Certificate: `contiguously_nps_start_correspondence`

## Official Rocq

```coq
contiguously_nps_start :
forall {Job : JobType} (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
  (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
  (job_cost_bound : JobCost Job) (t0 t2 : nat),
is_true
  (~~ @contiguously_nps Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0 t2) ->
is_true
  (@contiguously_nps Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0.+1 t2) ->
is_true
  (~~ @nonpositive_slack Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0 t2)

contiguously_nps_start is not universe polymorphic
Arguments contiguously_nps_start {Job} ref_sched online_sched ref_job_cost online_job_cost 
  arr_seq job_cost_bound (t0 t2)%nat_scope _ _
contiguously_nps_start is opaque
Expands to: Constant prosa.results.transfer_schedulability.criterion.contiguously_nps_start
Declared in library prosa.results.transfer_schedulability.criterion, line 686, characters 10-32
@contiguously_nps_start
     : forall (Job : JobType) (ref_sched online_sched : @schedule Job (ideal.processor_state Job))
         (ref_job_cost online_job_cost : JobCost Job) (arr_seq : arrival_sequence Job)
         (job_cost_bound : JobCost Job) (t0 t2 : nat),
       is_true
         (~~
          @contiguously_nps Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0
            t2) ->
       is_true
         (@contiguously_nps Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
            t0.+1 t2) ->
       is_true
         (~~
          @nonpositive_slack Job ref_sched online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
            t0 t2)
```

## Lean

```lean
@Prosa.Results.TransferSchedulability.Criterion.contiguously_nps_start : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job]
  (ref_sched online_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (ref_job_cost online_job_cost : Prosa.Behavior.Job.JobCost Job)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (job_cost_bound : Prosa.Behavior.Job.JobCost Job)
  (t0 t2 : ℕ),
  (!Prosa.Results.TransferSchedulability.Criterion.contiguously_nps ref_sched online_sched ref_job_cost online_job_cost
          arr_seq job_cost_bound t0 t2) =
      true →
    Prosa.Results.TransferSchedulability.Criterion.contiguously_nps ref_sched online_sched ref_job_cost online_job_cost
          arr_seq job_cost_bound (t0 + 1) t2 =
        true →
      (!Prosa.Results.TransferSchedulability.Criterion.nonpositive_slack ref_sched online_sched ref_job_cost
            online_job_cost arr_seq job_cost_bound t0 t2) =
        true
```

## Lean, imported into Rocq

```coq
Prosa_Results_TransferSchedulability_Criterion_contiguously_nps_start
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (ref_sched
          online_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3))
         (ref_job_cost
          online_job_cost : Prosa_Behavior_Job_JobCost Job
                              inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (job_cost_bound : Prosa_Behavior_Job_JobCost Job
                             inst_3)
         (t0 t2 : Nat),
       @eq Bool
         (Bool_not
            (Prosa_Results_TransferSchedulability_Criterion_contiguously_nps Job
               inst_3 ref_sched
               online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0 t2))
         Bool_true ->
       @eq Bool
         (Prosa_Results_TransferSchedulability_Criterion_contiguously_nps Job
            inst_3 ref_sched
            online_sched ref_job_cost online_job_cost arr_seq job_cost_bound
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) t0
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
            t2)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Results_TransferSchedulability_Criterion_nonpositive_slack Job
               inst_3 ref_sched
               online_sched ref_job_cost online_job_cost arr_seq job_cost_bound t0 t2))
         Bool_true
```
