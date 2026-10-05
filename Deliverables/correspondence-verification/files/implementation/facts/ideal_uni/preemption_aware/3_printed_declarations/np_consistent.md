# `np_consistent`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.ideal_uni.preemption_aware.np_consistent`
- Lean: `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_consistent`
- Certificate: `np_consistent_correspondence`

## Official Rocq

```coq
np_consistent :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall {RM : @JobReady Job (processor_state Job) H H0},
@nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
forall {H1 : JobPreemptable Job}
  (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
(forall (t : instant) (s : seq (Equality.sort Job)) (j : Equality.sort Job),
 choose_job t s = @Some (Equality.sort Job) j -> is_true (j \in s)) ->
forall t : nat,
is_true
  (@prev_job_nonpreemptive Job H H0 RM H1
     ((fun t0 : nat =>
       match t0 with
       | 0 => @empty_schedule Job (processor_state Job) (@None (Equality.sort Job))
       | t'.+1 =>
           @schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
             (@None (Equality.sort Job)) t'
       end) t)
     t) ->
is_true
  (~~
   @preemption_time Job H1 arr_seq (processor_state Job)
     (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) t)

np_consistent is not universe polymorphic
Arguments np_consistent {Job H H0} arr_seq H_valid_arrivals {RM} H_nonclairvoyant_job_readiness 
  {H1} (choose_job H_chooses_from_set)%function_scope t%nat_scope _
np_consistent is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.preemption_aware.np_consistent
Declared in library prosa.implementation.facts.ideal_uni.preemption_aware, line 222, characters 10-23
@np_consistent
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall RM : @JobReady Job (processor_state Job) H H0,
       @nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
       forall (H1 : JobPreemptable Job)
         (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
       (forall (t : instant) (s : seq (Equality.sort Job)) (j : Equality.sort Job),
        choose_job t s = @Some (Equality.sort Job) j -> is_true (j \in s)) ->
       forall t : nat,
       is_true
         (@prev_job_nonpreemptive Job H H0 RM H1
            match t with
            | 0 => @empty_schedule Job (processor_state Job) (@None (Equality.sort Job))
            | t'.+1 =>
                @schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
                  (@None (Equality.sort Job)) t'
            end t) ->
       is_true
         (~~
          @preemption_time Job H1 arr_seq (processor_state Job)
            (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) t)
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_consistent : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
      Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
        ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
          (choose_job : Prosa.Behavior.Time.instant → List Job → Option Job),
          (∀ (t : Prosa.Behavior.Time.instant) (s : List Job) (j : Job),
              choose_job t s = some j → decide (j ∈ s) = true) →
            ∀ (t : ℕ),
              Prosa.Implementation.Definitions.IdealUniScheduler.prev_job_nonpreemptive
                    (match t with
                    | 0 => Prosa.Implementation.Definitions.GenericScheduler.empty_schedule none
                    | t'.succ =>
                      Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to
                        (Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at arr_seq choose_job) none t')
                    t =
                  true →
                (!Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq
                      (Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule arr_seq choose_job) t) =
                  true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PreemptionAware_np_consistent
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_9 arr_seq ->
       forall
         RM : Prosa_Behavior_Ready_JobReady_inst4 Job
                inst_3
                (Prosa_Model_Processor_Ideal_processor_state Job
                   inst_3)
                inst_6
                inst_9,
       Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM ->
       forall
         (inst_30 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (choose_job : Prosa_Behavior_Time_instant -> List Job -> Option Job),
       (forall (t : Prosa_Behavior_Time_instant) (s : List Job) (j : Job),
        @eq (Option Job) (choose_job t s) (Option_some Job j) ->
        @eq Bool
          (Decidable_decide (Membership_mem Job (List Job) (List_instMembership Job) s j)
             (List_instDecidableMemOfLawfulBEq Job
                (instBEqOfDecidableEq Job
                   inst_3)
                (instLawfulBEq Job
                   inst_3)
                j s))
          Bool_true) ->
       forall t : Nat,
       @eq Bool
         (Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive Job
            inst_3
            inst_6
            inst_9 RM
            inst_30
            (Prosa_Implementation_Facts_IdealUni_PreemptionAware_np_job_remains_scheduled_match_1
               (fun _ : Nat =>
                Prosa_Behavior_Schedule_schedule_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3))
               t
               (fun _ : Unit =>
                Prosa_Implementation_Definitions_GenericScheduler_empty_schedule_inst2 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  (Option_none Job))
               (fun t' : Nat =>
                Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst2 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  (Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
                     inst_3
                     inst_6
                     inst_9
                     arr_seq RM
                     inst_30
                     choose_job)
                  (Option_none Job) t'))
            t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Schedule_PreemptionTime_preemption_time_inst4 Job
               inst_3
               inst_30
               arr_seq
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               (Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
                  inst_3
                  inst_6
                  inst_9
                  arr_seq RM
                  inst_30
                  choose_job)
               t))
         Bool_true
```
