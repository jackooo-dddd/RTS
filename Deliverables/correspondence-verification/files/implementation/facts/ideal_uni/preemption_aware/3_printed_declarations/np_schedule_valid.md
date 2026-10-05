# `np_schedule_valid`

- Kind (Rocq): Theorem
- Rocq: `prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_valid`
- Lean: `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_schedule_valid`
- Certificate: `np_schedule_valid_correspondence`

## Official Rocq

```coq
np_schedule_valid :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job)
  {RM : @JobReady Job (processor_state Job) H H0} {H1 : JobPreemptable Job}
  (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
(forall (t : instant) (s : seq (Equality.sort Job)) (j : Equality.sort Job),
 choose_job t s = @Some (Equality.sort Job) j -> is_true (j \in s)) ->
@nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
@valid_schedule Job H0 (processor_state Job) (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) H RM
  arr_seq

np_schedule_valid is not universe polymorphic
Arguments np_schedule_valid {Job H H0} arr_seq {RM H1} (choose_job H_chooses_from_set)%function_scope
  H_nonclairvoyant_readiness
np_schedule_valid is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.preemption_aware.np_schedule_valid
Declared in library prosa.implementation.facts.ideal_uni.preemption_aware, line 184, characters 12-29
@np_schedule_valid
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (RM : @JobReady Job (processor_state Job) H H0) (H1 : JobPreemptable Job)
         (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
       (forall (t : instant) (s : seq (Equality.sort Job)) (j : Equality.sort Job),
        choose_job t s = @Some (Equality.sort Job) j -> is_true (j \in s)) ->
       @nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
       @valid_schedule Job H0 (processor_state Job) (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) H
         RM arr_seq
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_schedule_valid : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
  [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (choose_job : Prosa.Behavior.Time.instant → List Job → Option Job),
  (∀ (t : Prosa.Behavior.Time.instant) (s : List Job) (j : Job), choose_job t s = some j → decide (j ∈ s) = true) →
    Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
      Prosa.Behavior.Ready.valid_schedule
        (Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule arr_seq choose_job) arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PreemptionAware_np_schedule_valid
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
                      inst_3)
         (RM : Prosa_Behavior_Ready_JobReady_inst4 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3)
                 inst_6
                 inst_9)
         (inst_20 : 
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
       Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM ->
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_3
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
            inst_3
            inst_6
            inst_9 arr_seq
            RM inst_20
            choose_job)
         inst_6 RM arr_seq
```
