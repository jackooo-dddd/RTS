# `chosen_job_is_ready`

- Kind (Rocq): Theorem
- Rocq: `prosa.implementation.facts.ideal_uni.preemption_aware.chosen_job_is_ready`
- Lean: `Prosa.Implementation.Facts.IdealUni.PreemptionAware.chosen_job_is_ready`
- Certificate: `chosen_job_is_ready_correspondence`

## Official Rocq

```coq
chosen_job_is_ready :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job)
  {RM : @JobReady Job (processor_state Job) H H0} {H1 : JobPreemptable Job}
  (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
(forall (t : instant) (s : seq (Equality.sort Job)) (j : Equality.sort Job),
 choose_job t s = @Some (Equality.sort Job) j -> is_true (j \in s)) ->
@nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
forall (j : Equality.sort Job) (t : instant),
is_true
  (choose_job t
     (@jobs_backlogged_at Job H0 H (processor_state Job) RM arr_seq
        ((fun t0 : nat =>
          match t0 with
          | 0 => @empty_schedule Job (processor_state Job) (@None (Equality.sort Job))
          | t'.+1 =>
              @schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
                (@None (Equality.sort Job)) t'
          end) t)
        t) ==
   @Some (Equality.sort Job) j) ->
is_true
  (@job_ready Job (processor_state Job) H H0 RM (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) j t)

chosen_job_is_ready is not universe polymorphic
Arguments chosen_job_is_ready {Job H H0} arr_seq {RM H1} (choose_job H_chooses_from_set)%function_scope
  H_nonclairvoyant_readiness j t _
chosen_job_is_ready is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.preemption_aware.chosen_job_is_ready
Declared in library prosa.implementation.facts.ideal_uni.preemption_aware, line 150, characters 12-31
@chosen_job_is_ready
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (RM : @JobReady Job (processor_state Job) H H0) (H1 : JobPreemptable Job)
         (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
       (forall (t : instant) (s : seq (Equality.sort Job)) (j : Equality.sort Job),
        choose_job t s = @Some (Equality.sort Job) j -> is_true (j \in s)) ->
       @nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
       forall (j : Equality.sort Job) (t : instant),
       is_true
         (choose_job t
            (@jobs_backlogged_at Job H0 H (processor_state Job) RM arr_seq
               match t with
               | 0 => @empty_schedule Job (processor_state Job) (@None (Equality.sort Job))
               | t'.+1 =>
                   @schedule_up_to Job (processor_state Job)
                     (@allocation_at Job H H0 arr_seq RM H1 choose_job) (@None (Equality.sort Job)) t'
               end t) ==
          @Some (Equality.sort Job) j) ->
       is_true
         (@job_ready Job (processor_state Job) H H0 RM (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job)
            j t)
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PreemptionAware.chosen_job_is_ready : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
  [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (choose_job : Prosa.Behavior.Time.instant → List Job → Option Job),
  (∀ (t : Prosa.Behavior.Time.instant) (s : List Job) (j : Job), choose_job t s = some j → decide (j ∈ s) = true) →
    Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
      ∀ (j : Job) (t : Prosa.Behavior.Time.instant),
        decide
              (choose_job t
                  (Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq
                    (match t with
                    | 0 => Prosa.Implementation.Definitions.GenericScheduler.empty_schedule none
                    | Nat.succ t' =>
                      Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to
                        (Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at arr_seq choose_job) none t')
                    t) =
                some j) =
            true →
          Prosa.Behavior.Ready.job_ready
              (Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule arr_seq choose_job) j t =
            true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PreemptionAware_chosen_job_is_ready
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
       forall (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (@eq (Option Job)
               (choose_job t
                  (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst4 Job
                     inst_3
                     inst_9
                     inst_6
                     (Prosa_Model_Processor_Ideal_processor_state Job
                        inst_3)
                     RM arr_seq
                     (_private_Prosa_Implementation_Facts_IdealUni_PreemptionAware0_Prosa_Implementation_Facts_IdealUni_PreemptionAware_pmc_eq_match_1
                        (fun _ : Prosa_Behavior_Time_instant =>
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
                        (fun t' : Prosa_Behavior_Time_instant =>
                         Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst2 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3)
                           (Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
                              inst_3
                              inst_6
                              inst_9
                              arr_seq RM
                              inst_20
                              choose_job)
                           (Option_none Job) t'))
                     t))
               (Option_some Job j))
            (Option_instDecidableEq Job
               inst_3
               (choose_job t
                  (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst4 Job
                     inst_3
                     inst_9
                     inst_6
                     (Prosa_Model_Processor_Ideal_processor_state Job
                        inst_3)
                     RM arr_seq
                     (_private_Prosa_Implementation_Facts_IdealUni_PreemptionAware0_Prosa_Implementation_Facts_IdealUni_PreemptionAware_pmc_eq_match_1
                        (fun _ : Prosa_Behavior_Time_instant =>
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
                        (fun t' : Prosa_Behavior_Time_instant =>
                         Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst2 Job
                           inst_3
                           (Prosa_Model_Processor_Ideal_processor_state Job
                              inst_3)
                           (Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
                              inst_3
                              inst_6
                              inst_9
                              arr_seq RM
                              inst_20
                              choose_job)
                           (Option_none Job) t'))
                     t))
               (Option_some Job j)))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Ready_JobReady_job_ready_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_6
            inst_9 RM
            (Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
               inst_3
               inst_6
               inst_9
               arr_seq RM
               inst_20
               choose_job)
            j t)
         Bool_true
```
