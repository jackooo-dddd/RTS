# `np_respects_preemption_model`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.ideal_uni.preemption_aware.np_respects_preemption_model`
- Lean: `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_respects_preemption_model`
- Certificate: `np_respects_preemption_model_correspondence`

## Official Rocq

```coq
np_respects_preemption_model :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job)
  {RM : @JobReady Job (processor_state Job) H H0},
@nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
forall {H1 : JobPreemptable Job}
  (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
(forall j : Equality.sort Job,
 @arrives_in Job arr_seq j -> is_true (@job_cannot_become_nonpreemptive_before_execution Job H1 j)) ->
@valid_nonpreemptive_readiness Job H H0 (processor_state Job) RM H1
  (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) ->
@schedule_respects_preemption_model Job (processor_state Job) H1 arr_seq
  (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job)

np_respects_preemption_model is not universe polymorphic
Arguments np_respects_preemption_model {Job H H0} arr_seq {RM} H_nonclairvoyant_job_readiness 
  {H1} (choose_job H_valid_preemption_function)%function_scope H_valid_preemption_behavior 
  j t _ _
np_respects_preemption_model is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.preemption_aware.np_respects_preemption_model
Declared in library prosa.implementation.facts.ideal_uni.preemption_aware, line 266, characters 10-38
@np_respects_preemption_model
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (RM : @JobReady Job (processor_state Job) H H0),
       @nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
       forall (H1 : JobPreemptable Job)
         (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
       (forall j : Equality.sort Job,
        @arrives_in Job arr_seq j -> is_true (@job_cannot_become_nonpreemptive_before_execution Job H1 j)) ->
       @valid_nonpreemptive_readiness Job H H0 (processor_state Job) RM H1
         (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) ->
       @schedule_respects_preemption_model Job (processor_state Job) H1 arr_seq
         (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job)
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_respects_preemption_model : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
  Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
    ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
      (choose_job : Prosa.Behavior.Time.instant → List Job → Option Job),
      (∀ (j : Job),
          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
            Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution j = true) →
        Prosa.Analysis.Definitions.Readiness.valid_nonpreemptive_readiness RM
            (Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule arr_seq choose_job) →
          Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq
            (Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule arr_seq choose_job)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PreemptionAware_np_respects_preemption_model
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
                 inst_9),
       Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM ->
       forall
         (inst_25 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (choose_job : Prosa_Behavior_Time_instant -> List Job -> Option Job),
       (forall j : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_3 arr_seq j ->
        @eq Bool
          (Prosa_Model_Preemption_Parameter_job_cannot_become_nonpreemptive_before_execution Job
             inst_3
             inst_25 j)
          Bool_true) ->
       Prosa_Analysis_Definitions_Readiness_valid_nonpreemptive_readiness_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM inst_25
         (Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
            inst_3
            inst_6
            inst_9 arr_seq
            RM inst_25
            choose_job) ->
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         inst_25 arr_seq
         (Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
            inst_3
            inst_6
            inst_9 arr_seq
            RM inst_25
            choose_job)
```
