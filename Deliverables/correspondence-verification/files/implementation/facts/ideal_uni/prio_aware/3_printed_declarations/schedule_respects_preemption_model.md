# `schedule_respects_preemption_model`

- Kind (Rocq): Corollary
- Rocq: `prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_preemption_model`
- Lean: `Prosa.Implementation.Facts.IdealUni.PrioAware.schedule_respects_preemption_model`
- Certificate: `schedule_respects_preemption_model_correspondence`

## Official Rocq

```coq
schedule_respects_preemption_model :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job} (arr_seq : arrival_sequence Job)
  {RM : @JobReady Job (processor_state Job) JC JA},
@nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
forall {H : JobPreemptable Job} {JLDP : JLDP_policy Job},
@valid_nonpreemptive_readiness Job JC JA (processor_state Job) RM H
  (@uni_schedule Job JC JA arr_seq RM H JLDP) ->
(forall j : Equality.sort Job,
 @arrives_in Job arr_seq j -> is_true (@job_cannot_become_nonpreemptive_before_execution Job H j)) ->
@limited_preemptive.schedule_respects_preemption_model Job (processor_state Job) H arr_seq
  (@uni_schedule Job JC JA arr_seq RM H JLDP)

schedule_respects_preemption_model is not universe polymorphic
Arguments schedule_respects_preemption_model {Job JC JA} arr_seq {RM} H_nonclairvoyant_job_readiness 
  {H JLDP} H_valid_preemption_behavior H_valid_preemption_function%function_scope 
  j t _ _
schedule_respects_preemption_model is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_preemption_model
Declared in library prosa.implementation.facts.ideal_uni.prio_aware, line 77, characters 14-48
@schedule_respects_preemption_model
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) (arr_seq : arrival_sequence Job)
         (RM : @JobReady Job (processor_state Job) JC JA),
       @nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
       forall (H : JobPreemptable Job) (JLDP : JLDP_policy Job),
       @valid_nonpreemptive_readiness Job JC JA (processor_state Job) RM H
         (@uni_schedule Job JC JA arr_seq RM H JLDP) ->
       (forall j : Equality.sort Job,
        @arrives_in Job arr_seq j -> is_true (@job_cannot_become_nonpreemptive_before_execution Job H j)) ->
       @limited_preemptive.schedule_respects_preemption_model Job (processor_state Job) H arr_seq
         (@uni_schedule Job JC JA arr_seq RM H JLDP)
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PrioAware.schedule_respects_preemption_model : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [JC : Prosa.Behavior.Job.JobCost Job] [JA : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
  Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
    ∀ [inst_1 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
      [JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job],
      Prosa.Analysis.Definitions.Readiness.valid_nonpreemptive_readiness RM
          (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq) →
        (∀ (j : Job),
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
              Prosa.Model.Preemption.Parameter.job_cannot_become_nonpreemptive_before_execution j = true) →
          Prosa.Model.Schedule.LimitedPreemptive.schedule_respects_preemption_model arr_seq
            (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PrioAware_schedule_respects_preemption_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (JC : Prosa_Behavior_Job_JobCost Job
                 inst_3)
         (JA : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (RM : Prosa_Behavior_Ready_JobReady_inst4 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3)
                 JC JA),
       Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness_inst4 Job
         inst_3 JC JA
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM ->
       forall
         (inst_23 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
                   inst_3),
       Prosa_Analysis_Definitions_Readiness_valid_nonpreemptive_readiness_inst4 Job
         inst_3 JC JA
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM inst_23
         (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job
            inst_3 JC JA arr_seq
            RM inst_23 JLDP) ->
       (forall j : Job,
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_3 arr_seq j ->
        @eq Bool
          (Prosa_Model_Preemption_Parameter_job_cannot_become_nonpreemptive_before_execution Job
             inst_3
             inst_23 j)
          Bool_true) ->
       Prosa_Model_Schedule_LimitedPreemptive_schedule_respects_preemption_model_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         inst_23 arr_seq
         (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job
            inst_3 JC JA arr_seq
            RM inst_23 JLDP)
```
