# `uni_schedule_valid`

- Kind (Rocq): Corollary
- Rocq: `prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_valid`
- Lean: `Prosa.Implementation.Facts.IdealUni.PrioAware.uni_schedule_valid`
- Certificate: `uni_schedule_valid_correspondence`

## Official Rocq

```coq
uni_schedule_valid :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job} (arr_seq : arrival_sequence Job)
  {RM : @JobReady Job (processor_state Job) JC JA},
@nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
forall {H : JobPreemptable Job} {JLDP : JLDP_policy Job},
@valid_schedule Job JA (processor_state Job) (@uni_schedule Job JC JA arr_seq RM H JLDP) JC RM arr_seq

uni_schedule_valid is not universe polymorphic
Arguments uni_schedule_valid {Job JC JA} arr_seq {RM} H_nonclairvoyant_job_readiness {H JLDP}
uni_schedule_valid is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_valid
Declared in library prosa.implementation.facts.ideal_uni.prio_aware, line 56, characters 12-30
@uni_schedule_valid
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) (arr_seq : arrival_sequence Job)
         (RM : @JobReady Job (processor_state Job) JC JA),
       @nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
       forall (H : JobPreemptable Job) (JLDP : JLDP_policy Job),
       @valid_schedule Job JA (processor_state Job) (@uni_schedule Job JC JA arr_seq RM H JLDP) JC RM arr_seq
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PrioAware.uni_schedule_valid : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [JC : Prosa.Behavior.Job.JobCost Job] [JA : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
  Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
    ∀ [inst_1 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
      [JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job],
      Prosa.Behavior.Ready.valid_schedule (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq)
        arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PrioAware_uni_schedule_valid
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
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_3 JA
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job
            inst_3 JC JA arr_seq
            RM inst_23 JLDP)
         JC RM arr_seq
```
