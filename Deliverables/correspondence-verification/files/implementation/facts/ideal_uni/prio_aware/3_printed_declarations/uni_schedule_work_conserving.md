# `uni_schedule_work_conserving`

- Kind (Rocq): Corollary
- Rocq: `prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_work_conserving`
- Lean: `Prosa.Implementation.Facts.IdealUni.PrioAware.uni_schedule_work_conserving`
- Certificate: `uni_schedule_work_conserving_correspondence`

## Official Rocq

```coq
uni_schedule_work_conserving :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job JA arr_seq ->
forall {RM : @JobReady Job (processor_state Job) JC JA},
@nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
forall {H : JobPreemptable Job} {JLDP : JLDP_policy Job},
@work_conserving Job JA JC (processor_state Job) RM arr_seq (@uni_schedule Job JC JA arr_seq RM H JLDP)

uni_schedule_work_conserving is not universe polymorphic
Arguments uni_schedule_work_conserving {Job JC JA} arr_seq H_valid_arrivals {RM}
  H_nonclairvoyant_job_readiness {H JLDP} j t _ _
uni_schedule_work_conserving is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.prio_aware.uni_schedule_work_conserving
Declared in library prosa.implementation.facts.ideal_uni.prio_aware, line 45, characters 12-40
@uni_schedule_work_conserving
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job JA arr_seq ->
       forall RM : @JobReady Job (processor_state Job) JC JA,
       @nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
       forall (H : JobPreemptable Job) (JLDP : JLDP_policy Job),
       @work_conserving Job JA JC (processor_state Job) RM arr_seq
         (@uni_schedule Job JC JA arr_seq RM H JLDP)
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PrioAware.uni_schedule_work_conserving : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [JC : Prosa.Behavior.Job.JobCost Job] [JA : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
      Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
        ∀ [inst_1 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
          [JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job],
          Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq
            (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PrioAware_uni_schedule_work_conserving
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (JC : Prosa_Behavior_Job_JobCost Job
                 inst_3)
         (JA : Prosa_Behavior_Job_JobArrival Job
                 inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3 JA arr_seq ->
       forall
         RM : Prosa_Behavior_Ready_JobReady_inst4 Job
                inst_3
                (Prosa_Model_Processor_Ideal_processor_state Job
                   inst_3)
                JC JA,
       Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness_inst4 Job
         inst_3 JC JA
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM ->
       forall
         (inst_28 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (JLDP : Prosa_Model_Priority_Definitions_JLDP_policy Job
                   inst_3),
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_3 JA JC
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM arr_seq
         (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job
            inst_3 JC JA arr_seq
            RM inst_28 JLDP)
```
