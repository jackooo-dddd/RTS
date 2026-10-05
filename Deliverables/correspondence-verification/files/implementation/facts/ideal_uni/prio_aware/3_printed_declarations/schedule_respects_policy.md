# `schedule_respects_policy`

- Kind (Rocq): Theorem
- Rocq: `prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_policy`
- Lean: `Prosa.Implementation.Facts.IdealUni.PrioAware.schedule_respects_policy`
- Certificate: `schedule_respects_policy_correspondence`

## Official Rocq

```coq
schedule_respects_policy :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job JA arr_seq ->
forall {RM : @JobReady Job (processor_state Job) JC JA},
@nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
forall {H : JobPreemptable Job} {JLDP : JLDP_policy Job},
@reflexive_priorities Job JLDP ->
@total_priorities Job JLDP ->
@transitive_priorities Job JLDP ->
@respects_JLDP_policy_at_preemption_point Job JA JC (processor_state Job) H RM arr_seq
  (@uni_schedule Job JC JA arr_seq RM H JLDP) JLDP

schedule_respects_policy is not universe polymorphic
Arguments schedule_respects_policy {Job JC JA} arr_seq H_valid_arrivals {RM} H_nonclairvoyant_job_readiness
  {H JLDP} H_reflexive_priorities H_total H_transitive j j_hp t _ _ _ _
schedule_respects_policy is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.prio_aware.schedule_respects_policy
Declared in library prosa.implementation.facts.ideal_uni.prio_aware, line 118, characters 10-34
@schedule_respects_policy
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job JA arr_seq ->
       forall RM : @JobReady Job (processor_state Job) JC JA,
       @nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
       forall (H : JobPreemptable Job) (JLDP : JLDP_policy Job),
       @reflexive_priorities Job JLDP ->
       @total_priorities Job JLDP ->
       @transitive_priorities Job JLDP ->
       @respects_JLDP_policy_at_preemption_point Job JA JC (processor_state Job) H RM arr_seq
         (@uni_schedule Job JC JA arr_seq RM H JLDP) JLDP
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PrioAware.schedule_respects_policy : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [JC : Prosa.Behavior.Job.JobCost Job] [JA : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
      Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
        ∀ [inst_1 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
          [JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job],
          Prosa.Model.Priority.Definitions.reflexive_priorities JLDP →
            Prosa.Model.Priority.Definitions.total_priorities JLDP →
              Prosa.Model.Priority.Definitions.transitive_priorities JLDP →
                Prosa.Model.Schedule.PriorityDriven.respects_JLDP_policy_at_preemption_point arr_seq
                  (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq) JLDP
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PrioAware_schedule_respects_policy
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
       Prosa_Model_Priority_Definitions_reflexive_priorities Job
         inst_3 JLDP ->
       Prosa_Model_Priority_Definitions_total_priorities Job
         inst_3 JLDP ->
       Prosa_Model_Priority_Definitions_transitive_priorities Job
         inst_3 JLDP ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point_inst4 Job
         inst_3 JA JC
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         inst_28 RM arr_seq
         (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job
            inst_3 JC JA arr_seq
            RM inst_28 JLDP)
         JLDP
```
