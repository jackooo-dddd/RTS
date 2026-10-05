# `scheduled_job_is_supremum`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.ideal_uni.prio_aware.scheduled_job_is_supremum`
- Lean: `Prosa.Implementation.Facts.IdealUni.PrioAware.scheduled_job_is_supremum`
- Certificate: `scheduled_job_is_supremum_correspondence`

## Official Rocq

```coq
scheduled_job_is_supremum :
forall {Job : JobType} {JC : JobCost Job} {JA : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job JA arr_seq ->
forall {RM : @JobReady Job (processor_state Job) JC JA},
@nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
forall {H : JobPreemptable Job} {JLDP : JLDP_policy Job} (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job (processor_state Job) (@uni_schedule Job JC JA arr_seq RM H JLDP) j t) ->
is_true (@preemption_time Job H arr_seq (processor_state Job) (@uni_schedule Job JC JA arr_seq RM H JLDP) t) ->
@supremum Job (@hep_job_at Job JLDP t)
  (@jobs_backlogged_at Job JA JC (processor_state Job) RM arr_seq
     ((fun t0 : nat =>
       match t0 with
       | 0 => @empty_schedule Job (processor_state Job) (@None (Equality.sort Job))
       | t'.+1 =>
           @schedule_up_to Job (processor_state Job)
             (@allocation_at Job JC JA arr_seq RM H (@choose_highest_prio_job Job JLDP))
             (@None (Equality.sort Job)) t'
       end) t)
     t) =
@Some (Equality.sort Job) j

scheduled_job_is_supremum is not universe polymorphic
Arguments scheduled_job_is_supremum {Job JC JA} arr_seq H_valid_arrivals {RM} H_nonclairvoyant_job_readiness
  {H JLDP} j t _ _
scheduled_job_is_supremum is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.prio_aware.scheduled_job_is_supremum
Declared in library prosa.implementation.facts.ideal_uni.prio_aware, line 99, characters 8-33
@scheduled_job_is_supremum
     : forall (Job : JobType) (JC : JobCost Job) (JA : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job JA arr_seq ->
       forall RM : @JobReady Job (processor_state Job) JC JA,
       @nonclairvoyant_readiness Job JC JA (processor_state Job) RM ->
       forall (H : JobPreemptable Job) (JLDP : JLDP_policy Job) (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job (processor_state Job) (@uni_schedule Job JC JA arr_seq RM H JLDP) j t) ->
       is_true
         (@preemption_time Job H arr_seq (processor_state Job) (@uni_schedule Job JC JA arr_seq RM H JLDP) t) ->
       @supremum Job (@hep_job_at Job JLDP t)
         (@jobs_backlogged_at Job JA JC (processor_state Job) RM arr_seq
            match t with
            | 0 => @empty_schedule Job (processor_state Job) (@None (Equality.sort Job))
            | t'.+1 =>
                @schedule_up_to Job (processor_state Job)
                  (@allocation_at Job JC JA arr_seq RM H (@choose_highest_prio_job Job JLDP))
                  (@None (Equality.sort Job)) t'
            end t) =
       @Some (Equality.sort Job) j
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PrioAware.scheduled_job_is_supremum : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [JC : Prosa.Behavior.Job.JobCost Job] [JA : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
      Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
        ∀ [inst_1 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
          [JLDP : Prosa.Model.Priority.Definitions.JLDP_policy Job] (j : Job) (t : Prosa.Behavior.Time.instant),
          Prosa.Behavior.Service.scheduled_at (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq)
                j t =
              true →
            Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq
                  (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq) t =
                true →
              Prosa.Util.Supremum.supremum (Prosa.Model.Priority.Definitions.hep_job_at t)
                  (Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq
                    (match t with
                    | 0 => Prosa.Implementation.Definitions.GenericScheduler.empty_schedule none
                    | Nat.succ t' =>
                      Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to
                        (Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at arr_seq
                          Prosa.Implementation.Definitions.IdealUniScheduler.choose_highest_prio_job)
                        none t')
                    t) =
                some j
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PrioAware_scheduled_job_is_supremum
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
                   inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job
               inst_3 JC JA
               arr_seq RM inst_28
               JLDP)
            j t)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Schedule_PreemptionTime_preemption_time_inst4 Job
            inst_3
            inst_28 arr_seq
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule Job
               inst_3 JC JA
               arr_seq RM inst_28
               JLDP)
            t)
         Bool_true ->
       @eq (Option Job)
         (Prosa_Util_Supremum_supremum Job
            (Prosa_Model_Priority_Definitions_JLDP_policy_hep_job_at Job
               inst_3 JLDP t)
            (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst4 Job
               inst_3 JA JC
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               RM arr_seq
               (Prosa_Implementation_Facts_IdealUni_PrioAware_scheduled_job_is_supremum_match_1
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
                        inst_3 JC
                        JA arr_seq RM
                        inst_28
                        (Prosa_Implementation_Definitions_IdealUniScheduler_choose_highest_prio_job Job
                           inst_3
                           JLDP))
                     (Option_none Job) t'))
               t))
         (Option_some Job j)
```
