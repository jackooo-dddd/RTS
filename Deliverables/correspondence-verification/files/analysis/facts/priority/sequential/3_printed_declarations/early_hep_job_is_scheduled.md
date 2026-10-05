# `early_hep_job_is_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.priority.sequential.early_hep_job_is_scheduled`
- Lean: `Prosa.Analysis.Facts.Priority.Sequential.early_hep_job_is_scheduled`
- Certificate: `early_hep_job_is_scheduled_correspondence`

## Official Rocq

```coq
early_hep_job_is_scheduled :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {JLFP : JLFP_policy Job},
@transitive_job_priorities Job JLFP ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {H : @JobReady Job PState Cost Arrival},
@work_bearing_readiness Job Arrival Cost PState H arr_seq sched JLFP ->
@valid_schedule Job Arrival PState sched Cost H arr_seq ->
forall {H0 : JobPreemptable Job},
@valid_preemption_model Job Cost H0 PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H0 H arr_seq sched JLFP ->
forall j1 j2 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
is_true (@job_arrival Job Arrival j1 < @job_arrival Job Arrival j2) ->
@always_higher_priority Job (@JLFP_to_JLDP Job JLFP) j1 j2 ->
forall t : instant,
is_true (@scheduled_at Job PState sched j2 t) -> is_true (@completed_by Job PState sched Cost j1 t)

early_hep_job_is_scheduled is not universe polymorphic
Arguments early_hep_job_is_scheduled {Job Arrival Cost} arr_seq H_valid_arrivals 
  {JLFP} H_priority_is_transitive {PState} H_uniproc sched {H} H_job_ready H_sched_valid 
  {H0} H_valid_preemption_model H_respects_policy j1 j2 _ _ _ t _
early_hep_job_is_scheduled is opaque
Expands to: Constant prosa.analysis.facts.priority.sequential.early_hep_job_is_scheduled
Declared in library prosa.analysis.facts.priority.sequential, line 55, characters 8-34
@early_hep_job_is_scheduled
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall JLFP : JLFP_policy Job,
       @transitive_job_priorities Job JLFP ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (H : @JobReady Job PState Cost Arrival),
       @work_bearing_readiness Job Arrival Cost PState H arr_seq sched JLFP ->
       @valid_schedule Job Arrival PState sched Cost H arr_seq ->
       forall H0 : JobPreemptable Job,
       @valid_preemption_model Job Cost H0 PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H0 H arr_seq sched JLFP ->
       forall j1 j2 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       is_true (@job_arrival Job Arrival j1 < @job_arrival Job Arrival j2) ->
       @always_higher_priority Job (@JLFP_to_JLDP Job JLFP) j1 j2 ->
       forall t : instant,
       is_true (@scheduled_at Job PState sched j2 t) -> is_true (@completed_by Job PState sched Cost j1 t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Priority.Sequential.early_hep_job_is_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
      Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
        ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job),
          Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
            ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [inst_3 : Prosa.Behavior.Ready.JobReady Job PState],
              Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                  ∀ [inst_4 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                    Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                      Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
                        ∀ (j1 j2 : Job),
                          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
                            Prosa.Behavior.Job.job_arrival j1 < Prosa.Behavior.Job.job_arrival j2 →
                              Prosa.Analysis.Definitions.AlwaysHigherPriority.always_higher_priority j1 j2 →
                                ∀ (t : Prosa.Behavior.Time.instant),
                                  Prosa.Behavior.Service.scheduled_at sched j2 t = true →
                                    Prosa.Behavior.Service.completed_by sched j1 t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Priority_Sequential_early_hep_job_is_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_39 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_39 arr_seq sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_39 arr_seq ->
       forall
         inst_53 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_53 PState arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_53
         inst_39 arr_seq sched JLFP ->
       forall j1 j2 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j1 ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j1)
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j2) ->
       Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority Job
         inst_3
         (Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job
            inst_3 JLFP)
         j1 j2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched j2 t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_completed_by Job
            inst_3 PState sched
            inst_9 j1 t)
         Bool_true
```
