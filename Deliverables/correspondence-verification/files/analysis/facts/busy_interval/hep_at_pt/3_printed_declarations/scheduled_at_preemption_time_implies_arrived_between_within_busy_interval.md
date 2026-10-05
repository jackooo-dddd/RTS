# `scheduled_at_preemption_time_implies_arrived_between_within_busy_interval`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval`
- Lean: `Prosa.Analysis.Facts.BusyInterval.HepAtPt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval`
- Certificate: `scheduled_at_preemption_time_implies_arrived_between_within_busy_interval_correspondence`

## Official Rocq

```coq
scheduled_at_preemption_time_implies_arrived_between_within_busy_interval :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {JLFP : JLFP_policy Job},
@transitive_job_priorities Job JLFP ->
forall {H : JobPreemptable Job} {H0 : @JobReady Job PState Cost Arrival},
@work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
@valid_schedule Job Arrival PState sched Cost H0 arr_seq ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H H0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job Cost j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t2 ->
forall t : instant,
is_true (t1 <= t < t2) ->
is_true (@preemption_time Job H arr_seq PState sched t) ->
forall jhp : Equality.sort Job,
is_true (@scheduled_at Job PState sched jhp t) -> is_true (@arrived_between Job Arrival jhp t1 t2)

scheduled_at_preemption_time_implies_arrived_between_within_busy_interval is not universe polymorphic
Arguments scheduled_at_preemption_time_implies_arrived_between_within_busy_interval 
  {Job Arrival Cost} arr_seq {PState} H_uni sched {JLFP} H_priority_is_transitive 
  {H H0} H_job_ready H_sched_valid H_respects_policy j H_j_arrives H_job_cost_positive 
  t1 t2 H_busy_interval_prefix t H_t_in_busy_interval H_t_preemption_time jhp _
scheduled_at_preemption_time_implies_arrived_between_within_busy_interval is opaque
Expands to: Constant
            prosa.analysis.facts.busy_interval.hep_at_pt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval
Declared in library prosa.analysis.facts.busy_interval.hep_at_pt, line 188, characters 8-81
@scheduled_at_preemption_time_implies_arrived_between_within_busy_interval
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (JLFP : JLFP_policy Job),
       @transitive_job_priorities Job JLFP ->
       forall (H : JobPreemptable Job) (H0 : @JobReady Job PState Cost Arrival),
       @work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
       @valid_schedule Job Arrival PState sched Cost H0 arr_seq ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H H0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job Cost j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t2 ->
       forall t : instant,
       is_true (t1 <= t < t2) ->
       is_true (@preemption_time Job H arr_seq PState sched t) ->
       forall jhp : Equality.sort Job,
       is_true (@scheduled_at Job PState sched jhp t) -> is_true (@arrived_between Job Arrival jhp t1 t2)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.HepAtPt.scheduled_at_preemption_time_implies_arrived_between_within_busy_interval : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
      Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
        ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
          [inst_4 : Prosa.Behavior.Ready.JobReady Job PState],
          Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
                ∀ (j : Job),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    Prosa.Model.Job.Properties.job_cost_positive j = true →
                      ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
                          ∀ (t : Prosa.Behavior.Time.instant),
                            (decide (t1 ≤ t) && decide (t < t2)) = true →
                              Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t = true →
                                ∀ (jhp : Job),
                                  Prosa.Behavior.Service.scheduled_at sched jhp t = true →
                                    Prosa.Behavior.Arrival_sequence.arrived_between jhp t1 t2 = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_HepAtPt_scheduled_at_preemption_time_implies_arrived_between_within_busy_interval
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         (inst_32 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (inst_35 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_35 arr_seq sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_35 arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_32
         inst_35 arr_seq sched JLFP ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched
         JLFP j t1 t2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
            inst_3
            inst_32 arr_seq PState
            sched t)
         Bool_true ->
       forall jhp : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched jhp t)
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Arrival_sequence_arrived_between Job
            inst_3
            inst_6 jhp t1 t2)
         Bool_true
```
