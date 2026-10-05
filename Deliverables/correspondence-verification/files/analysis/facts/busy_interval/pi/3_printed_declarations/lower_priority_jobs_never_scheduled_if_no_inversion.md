# `lower_priority_jobs_never_scheduled_if_no_inversion`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.busy_interval.pi.lower_priority_jobs_never_scheduled_if_no_inversion`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.lower_priority_jobs_never_scheduled_if_no_inversion`
- Certificate: `lower_priority_jobs_never_scheduled_if_no_inversion_correspondence`

## Official Rocq

```coq
lower_priority_jobs_never_scheduled_if_no_inversion :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
@transitive_job_priorities Job JLFP ->
forall {H4 : JobPreemptable Job},
@valid_preemption_model Job H2 H4 PState arr_seq sched ->
forall {JobReady0 : @JobReady Job PState H2 H1},
@work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
@respects_JLFP_policy_at_preemption_point Job H1 H2 PState H4 JobReady0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H2 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
forall jlp : Equality.sort Job,
is_true (~~ @hep_job Job JLFP jlp j) ->
forall t : nat,
is_true (t1 <= t < t2) ->
is_true (~~ @priority_inversion Job PState arr_seq sched JLFP j t1) ->
is_true (~~ @scheduled_at Job PState sched jlp t)

lower_priority_jobs_never_scheduled_if_no_inversion is not universe polymorphic
Arguments lower_priority_jobs_never_scheduled_if_no_inversion {Job H1 H2} arr_seq 
  H_valid_arrivals {PState} H_uni sched {JLFP} H_priority_is_reflexive H_priority_is_transitive 
  {H4} H_valid_preemption_model {JobReady0} H_job_ready H_sched_valid H_respects_policy 
  j H_j_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix jlp H_jlp_lower_priority 
  t%nat_scope _ _
lower_priority_jobs_never_scheduled_if_no_inversion is opaque
Expands to: Constant
            prosa.analysis.facts.busy_interval.pi.lower_priority_jobs_never_scheduled_if_no_inversion
Declared in library prosa.analysis.facts.busy_interval.pi, line 184, characters 14-65
@lower_priority_jobs_never_scheduled_if_no_inversion
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       @transitive_job_priorities Job JLFP ->
       forall H4 : JobPreemptable Job,
       @valid_preemption_model Job H2 H4 PState arr_seq sched ->
       forall JobReady0 : @JobReady Job PState H2 H1,
       @work_bearing_readiness Job H1 H2 PState JobReady0 arr_seq sched JLFP ->
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       @respects_JLFP_policy_at_preemption_point Job H1 H2 PState H4 JobReady0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H1 H2 PState arr_seq sched JLFP j t1 t2 ->
       forall jlp : Equality.sort Job,
       is_true (~~ @hep_job Job JLFP jlp j) ->
       forall t : nat,
       is_true (t1 <= t < t2) ->
       is_true (~~ @priority_inversion Job PState arr_seq sched JLFP j t1) ->
       is_true (~~ @scheduled_at Job PState sched jlp t)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.lower_priority_jobs_never_scheduled_if_no_inversion : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
          Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
            Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
              ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                  ∀ [inst_4 : Prosa.Behavior.Ready.JobReady Job PState],
                    Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                        Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                            JLFP →
                          ∀ (j : Job),
                            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                              Prosa.Model.Job.Properties.job_cost_positive j = true →
                                ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                  Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j
                                      t1 t2 →
                                    ∀ (jlp : Job),
                                      (!Prosa.Model.Priority.Definitions.hep_job jlp j) = true →
                                        ∀ (t : ℕ),
                                          (decide (t1 ≤ t) && decide (t < t2)) = true →
                                            (!Prosa.Analysis.Definitions.PriorityInversion.priority_inversion arr_seq
                                                    sched j t1) =
                                                true →
                                              (!Prosa.Behavior.Service.scheduled_at sched jlp t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_lower_priority_jobs_never_scheduled_if_no_inversion
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
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         inst_38 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_9
         inst_38 PState arr_seq sched ->
       forall
         inst_47 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_6
         inst_9 PState
         inst_47 arr_seq sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_6 PState sched
         inst_9
         inst_47 arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_6
         inst_9 PState
         inst_38
         inst_47 arr_seq sched JLFP ->
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
         inst_9 PState arr_seq sched JLFP
         j t1 t2 ->
       forall jlp : Job,
       @eq Bool
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
               inst_3 JLFP jlp j))
         Bool_true ->
       forall t : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_PriorityInversion_priority_inversion Job
               inst_3 PState arr_seq sched
               JLFP j t1))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_scheduled_at Job
               inst_3 PState sched jlp t))
         Bool_true
```
