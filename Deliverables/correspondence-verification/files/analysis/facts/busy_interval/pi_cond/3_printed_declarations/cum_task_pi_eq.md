# `cum_task_pi_eq`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi_cond.cum_task_pi_eq`
- Lean: `Prosa.Analysis.Facts.BusyInterval.PiCond.cum_task_pi_eq`
- Certificate: `cum_task_pi_eq_correspondence`

## Official Rocq

```coq
cum_task_pi_eq :
forall {Job : JobType} {Arrival : JobArrival Job} {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
@transitive_job_priorities Job JLFP ->
forall {H2 : JobPreemptable Job},
@valid_preemption_model Job Cost H2 PState arr_seq sched ->
forall {H3 : @JobReady Job PState Cost Arrival},
@work_bearing_readiness Job Arrival Cost PState H3 arr_seq sched JLFP ->
@valid_schedule Job Arrival PState sched Cost H3 arr_seq ->
@respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H2 H3 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job Cost j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t2 ->
forall (jlp : Equality.sort Job) (P : pred (Equality.sort Job)),
is_true (@scheduled_at Job PState sched jlp t1) ->
is_true (P jlp) ->
@cumulative_priority_inversion Job PState arr_seq sched JLFP j t1 t2 =
@cumulative_priority_inversion_cond Job PState arr_seq sched JLFP j P t1 t2

cum_task_pi_eq is not universe polymorphic
Arguments cum_task_pi_eq {Job Arrival Cost} arr_seq H_valid_arrivals {PState} H_uni 
  sched {JLFP} H_priority_is_reflexive H_priority_is_transitive {H2} H_valid_preemption_model 
  {H3} H_job_ready H_sched_valid H_respects_policy j H_j_arrives H_job_cost_positive 
  t1 t2 H_busy_interval_prefix jlp P _ _
cum_task_pi_eq is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi_cond.cum_task_pi_eq
Declared in library prosa.analysis.facts.busy_interval.pi_cond, line 67, characters 8-22
@cum_task_pi_eq
     : forall (Job : JobType) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       @transitive_job_priorities Job JLFP ->
       forall H2 : JobPreemptable Job,
       @valid_preemption_model Job Cost H2 PState arr_seq sched ->
       forall H3 : @JobReady Job PState Cost Arrival,
       @work_bearing_readiness Job Arrival Cost PState H3 arr_seq sched JLFP ->
       @valid_schedule Job Arrival PState sched Cost H3 arr_seq ->
       @respects_JLFP_policy_at_preemption_point Job Arrival Cost PState H2 H3 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job Cost j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t2 ->
       forall (jlp : Equality.sort Job) (P : pred (Equality.sort Job)),
       is_true (@scheduled_at Job PState sched jlp t1) ->
       is_true (P jlp) ->
       @cumulative_priority_inversion Job PState arr_seq sched JLFP j t1 t2 =
       @cumulative_priority_inversion_cond Job PState arr_seq sched JLFP j P t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.PiCond.cum_task_pi_eq : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
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
                                    ∀ (jlp : Job) (P : Job → Bool),
                                      Prosa.Behavior.Service.scheduled_at sched jlp t1 = true →
                                        P jlp = true →
                                          Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion
                                              arr_seq sched j t1 t2 =
                                            Prosa.Analysis.Definitions.PriorityInversion.cumulative_priority_inversion_cond
                                              arr_seq sched j P t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_PiCond_cum_task_pi_eq
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
         inst_9 PState arr_seq sched
         JLFP j t1 t2 ->
       forall (jlp : Job) (P : Job -> Bool),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3 PState sched jlp t1)
         Bool_true ->
       @eq Bool (P jlp) Bool_true ->
       @eq Nat
         (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion Job
            inst_3 PState arr_seq
            sched JLFP j t1 t2)
         (Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_cond Job
            inst_3 PState arr_seq
            sched JLFP j P t1 t2)
```
