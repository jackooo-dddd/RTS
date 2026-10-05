# `lp_job_bounded_service`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service`
- Lean: `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.lp_job_bounded_service`
- Certificate: `lp_job_bounded_service_correspondence`

## Official Rocq

```coq
lp_job_bounded_service :
forall {Task : TaskType} {H0 : TaskMaxNonpreemptiveSegment Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
forall {JLFP : JLFP_policy Job},
@transitive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H2 arr_seq ->
forall (sched : @schedule Job PState) {JobReady0 : @JobReady Job PState H3 H2},
@work_bearing_readiness Job H2 H3 PState JobReady0 arr_seq sched JLFP ->
@valid_schedule Job H2 PState sched H3 JobReady0 arr_seq ->
forall {H4 : JobPreemptable Job},
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
@valid_model_with_bounded_nonpreemptive_segments Task Job H1 H3 H0 H4 PState arr_seq sched ->
@respects_JLFP_policy_at_preemption_point Job H2 H3 PState H4 JobReady0 arr_seq sched JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H3 j) ->
forall jlp : Equality.sort Job,
@arrives_in Job arr_seq jlp ->
is_true (~~ @hep_job Job JLFP jlp j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H2 H3 PState arr_seq sched JLFP j t1 t2 ->
forall t : nat,
is_true (t <= t2) ->
is_true (@service_during Job PState sched jlp t1 t <= @job_max_nonpreemptive_segment Job H3 H4 jlp - 1)

lp_job_bounded_service is not universe polymorphic
Arguments lp_job_bounded_service {Task H0 Job H1 H2 H3 PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model {JLFP} H_priority_is_transitive arr_seq H_valid_arrival_sequence 
  sched {JobReady0} H_job_ready H_sched_valid {H4} H_valid_preemption_model
  H_valid_model_with_bounded_nonpreemptive_segments H_respects_policy j H_j_arrives 
  H_j_job_cost_positive jlp H_jlp_arrives H_jlp_lp t1 t2 H_busy_prefix t%nat_scope 
  _
lp_job_bounded_service is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.service_inversion.lp_job_bounded_service
Declared in library prosa.analysis.facts.busy_interval.service_inversion, line 491, characters 10-32
@lp_job_bounded_service
     : forall (Task : TaskType) (H0 : TaskMaxNonpreemptiveSegment Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       forall JLFP : JLFP_policy Job,
       @transitive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H2 arr_seq ->
       forall (sched : @schedule Job PState) (JobReady0 : @JobReady Job PState H3 H2),
       @work_bearing_readiness Job H2 H3 PState JobReady0 arr_seq sched JLFP ->
       @valid_schedule Job H2 PState sched H3 JobReady0 arr_seq ->
       forall H4 : JobPreemptable Job,
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       @valid_model_with_bounded_nonpreemptive_segments Task Job H1 H3 H0 H4 PState arr_seq sched ->
       @respects_JLFP_policy_at_preemption_point Job H2 H3 PState H4 JobReady0 arr_seq sched JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H3 j) ->
       forall jlp : Equality.sort Job,
       @arrives_in Job arr_seq jlp ->
       is_true (~~ @hep_job Job JLFP jlp j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H2 H3 PState arr_seq sched JLFP j t1 t2 ->
       forall t : nat,
       is_true (t <= t2) ->
       is_true
         (@service_during Job PState sched jlp t1 t <= @job_max_nonpreemptive_segment Job H3 H4 jlp - 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.ServiceInversion.lp_job_bounded_service : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
        Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
          ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
            Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
              ∀ (sched : Prosa.Behavior.Schedule.schedule PState) [inst_6 : Prosa.Behavior.Ready.JobReady Job PState],
                Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                    ∀ [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
                      Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                        Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq
                            sched →
                          Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                              JLFP →
                            ∀ (j : Job),
                              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                Prosa.Model.Job.Properties.job_cost_positive j = true →
                                  ∀ (jlp : Job),
                                    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq jlp →
                                      (!Prosa.Model.Priority.Definitions.hep_job jlp j) = true →
                                        ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                          Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq
                                              sched j t1 t2 →
                                            ∀ t ≤ t2,
                                              Prosa.Behavior.Service.service_during sched jlp t1 t ≤
                                                Prosa.Model.Preemption.Parameter.job_max_nonpreemptive_segment jlp - 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_ServiceInversion_lp_job_bounded_service
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : 
          DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_7)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_17 arr_seq ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState)
         (inst_53 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_20
            inst_17),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_17
         inst_20 PState
         inst_53 arr_seq
         sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_17 PState sched
         inst_20
         inst_53 arr_seq ->
       forall
         inst_67 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_20
         inst_67 PState
         arr_seq sched ->
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_13
         inst_20
         inst_10
         inst_67 PState
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_17
         inst_20 PState
         inst_67
         inst_53 arr_seq
         sched JLFP ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_20 j)
         Bool_true ->
       forall jlp : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq jlp ->
       @eq Bool
         (Bool_not
            (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
               inst_3 JLFP
               jlp j))
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_17
         inst_20 PState
         arr_seq sched JLFP j t1 t2 ->
       forall t : Nat,
       LE_le_inst1 Nat instLENat t t2 ->
       LE_le_inst1 Prosa_Behavior_Job_work instLENat
         (Prosa_Behavior_Service_service_during Job
            inst_3 PState
            sched jlp t1 t)
         (HSub_hSub_inst7 Nat Prosa_Behavior_Job_work Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Model_Preemption_Parameter_job_max_nonpreemptive_segment Job
               inst_3
               inst_20
               inst_67 jlp)
            (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1)))
```
