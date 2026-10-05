# `not_interference_implies_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.iw_instantiation.not_interference_implies_scheduled`
- Lean: `Prosa.Analysis.Abstract.Ideal.IwInstantiation.not_interference_implies_scheduled`
- Certificate: `not_interference_implies_scheduled_correspondence`

## Official Rocq

```coq
not_interference_implies_scheduled :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H2 ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall {JobReady0 : @JobReady Job (ideal.processor_state Job) H2 H1},
@work_bearing_readiness Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched JLFP ->
@work_conserving.work_conserving Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched ->
@reflexive_job_priorities Job JLFP ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (0 < @job_cost Job H2 j) ->
forall t1 t2 : instant,
@definitions.busy_interval_prefix Job H1 H2 (ideal.processor_state Job) sched
  (@ideal_jlfp_interference Job arr_seq sched JLFP)
  (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP) j t1 t2 ->
forall t : instant,
is_true (t1 <= t < t2) ->
~ is_true (@interference Job (@ideal_jlfp_interference Job arr_seq sched JLFP) j t) ->
is_true (@receives_service_at Job (ideal.processor_state Job) sched j t)

not_interference_implies_scheduled is not universe polymorphic
Arguments not_interference_implies_scheduled {Job H1 H2} arr_seq H_valid_arrival_sequence 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  {JLFP} H_priority_is_reflexive {JobReady0} H_work_bearing_readiness H_work_conserving 
  H_policy_reflexive j H_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix 
  t H_t_in_busy_interval _
not_interference_implies_scheduled is opaque
Expands to: Constant prosa.analysis.abstract.ideal.iw_instantiation.not_interference_implies_scheduled
Declared in library prosa.analysis.abstract.ideal.iw_instantiation, line 558, characters 12-46
@not_interference_implies_scheduled
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H2 ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall JobReady0 : @JobReady Job (ideal.processor_state Job) H2 H1,
       @work_bearing_readiness Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched JLFP ->
       @work_conserving.work_conserving Job H1 H2 (ideal.processor_state Job) JobReady0 arr_seq sched ->
       @reflexive_job_priorities Job JLFP ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (0 < @job_cost Job H2 j) ->
       forall t1 t2 : instant,
       @definitions.busy_interval_prefix Job H1 H2 (ideal.processor_state Job) sched
         (@ideal_jlfp_interference Job arr_seq sched JLFP)
         (@ideal_jlfp_interfering_workload Job H2 arr_seq sched JLFP) j t1 t2 ->
       forall t : instant,
       is_true (t1 <= t < t2) ->
       ~ is_true (@interference Job (@ideal_jlfp_interference Job arr_seq sched JLFP) j t) ->
       is_true (@receives_service_at Job (ideal.processor_state Job) sched j t)
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.IwInstantiation.not_interference_implies_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
              Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                ∀ [JobReady0 : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
                  Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                    Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                      Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                        ∀ (j : Job),
                          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                            0 < Prosa.Behavior.Job.job_cost j →
                              ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
                                  ∀ (t : Prosa.Behavior.Time.instant),
                                    (decide (t1 ≤ t) && decide (t < t2)) = true →
                                      ¬Prosa.Analysis.Abstract.Definitions.interference j t = true →
                                        Prosa.Behavior.Service.receives_service_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_IwInstantiation_not_interference_implies_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_7
         inst_10
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_7
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_13 ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall
         JobReady0 : Prosa_Behavior_Ready_JobReady_inst4 Job
                       inst_7
                       (Prosa_Model_Processor_Ideal_processor_state Job
                          inst_7)
                       inst_13
                       inst_10,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness_inst4 Job
         inst_7
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         JobReady0 arr_seq sched JLFP ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_7
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         JobReady0 arr_seq sched ->
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_7
            inst_13 j) ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            JLFP)
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_13 arr_seq sched
            JLFP)
         inst_10
         inst_13
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched j t1 t2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
            (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t t2) (Nat_decLt t t2)))
         Bool_true ->
       Not
         (@eq Bool
            (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
               inst_7
               (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
                  inst_7 arr_seq
                  sched JLFP)
               j t)
            Bool_true) ->
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            sched j t)
         Bool_true
```
