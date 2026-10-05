# `preemption_time_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi.preemption_time_exists`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Pi.preemption_time_exists`
- Certificate: `preemption_time_exists_correspondence`

## Official Rocq

```coq
preemption_time_exists :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
forall (sched : @schedule Job PState) {JLFP : JLFP_policy Job},
@transitive_job_priorities Job JLFP ->
forall {H3 : TaskMaxNonpreemptiveSegment Task} {H4 : JobPreemptable Job},
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
@valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 H4 PState arr_seq sched ->
@unit_service_proc_model Job PState ->
@ideal_progress_proc_model Job PState ->
exists pr_t : instant,
  is_true (@preemption_time Job H4 arr_seq PState sched pr_t) /\
  is_true (t1 <= pr_t <= t1 + @max_lp_nonpreemptive_segment Job H2 arr_seq JLFP H4 j t1)

preemption_time_exists is not universe polymorphic
Arguments preemption_time_exists {Task Job H0 H1 H2} arr_seq H_valid_arrivals {PState} 
  H_uni sched {JLFP} H_priority_is_transitive {H3 H4} H_valid_preemption_model {JobReady0} 
  H_job_ready H_sched_valid H_respects_policy j H_j_arrives H_job_cost_positive t1 
  t2 H_busy_interval_prefix H_valid_model_with_bounded_nonpreemptive_segments H_unit 
  H_progress
preemption_time_exists is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi.preemption_time_exists
Declared in library prosa.analysis.facts.busy_interval.pi, line 635, characters 10-32
@preemption_time_exists
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall PState : ProcessorState Job,
       @uniprocessor_model Job PState ->
       forall (sched : @schedule Job PState) (JLFP : JLFP_policy Job),
       @transitive_job_priorities Job JLFP ->
       forall (H3 : TaskMaxNonpreemptiveSegment Task) (H4 : JobPreemptable Job),
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
       @valid_model_with_bounded_nonpreemptive_segments Task Job H0 H2 H3 H4 PState arr_seq sched ->
       @unit_service_proc_model Job PState ->
       @ideal_progress_proc_model Job PState ->
       exists pr_t : instant,
         is_true (@preemption_time Job H4 arr_seq PState sched pr_t) /\
         is_true (t1 <= pr_t <= t1 + @max_lp_nonpreemptive_segment Job H2 arr_seq JLFP H4 j t1)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Pi.preemption_time_exists : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job},
      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
          Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
            ∀ [inst_5 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
              [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
              Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                ∀ [inst_7 : Prosa.Behavior.Ready.JobReady Job PState],
                  Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                    Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                      Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
                        ∀ (j : Job),
                          Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                            Prosa.Model.Job.Properties.job_cost_positive j = true →
                              ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                                Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j
                                    t1 t2 →
                                  Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments
                                      arr_seq sched →
                                    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                                      Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
                                        ∃ pr_t,
                                          Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched pr_t =
                                              true ∧
                                            (decide (t1 ≤ pr_t) &&
                                                decide
                                                  (pr_t ≤
                                                    t1 +
                                                      Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment
                                                        arr_seq j t1)) =
                                              true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Pi_preemption_time_exists
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_14 arr_seq ->
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
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       forall
         (inst_43 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_7)
         (inst_46 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3),
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_17
         inst_46 PState arr_seq sched ->
       forall
         inst_55 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_17
            inst_14,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_14
         inst_17 PState
         inst_55 arr_seq sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_14 PState sched
         inst_17
         inst_55 arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_14
         inst_17 PState
         inst_46
         inst_55 arr_seq sched JLFP ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_17 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_14
         inst_17 PState arr_seq sched JLFP
         j t1 t2 ->
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_10
         inst_17
         inst_43
         inst_46 PState arr_seq sched ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       Exists Prosa_Behavior_Time_instant
         (fun pr_t : Prosa_Behavior_Time_instant =>
          And
            (@eq Bool
               (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                  inst_3
                  inst_46 arr_seq PState
                  sched pr_t)
               Bool_true)
            (@eq Bool
               (Bool_and
                  (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 pr_t)
                     (Nat_decLe t1 pr_t))
                  (Decidable_decide
                     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat pr_t
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                           (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
                              inst_3
                              inst_17
                              arr_seq JLFP
                              inst_46 j t1)))
                     (Nat_decLe pr_t
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                           (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
                              inst_3
                              inst_17
                              arr_seq JLFP
                              inst_46 j t1)))))
               Bool_true))
```
