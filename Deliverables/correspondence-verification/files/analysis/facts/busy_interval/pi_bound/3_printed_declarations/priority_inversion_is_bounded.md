# `priority_inversion_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.pi_bound.priority_inversion_is_bounded`
- Lean: `Prosa.Analysis.Facts.BusyInterval.PiBound.priority_inversion_is_bounded`
- Certificate: `priority_inversion_is_bounded_correspondence`

## Official Rocq

```coq
priority_inversion_is_bounded :
forall {Task : TaskType} {H0 : TaskMaxNonpreemptiveSegment Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} {H4 : JobPreemptable Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState) {JLFP : JLFP_policy Job},
@transitive_job_priorities Job JLFP ->
@valid_model_with_bounded_nonpreemptive_segments Task Job H1 H3 H0 H4 PState arr_seq sched ->
forall {JobReady0 : @JobReady Job PState H3 H2},
@work_bearing_readiness Job H2 H3 PState JobReady0 arr_seq sched JLFP ->
@valid_schedule Job H2 PState sched H3 JobReady0 arr_seq ->
@respects_JLFP_policy_at_preemption_point Job H2 H3 PState H4 JobReady0 arr_seq sched JLFP ->
@valid_preemption_model Job H3 H4 PState arr_seq sched ->
forall (tsk : Equality.sort Task) (blocking_bound : duration -> duration),
@uniprocessor_model Job PState ->
@unit_service_proc_model Job PState ->
@ideal_progress_proc_model Job PState ->
(forall (j : Equality.sort Job) (t1 t2 : instant),
 @arrives_in Job arr_seq j ->
 is_true (@job_of_task Job Task H1 tsk j) ->
 @busy_interval_prefix Job H2 H3 PState arr_seq sched JLFP j t1 t2 ->
 is_true
   (@max_lp_nonpreemptive_segment Job H3 arr_seq JLFP H4 j t1 <= blocking_bound (@job_arrival Job H2 j - t1))) ->
@priority_inversion_is_bounded_by Task Job H1 H2 H3 PState arr_seq sched JLFP tsk blocking_bound

priority_inversion_is_bounded is not universe polymorphic
Arguments priority_inversion_is_bounded {Task H0 Job H1 H2 H3 H4} arr_seq H_valid_arrival_sequence 
  {PState} sched {JLFP} H_priority_is_transitive H_valid_model_with_bounded_nonpreemptive_segments
  {JobReady0} H_job_ready H_valid_schedule H_respects_policy H_valid_preemption_model 
  tsk blocking_bound%function_scope H_uni H_unit H_progress
  H_priority_inversion_is_bounded_by_blocking%function_scope j _ _ _ t1 t2 _
priority_inversion_is_bounded is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.pi_bound.priority_inversion_is_bounded
Declared in library prosa.analysis.facts.busy_interval.pi_bound, line 90, characters 8-37
@priority_inversion_is_bounded
     : forall (Task : TaskType) (H0 : TaskMaxNonpreemptiveSegment Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job) (H4 : JobPreemptable Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState) (JLFP : JLFP_policy Job),
       @transitive_job_priorities Job JLFP ->
       @valid_model_with_bounded_nonpreemptive_segments Task Job H1 H3 H0 H4 PState arr_seq sched ->
       forall JobReady0 : @JobReady Job PState H3 H2,
       @work_bearing_readiness Job H2 H3 PState JobReady0 arr_seq sched JLFP ->
       @valid_schedule Job H2 PState sched H3 JobReady0 arr_seq ->
       @respects_JLFP_policy_at_preemption_point Job H2 H3 PState H4 JobReady0 arr_seq sched JLFP ->
       @valid_preemption_model Job H3 H4 PState arr_seq sched ->
       forall (tsk : Equality.sort Task) (blocking_bound : duration -> duration),
       @uniprocessor_model Job PState ->
       @unit_service_proc_model Job PState ->
       @ideal_progress_proc_model Job PState ->
       (forall (j : Equality.sort Job) (t1 t2 : instant),
        @arrives_in Job arr_seq j ->
        is_true (@job_of_task Job Task H1 tsk j) ->
        @busy_interval_prefix Job H2 H3 PState arr_seq sched JLFP j t1 t2 ->
        is_true
          (@max_lp_nonpreemptive_segment Job H3 arr_seq JLFP H4 j t1 <=
           blocking_bound (@job_arrival Job H2 j - t1))) ->
       @priority_inversion_is_bounded_by Task Job H1 H2 H3 PState arr_seq sched JLFP tsk blocking_bound
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.PiBound.priority_inversion_is_bounded : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
      (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
      Prosa.Model.Priority.Definitions.transitive_job_priorities JLFP →
        Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
          ∀ [inst_7 : Prosa.Behavior.Ready.JobReady Job PState],
            Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
              Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
                  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                    ∀ (tsk : Task) (blocking_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                      Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
                        Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                          Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
                            (∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
                                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                                  Prosa.Model.Task.Concept.job_of_task tsk j = true →
                                    Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched
                                        j t1 t2 →
                                      Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment arr_seq j t1 ≤
                                        blocking_bound (Prosa.Behavior.Job.job_arrival j - t1)) →
                              Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by arr_seq
                                sched tsk blocking_bound
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_PiBound_priority_inversion_is_bounded
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
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
         (inst_23 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_17 arr_seq ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_transitive_job_priorities Job
         inst_3 JLFP ->
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_13
         inst_20
         inst_10
         inst_23 PState arr_seq sched ->
       forall
         inst_49 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_20
            inst_17,
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_17
         inst_20 PState
         inst_49 arr_seq sched JLFP ->
       Prosa_Behavior_Ready_valid_schedule Job
         inst_3
         inst_17 PState sched
         inst_20
         inst_49 arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point Job
         inst_3
         inst_17
         inst_20 PState
         inst_23
         inst_49 arr_seq sched JLFP ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_20
         inst_23 PState arr_seq sched ->
       forall (tsk : Task) (blocking_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       (forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_3 arr_seq j ->
        @eq Bool
          (Prosa_Model_Task_Concept_job_of_task Job
             inst_3 Task
             inst_7
             inst_13 tsk j)
          Bool_true ->
        Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
          inst_3
          inst_17
          inst_20 PState arr_seq sched
          JLFP j t1 t2 ->
        LE_le_inst1 Nat instLENat
          (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
             inst_3
             inst_20 arr_seq JLFP
             inst_23 j t1)
          (blocking_bound
             (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                (Prosa_Behavior_Job_JobArrival_job_arrival Job
                   inst_3
                   inst_17 j)
                t1))) ->
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by Task
         inst_7 Job
         inst_3
         inst_13
         inst_17
         inst_20 PState arr_seq sched
         JLFP tsk blocking_bound
```
