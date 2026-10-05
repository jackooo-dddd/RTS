# `busy_interval_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.existence.busy_interval_is_bounded`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_is_bounded`
- Certificate: `busy_interval_is_bounded_correspondence`

## Official Rocq

```coq
busy_interval_is_bounded :
forall {Task : TaskType} {Job : JobType} {JobTask : JobTask Job Task} {Arrival : JobArrival Job}
  {Cost : JobCost Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job Arrival PState sched ->
@completed_jobs_dont_execute Job PState sched Cost ->
forall {JLFP : JLFP_policy Job} {H0 : @JobReady Job PState Cost Arrival},
@work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task JobTask tsk j) ->
is_true (@job_cost_positive Job Cost j) ->
@work_conserving Job Arrival Cost PState H0 arr_seq sched ->
@arrival_sequence_uniq Job arr_seq ->
@reflexive_job_priorities Job JLFP ->
forall t_busy : instant,
is_true (@pending Job PState sched Cost Arrival j t_busy) ->
@uniprocessor_model Job PState ->
@unit_service_proc_model Job PState ->
@ideal_progress_proc_model Job PState ->
forall t1 : instant,
(fun t2 : instant => [eta @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t2]) t1
  t_busy.+1 ->
forall priority_inversion_bound : instant -> instant,
  priority_inversion_bound ->
forall delta : duration,
is_true (0 < delta) ->
is_true
  (priority_inversion_bound (@job_arrival Job Arrival j - t1) +
   (fun t2 : instant => [eta @workload_of_hep_jobs Job Cost arr_seq JLFP j t2]) t1 (t1 + delta) <= delta) ->
exists t2 : nat,
  is_true (t2 <= t1 + delta) /\
  (fun t3 : instant => [eta @busy_interval Job Arrival Cost PState arr_seq sched JLFP j t3]) t1 t2

busy_interval_is_bounded is not universe polymorphic
Arguments busy_interval_is_bounded {Task Job JobTask Arrival Cost} arr_seq H_valid_arrival_time 
  {PState} sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute {JLFP H0} H_job_ready tsk j H_from_arrival_sequence 
  H_job_task H_job_cost_positive H_work_conserving H_arrival_sequence_is_a_set H_priority_is_reflexive 
  t_busy H_j_is_pending H_uni H_unit H_progress t1 H_is_busy_prefix priority_inversion_bound%function_scope
  H_priority_inversion_is_bounded delta H_delta_positive H_workload_is_bounded
busy_interval_is_bounded is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.existence.busy_interval_is_bounded
Declared in library prosa.analysis.facts.busy_interval.existence, line 559, characters 14-38
@busy_interval_is_bounded
     : forall (Task : TaskType) (Job : JobType) (JobTask : JobTask Job Task) (Arrival : JobArrival Job)
         (Cost : JobCost Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job Arrival PState sched ->
       @completed_jobs_dont_execute Job PState sched Cost ->
       forall (JLFP : JLFP_policy Job) (H0 : @JobReady Job PState Cost Arrival),
       @work_bearing_readiness Job Arrival Cost PState H0 arr_seq sched JLFP ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task JobTask tsk j) ->
       is_true (@job_cost_positive Job Cost j) ->
       @work_conserving Job Arrival Cost PState H0 arr_seq sched ->
       @arrival_sequence_uniq Job arr_seq ->
       @reflexive_job_priorities Job JLFP ->
       forall t_busy : instant,
       is_true (@pending Job PState sched Cost Arrival j t_busy) ->
       @uniprocessor_model Job PState ->
       @unit_service_proc_model Job PState ->
       @ideal_progress_proc_model Job PState ->
       forall t1 : instant,
       @busy_interval_prefix Job Arrival Cost PState arr_seq sched JLFP j t1 t_busy.+1 ->
       forall priority_inversion_bound : instant -> instant,
       @priority_inversion_of_job_is_bounded_by Job Arrival Cost PState arr_seq sched JLFP j
         priority_inversion_bound ->
       forall delta : duration,
       is_true (0 < delta) ->
       is_true
         (priority_inversion_bound (@job_arrival Job Arrival j - t1) +
          @workload_of_hep_jobs Job Cost arr_seq JLFP j t1 (t1 + delta) <= delta) ->
       exists t2 : nat,
         is_true (t2 <= t1 + delta) /\ @busy_interval Job Arrival Cost PState arr_seq sched JLFP j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Existence.busy_interval_is_bounded : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
            ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job)
              [inst_5 : Prosa.Behavior.Ready.JobReady Job PState],
              Prosa.Analysis.Definitions.WorkBearingReadiness.work_bearing_readiness arr_seq sched →
                ∀ (tsk : Task) (j : Job),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    Prosa.Model.Task.Concept.job_of_task tsk j = true →
                      Prosa.Model.Job.Properties.job_cost_positive j = true →
                        Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                          Prosa.Behavior.Arrival_sequence.arrival_sequence_uniq arr_seq →
                            Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
                              ∀ (t_busy : Prosa.Behavior.Time.instant),
                                Prosa.Behavior.Service.pending sched j t_busy = true →
                                  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
                                    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
                                      Prosa.Model.Processor.PlatformProperties.ideal_progress_proc_model PState →
                                        ∀ (t1 : Prosa.Behavior.Time.instant),
                                          Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq
                                              sched j t1 (t_busy + 1) →
                                            ∀
                                              (priority_inversion_bound :
                                                Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant),
                                              Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_of_job_is_bounded_by
                                                  arr_seq sched j priority_inversion_bound →
                                                ∀ (delta : Prosa.Behavior.Time.duration),
                                                  0 < delta →
                                                    priority_inversion_bound (Prosa.Behavior.Job.job_arrival j - t1) +
                                                          Prosa.Model.Aggregate.Workload.workload_of_hep_jobs arr_seq j
                                                            t1 (t1 + delta) ≤
                                                        delta →
                                                      ∃ t2 ≤ t1 + delta,
                                                        Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval
                                                          arr_seq sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Existence_busy_interval_is_bounded
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : 
          DecidableEq Task)
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
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched
         arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_14 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_17 ->
       forall
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3)
         (inst_45 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_17
            inst_14),
       Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness Job
         inst_3
         inst_14
         inst_17 PState
         inst_45 arr_seq sched JLFP ->
       forall (tsk : Task) (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_17 j)
         Bool_true ->
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_3
         inst_14
         inst_17 PState
         inst_45 arr_seq sched ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence_uniq Job
         inst_3 arr_seq ->
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall t_busy : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Behavior_Service_pending Job
            inst_3 PState sched
            inst_17
            inst_14 j t_busy)
         Bool_true ->
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       Prosa_Model_Processor_PlatformProperties_ideal_progress_proc_model Job
         inst_3 PState ->
       forall t1 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_14
         inst_17 PState arr_seq
         sched JLFP j t1
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t_busy
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))) ->
       forall priority_inversion_bound : Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_is_bounded_by Job
         inst_3
         inst_14
         inst_17 PState arr_seq
         sched JLFP j priority_inversion_bound ->
       forall delta : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) delta ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
            (priority_inversion_bound
               (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_3
                     inst_14 j)
                  t1))
            (Prosa_Model_Aggregate_Workload_workload_of_hep_jobs Job
               inst_3
               inst_17 arr_seq JLFP
               j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  delta)))
         delta ->
       Exists Nat
         (fun t2 : Nat =>
          And
            (LE_le_inst1 Nat instLENat t2
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  delta))
            (Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval Job
               inst_3
               inst_14
               inst_17 PState
               arr_seq sched JLFP j t1 t2))
```
