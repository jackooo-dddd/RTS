# `uniprocessor_response_time_bound_fully_nonpreemptive_fp`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.rta.exc.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp`
- Lean: `Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp`
- Certificate: `uniprocessor_response_time_bound_fully_nonpreemptive_fp_correspondence`

## Official Rocq

```coq
uniprocessor_response_time_bound_fully_nonpreemptive_fp :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobCost Job} {H3 : JobArrival Job} (arr_seq : arrival_sequence Job)
  (ts : seq (Equality.sort Task)),
@valid_task_arrival_sequence Task H H0 Job H1 H2 H3 ts arr_seq ->
forall sched : @schedule Job (exceedance_proc_state Job),
@valid_schedule Job H3 (exceedance_proc_state Job) sched H2 (@sequential_readiness Task Job H1 H2 H3 arr_seq)
  arr_seq ->
@work_conserving Job H3 H2 (exceedance_proc_state Job) (@sequential_readiness Task Job H1 H2 H3 arr_seq)
  arr_seq sched ->
@nonpreemptive_schedule Job H2 (exceedance_proc_state Job) sched ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
@transitive_task_priorities Task FP ->
@respects_FP_policy_at_preemption_point Task Job H1 H3 H2 (exceedance_proc_state Job)
  (@fully_nonpreemptive_job_model Job H2) (@sequential_readiness Task Job H1 H2 H3 arr_seq) arr_seq sched FP ->
forall (e : work) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
(forall (j : Equality.sort Job) (t1 t2 : instant),
 @arrives_in Job arr_seq j ->
 is_true (@job_of_task Job Task H1 tsk j) ->
 @busy_interval_prefix Job H3 H2 (exceedance_proc_state Job) arr_seq sched (@FP_to_JLFP Job Task H1 FP) j t1
   t2 ->
 is_true (\sum_(t1 <= t < t2) nat_of_bool (@is_exceedance_exec Job (sched t)) <= e)) ->
forall L : duration,
@busy_window_recurrence_solution Task H H0 ts FP e tsk L ->
forall R : duration,
@rta_recurrence_solution Task H H0 ts FP e tsk L R ->
@task_response_time_bound Task Job H3 H2 H1 (exceedance_proc_state Job) arr_seq sched tsk R

uniprocessor_response_time_bound_fully_nonpreemptive_fp is not universe polymorphic
Arguments uniprocessor_response_time_bound_fully_nonpreemptive_fp {Task H H0 Job H1 H2 H3} 
  arr_seq ts%seq_scope H_valid_task_arrival_sequence sched H_valid_schedule H_work_conserving
  H_nonpreemptive_sched {FP} H_priority_is_reflexive H_priority_is_transitive
  H_respects_policy_at_preemption_point e tsk H_tsk_in_ts
  H_exceedance_in_busy_interval_bounded%function_scope L _ R _ j _ _
uniprocessor_response_time_bound_fully_nonpreemptive_fp is opaque
Expands to: Constant
            prosa.results.rta.exc.fp.fully_nonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp
Declared in library prosa.results.rta.exc.fp.fully_nonpreemptive, line 98, characters 10-65
@uniprocessor_response_time_bound_fully_nonpreemptive_fp
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobCost Job) (H3 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (ts : seq (Equality.sort Task)),
       @valid_task_arrival_sequence Task H H0 Job H1 H2 H3 ts arr_seq ->
       forall sched : @schedule Job (exceedance_proc_state Job),
       @valid_schedule Job H3 (exceedance_proc_state Job) sched H2
         (@sequential_readiness Task Job H1 H2 H3 arr_seq) arr_seq ->
       @work_conserving Job H3 H2 (exceedance_proc_state Job)
         (@sequential_readiness Task Job H1 H2 H3 arr_seq) arr_seq sched ->
       @nonpreemptive_schedule Job H2 (exceedance_proc_state Job) sched ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       @transitive_task_priorities Task FP ->
       @respects_FP_policy_at_preemption_point Task Job H1 H3 H2 (exceedance_proc_state Job)
         (@fully_nonpreemptive_job_model Job H2) (@sequential_readiness Task Job H1 H2 H3 arr_seq) arr_seq
         sched FP ->
       forall (e : work) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       (forall (j : Equality.sort Job) (t1 t2 : instant),
        @arrives_in Job arr_seq j ->
        is_true (@job_of_task Job Task H1 tsk j) ->
        @busy_interval_prefix Job H3 H2 (exceedance_proc_state Job) arr_seq sched
          (@FP_to_JLFP Job Task H1 FP) j t1 t2 ->
        is_true (\sum_(t1 <= t < t2) nat_of_bool (@is_exceedance_exec Job (sched t)) <= e)) ->
       forall L : duration,
       @busy_window_recurrence_solution Task H H0 ts FP e tsk L ->
       forall R : duration,
       @rta_recurrence_solution Task H H0 ts FP e tsk L R ->
       @task_response_time_bound Task Job H3 H2 H1 (exceedance_proc_state Job) arr_seq sched tsk R
```

## Lean

```lean
@Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive.uniprocessor_response_time_bound_fully_nonpreemptive_fp : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [inst_6 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (ts : List Task),
  Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
          Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule sched →
            ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
              Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
                Prosa.Model.Priority.Definitions.transitive_task_priorities FP →
                  Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq sched FP →
                    ∀ (e : Prosa.Behavior.Job.work) (tsk : Task),
                      decide (tsk ∈ ts) = true →
                        (∀ (j : Job) (t1 t2 : Prosa.Behavior.Time.instant),
                            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                              Prosa.Model.Task.Concept.job_of_task tsk j = true →
                                Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j
                                    t1 t2 →
                                  ∑ t ∈ Finset.Ico t1 t2,
                                      (Prosa.Analysis.Facts.Model.IdealUniExceed.is_exceedance_exec (sched t)).toNat ≤
                                    e) →
                          ∀ (L : Prosa.Behavior.Time.duration),
                            Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive.busy_window_recurrence_solution ts e tsk L →
                              ∀ (R : Prosa.Behavior.Time.duration),
                                Prosa.Results.Rta.Exc.Fp.FullyNonpreemptive.rta_recurrence_solution ts e tsk L R →
                                  Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched tsk R
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_uniprocessor_response_time_bound_fully_nonpreemptive_fp
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13)
         (ts : List Task),
       Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence Task
         inst_3
         inst_6
         inst_9 Job
         inst_13
         inst_16
         inst_20
         inst_23 ts arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_13
                   (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
                      inst_13),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_13
         inst_23
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_13)
         sched inst_20
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance_inst8 Job
            inst_13 Task
            inst_3
            inst_16
            inst_23
            inst_20
            (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
               inst_13)
            arr_seq)
         arr_seq ->
       Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
         inst_13
         inst_23
         inst_20
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_13)
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance_inst8 Job
            inst_13 Task
            inst_3
            inst_16
            inst_23
            inst_20
            (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
               inst_13)
            arr_seq)
         arr_seq sched ->
       Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule_inst4 Job
         inst_13
         inst_20
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_13)
         sched ->
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Priority_Definitions_transitive_task_priorities Task
         inst_3 FP ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst8 Task
         inst_3 Job
         inst_13
         inst_16
         inst_23
         inst_20
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_13)
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job
            inst_13
            inst_20)
         (Prosa_Model_Readiness_Sequential_sequential_ready_instance_inst8 Job
            inst_13 Task
            inst_3
            inst_16
            inst_23
            inst_20
            (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
               inst_13)
            arr_seq)
         arr_seq sched FP ->
       forall (e : Prosa_Behavior_Job_work) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       (forall (j : Job) (t1 t2 : Prosa_Behavior_Time_instant),
        Prosa_Behavior_Arrival_sequence_arrives_in Job
          inst_13 arr_seq j ->
        @eq Bool
          (Prosa_Model_Task_Concept_job_of_task Job
             inst_13 Task
             inst_3
             inst_16 tsk j)
          Bool_true ->
        Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix_inst4 Job
          inst_13
          inst_23
          inst_20
          (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
             inst_13)
          arr_seq sched
          (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
             inst_13 Task
             inst_3
             inst_16 FP)
          j t1 t2 ->
        LE_le_inst1 Nat instLENat
          (List_foldr_inst3 Nat Nat Nat_add 0
             (List_map_inst3 Nat Nat
                (fun t : Nat =>
                 Bool_toNat
                   (Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec Job
                      inst_13
                      (sched t)))
                (List_range' t1 (Nat_sub t2 t1) 1)))
          e) ->
       forall L : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_busy_window_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts FP e tsk L ->
       forall R : Prosa_Behavior_Time_duration,
       Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_rta_recurrence_solution Task
         inst_3
         inst_6
         inst_9 ts FP e tsk L R ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8 Task
         inst_3 Job
         inst_13
         inst_23
         inst_20
         inst_16
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_13)
         arr_seq sched tsk R
```
