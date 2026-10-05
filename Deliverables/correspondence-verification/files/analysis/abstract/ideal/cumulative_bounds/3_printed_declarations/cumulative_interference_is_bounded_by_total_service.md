# `cumulative_interference_is_bounded_by_total_service`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_interference_is_bounded_by_total_service`
- Lean: `Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_interference_is_bounded_by_total_service`
- Certificate: `cumulative_interference_is_bounded_by_total_service_correspondence`

## Official Rocq

```coq
cumulative_interference_is_bounded_by_total_service :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job} 
  {H1 : JobCost Job} {JR : @JobReady Job (ideal.processor_state Job) H1 H0} {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H0 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job H0 (ideal.processor_state Job) sched H1 JR arr_seq ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H tsk j) ->
is_true (@job_cost_positive Job H1 j) ->
forall t1 t2 : duration,
@definitions.busy_interval Job H0 H1 (ideal.processor_state Job) sched
  (@ideal_jlfp_interference Job JLFP arr_seq sched)
  (@ideal_jlfp_interfering_workload Job H1 JLFP arr_seq sched) j t1 t2 ->
forall Δ : duration,
is_true
  (@cumulative_another_task_hep_job_interference Task Job H (ideal.processor_state Job) arr_seq sched JLFP j
     t1 (t1 + Δ) <=
   @service_of_jobs Job (ideal.processor_state Job) sched ((@another_task_hep_job Task Job H JLFP)^~ j)
     (@arrivals_between Job arr_seq t1 (t1 + Δ)) t1 (t1 + Δ))

cumulative_interference_is_bounded_by_total_service is not universe polymorphic
Arguments cumulative_interference_is_bounded_by_total_service {Task Job H H0 H1 JR JLFP}
  H_policy_is_reflexive arr_seq H_valid_arrival_sequence sched H_valid_schedule tsk 
  j H_j_arrives H_job_of_tsk H_job_cost_positive t1 t2 H_busy_interval Δ
cumulative_interference_is_bounded_by_total_service is opaque
Expands to: Constant
            prosa.analysis.abstract.ideal.cumulative_bounds.cumulative_interference_is_bounded_by_total_service
Declared in library prosa.analysis.abstract.ideal.cumulative_bounds, line 90, characters 8-59
@cumulative_interference_is_bounded_by_total_service
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (H1 : JobCost Job) (JR : @JobReady Job (ideal.processor_state Job) H1 H0) 
         (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H0 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job H0 (ideal.processor_state Job) sched H1 JR arr_seq ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H tsk j) ->
       is_true (@job_cost_positive Job H1 j) ->
       forall t1 t2 : duration,
       @definitions.busy_interval Job H0 H1 (ideal.processor_state Job) sched
         (@ideal_jlfp_interference Job JLFP arr_seq sched)
         (@ideal_jlfp_interfering_workload Job H1 JLFP arr_seq sched) j t1 t2 ->
       forall Δ : duration,
       is_true
         (@cumulative_another_task_hep_job_interference Task Job H (ideal.processor_state Job) arr_seq sched
            JLFP j t1 (t1 + Δ) <=
          @service_of_jobs Job (ideal.processor_state Job) sched
            ((@another_task_hep_job Task Job H JLFP)^~ j) (@arrivals_between Job arr_seq t1 (t1 + Δ)) t1
            (t1 + Δ))
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.CumulativeBounds.cumulative_interference_is_bounded_by_total_service : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  [JR : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
  [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ (tsk : Task) (j : Job),
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                Prosa.Model.Task.Concept.job_of_task tsk j = true →
                  Prosa.Model.Job.Properties.job_cost_positive j = true →
                    ∀ (t1 t2 : Prosa.Behavior.Time.duration),
                      Prosa.Analysis.Abstract.Definitions.busy_interval sched j t1 t2 →
                        ∀ (Δ : Prosa.Behavior.Time.duration),
                          Prosa.Analysis.Definitions.Interference.cumulative_another_task_hep_job_interference arr_seq
                              sched j t1 (t1 + Δ) ≤
                            Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched
                              (fun jo => Prosa.Model.Priority.Definitions.another_task_hep_job jo j)
                              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ)) t1 (t1 + Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_CumulativeBounds_cumulative_interference_is_bounded_by_total_service
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (JR : Prosa_Behavior_Ready_JobReady_inst4 Job
                 inst_7
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_7)
                 inst_17
                 inst_14)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_7),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_7 JLFP ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_14
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_17 JR
         arr_seq ->
       forall (tsk : Task) (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_17 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_Definitions_busy_interval_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            JLFP)
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_17 arr_seq
            sched JLFP)
         inst_14
         inst_17
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched j t1 t2 ->
       forall _UU0394_ : Prosa_Behavior_Time_duration,
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Definitions_Interference_cumulative_another_task_hep_job_interference_inst8 Task
            inst_3 Job
            inst_7
            inst_10
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            arr_seq sched JLFP j t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
               _UU0394_))
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            sched
            (fun jo : Job =>
             Prosa_Model_Priority_Definitions_another_task_hep_job Task
               inst_3 Job
               inst_7
               inst_10 JLFP jo j)
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
                  _UU0394_))
            t1
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
               _UU0394_))
```
