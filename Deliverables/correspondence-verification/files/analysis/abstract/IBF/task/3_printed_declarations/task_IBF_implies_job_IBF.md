# `task_IBF_implies_job_IBF`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.IBF.task.task_IBF_implies_job_IBF`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.task_IBF_implies_job_IBF`
- Certificate: `task_IBF_implies_job_IBF_correspondence`

## Official Rocq

```coq
task_IBF_implies_job_IBF :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H1 : JobArrival Job} {jc : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_service_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
@completed_jobs_dont_execute Job PState sched jc ->
@arrivals_have_valid_job_costs Task H Job H0 jc arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {H2 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H0 arr_seq H2 ts ->
forall {H3 : Interference Job} {H4 : InterferingWorkload Job},
@work_conserving Job H1 jc PState arr_seq sched H3 H4 ->
@sequential_tasks Job Task H0 H1 jc PState arr_seq sched ->
@interference_and_workload_consistent_with_sequential_tasks Task Job H0 H1 jc PState arr_seq sched tsk H3 H4 ->
forall task_IBF : duration -> duration -> duration,
@task_interference_is_bounded_by Job Task H0 H1 jc PState arr_seq sched tsk H3 H4 task_IBF ->
@job_interference_is_bounded_by Job Task H0 H1 jc PState arr_seq sched tsk H3 H4
  (fun A R : duration =>
   @task_request_bound_function Task H H2 tsk (A + 1) - @task_cost Task H tsk + task_IBF A R)
  (@relative_arrival_time_of_job_is_A Job H1 jc PState sched H3 H4)

task_IBF_implies_job_IBF is not universe polymorphic
Arguments task_IBF_implies_job_IBF {Task H Job H0 H1 jc PState} H_uniprocessor_proc_model
  H_unit_service_proc_model arr_seq H_valid_arrival_sequence sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_job_cost ts%seq_scope 
  tsk H_tsk_in_ts {H2} H_is_arrival_curve {H3 H4} H_work_conserving H_sequential_tasks
  H_interference_and_workload_consistent_with_sequential_tasks task_IBF%function_scope
  H_task_interference_is_bounded t1 t2 Δ j _ _ _ _ _ X _
task_IBF_implies_job_IBF is opaque
Expands to: Constant prosa.analysis.abstract.IBF.task.task_IBF_implies_job_IBF
Declared in library prosa.analysis.abstract.IBF.task, line 567, characters 8-32
@task_IBF_implies_job_IBF
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (jc : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_service_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       @completed_jobs_dont_execute Job PState sched jc ->
       @arrivals_have_valid_job_costs Task H Job H0 jc arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall H2 : MaxArrivals Task,
       @taskset_respects_max_arrivals Task Job H0 arr_seq H2 ts ->
       forall (H3 : Interference Job) (H4 : InterferingWorkload Job),
       @work_conserving Job H1 jc PState arr_seq sched H3 H4 ->
       @sequential_tasks Job Task H0 H1 jc PState arr_seq sched ->
       @interference_and_workload_consistent_with_sequential_tasks Task Job H0 H1 jc PState arr_seq sched tsk
         H3 H4 ->
       forall task_IBF : duration -> duration -> duration,
       @task_interference_is_bounded_by Job Task H0 H1 jc PState arr_seq sched tsk H3 H4 task_IBF ->
       @job_interference_is_bounded_by Job Task H0 H1 jc PState arr_seq sched tsk H3 H4
         (fun A R : duration =>
          @task_request_bound_function Task H H2 tsk (A + 1) - @task_cost Task H tsk + task_IBF A R)
         (@relative_arrival_time_of_job_is_A Job H1 jc PState sched H3 H4)
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.task_IBF_implies_job_IBF : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType} [inst_1 : DecidableEq Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_service_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                    ∀ (ts : List Task) (tsk : Task),
                      decide (tsk ∈ ts) = true →
                        ∀ [inst_6 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                            ∀ [inst_7 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                              [inst_8 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                              Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                                Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                                  Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks
                                      arr_seq sched tsk →
                                    ∀
                                      (task_IBF :
                                        Prosa.Behavior.Time.duration →
                                          Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                                      Prosa.Analysis.Abstract.IBF.Task.task_interference_is_bounded_by arr_seq sched tsk
                                          task_IBF →
                                        Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched
                                          tsk
                                          (fun A R =>
                                            Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                  tsk (A + 1) -
                                                Prosa.Model.Task.Concept.task_cost tsk +
                                              task_IBF A R)
                                          (Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A sched)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_task_IBF_implies_job_IBF
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
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
       Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job
         inst_3 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_3,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_17 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_3 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_17 PState sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_3 PState sched
         inst_20 ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_7
         inst_10 Job
         inst_3
         inst_13
         inst_20 arr_seq ->
       forall (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_7)
               (instLawfulBEq Task inst_7) tsk
               ts))
         Bool_true ->
       forall
         inst_80 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_7,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_7 Job
         inst_3
         inst_13 arr_seq
         inst_80 ts ->
       forall
         (inst_89 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_3)
         (inst_92 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_3),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_3
         inst_89
         inst_92
         inst_17
         inst_20 PState arr_seq sched ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_13
         inst_17
         inst_20 PState arr_seq sched ->
       Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks Job
         inst_3 Task
         inst_7
         inst_13
         inst_17
         inst_20 PState arr_seq sched tsk
         inst_89
         inst_92 ->
       forall
         task_IBF : Prosa_Behavior_Time_duration ->
                    Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_IBF_Task_task_interference_is_bounded_by Job
         inst_3 Task
         inst_7
         inst_13
         inst_17
         inst_20 PState arr_seq sched tsk
         inst_89
         inst_92 task_IBF ->
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by Job
         inst_3
         inst_89
         inst_92
         inst_17
         inst_20 PState arr_seq sched Task
         inst_7
         inst_13 tsk
         (fun A R : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_7
                  inst_10
                  inst_80 tsk
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_7
                  inst_10 tsk))
            (task_IBF A R))
         (Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A Job
            inst_3
            inst_17
            inst_20 PState sched
            inst_89
            inst_92)
```
