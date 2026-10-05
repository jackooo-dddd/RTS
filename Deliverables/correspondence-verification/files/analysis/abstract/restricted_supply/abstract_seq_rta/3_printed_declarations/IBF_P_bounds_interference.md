# `IBF_P_bounds_interference`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.abstract_seq_rta.IBF_P_bounds_interference`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.IBF_P_bounds_interference`
- Certificate: `IBF_P_bounds_interference_correspondence`

## Official Rocq

```coq
IBF_P_bounds_interference :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H1 : JobTask Job Task} 
  {H2 : JobArrival Job} {jc : JobCost Job} {PState : ProcessorState Job},
@uniprocessor_model Job PState ->
@unit_supply_proc_model Job PState ->
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job H2 arr_seq ->
forall sched : @schedule Job PState,
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H2 PState sched ->
@completed_jobs_dont_execute Job PState sched jc ->
@arrivals_have_valid_job_costs Task H Job H1 jc arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall {H4 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H1 arr_seq H4 ts ->
forall {H5 : Interference Job} {H6 : InterferingWorkload Job},
@work_conserving Job H2 jc PState arr_seq sched H5 H6 ->
@sequential_tasks Job Task H1 H2 jc PState arr_seq sched ->
@interference_and_workload_consistent_with_sequential_tasks Task Job H1 H2 jc PState arr_seq sched tsk H5 H6 ->
forall task_intra_IBF : duration -> duration -> duration,
@task_intra_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H5 H6 task_intra_IBF ->
@intra_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H5 H6
  (fun A Δ : duration =>
   @task_request_bound_function Task H H4 tsk (A + 1) - @task_cost Task H tsk + task_intra_IBF A Δ)

IBF_P_bounds_interference is not universe polymorphic
Arguments IBF_P_bounds_interference {Task H Job H1 H2 jc PState} H_uniprocessor_proc_model
  H_unit_supply_proc_model arr_seq H_valid_arrivals sched H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_job_cost ts%seq_scope 
  tsk H_tsk_in_ts {H4} H_is_arrival_curve {H5 H6} H_work_conserving H_sequential_tasks
  H_interference_and_workload_consistent_with_sequential_tasks task_intra_IBF%function_scope
  H_interference_inside_reservation_is_bounded t1 t2 Δ j _ _ _ _ _ X _
IBF_P_bounds_interference is opaque
Expands to: Constant prosa.analysis.abstract.restricted_supply.abstract_seq_rta.IBF_P_bounds_interference
Declared in library prosa.analysis.abstract.restricted_supply.abstract_seq_rta, line 165, characters 10-35
@IBF_P_bounds_interference
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H1 : JobTask Job Task)
         (H2 : JobArrival Job) (jc : JobCost Job) (PState : ProcessorState Job),
       @uniprocessor_model Job PState ->
       @unit_supply_proc_model Job PState ->
       forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job H2 arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H2 PState sched ->
       @completed_jobs_dont_execute Job PState sched jc ->
       @arrivals_have_valid_job_costs Task H Job H1 jc arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall H4 : MaxArrivals Task,
       @taskset_respects_max_arrivals Task Job H1 arr_seq H4 ts ->
       forall (H5 : Interference Job) (H6 : InterferingWorkload Job),
       @work_conserving Job H2 jc PState arr_seq sched H5 H6 ->
       @sequential_tasks Job Task H1 H2 jc PState arr_seq sched ->
       @interference_and_workload_consistent_with_sequential_tasks Task Job H1 H2 jc PState arr_seq sched tsk
         H5 H6 ->
       forall task_intra_IBF : duration -> duration -> duration,
       @task_intra_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H5 H6 task_intra_IBF ->
       @intra_interference_is_bounded_by Job Task H1 H2 jc PState arr_seq sched tsk H5 H6
         (fun A Δ : duration =>
          @task_request_bound_function Task H H4 tsk (A + 1) - @task_cost Task H tsk + task_intra_IBF A Δ)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.IBF_P_bounds_interference : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_4 : Prosa.Behavior.Job.JobArrival Job]
  [jc : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.uniprocessor_model PState →
    Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
      ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
        Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
          ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
            Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
              Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
                Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
                  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
                    ∀ (ts : List Task) (tsk : Task),
                      decide (tsk ∈ ts) = true →
                        ∀ [inst_5 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
                          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                            ∀ [inst_6 : Prosa.Analysis.Abstract.Definitions.Interference Job]
                              [inst_7 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job],
                              Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
                                Prosa.Model.Task.Sequentiality.sequential_tasks arr_seq sched →
                                  Prosa.Analysis.Abstract.IBF.Task.interference_and_workload_consistent_with_sequential_tasks
                                      arr_seq sched tsk →
                                    ∀
                                      (task_intra_IBF :
                                        Prosa.Behavior.Time.duration →
                                          Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                                      Prosa.Analysis.Abstract.IBF.SupplyTask.task_intra_interference_is_bounded_by
                                          arr_seq sched tsk task_intra_IBF →
                                        Prosa.Analysis.Abstract.IBF.Supply.intra_interference_is_bounded_by arr_seq
                                          sched tsk fun A Δ =>
                                          Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function
                                                tsk (A + 1) -
                                              Prosa.Model.Task.Concept.task_cost tsk +
                                            task_intra_IBF A Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_AbstractSeqRta_IBF_P_bounds_interference
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (jc : Prosa_Behavior_Job_JobCost Job
                 inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_uniprocessor_model Job
         inst_7 PState ->
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_7 PState ->
       forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                     inst_7,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_17
         arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState
         sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_17 PState
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute Job
         inst_7 PState
         sched jc ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_13 jc
         arr_seq ->
       forall (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       forall
         inst_79 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_13
         arr_seq
         inst_79 ts ->
       forall
         (inst_88 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_91 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_88
         inst_91
         inst_17 jc
         PState arr_seq sched ->
       Prosa_Model_Task_Sequentiality_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_13
         inst_17 jc
         PState arr_seq sched ->
       Prosa_Analysis_Abstract_IBF_Task_interference_and_workload_consistent_with_sequential_tasks Job
         inst_7 Task
         inst_3
         inst_13
         inst_17 jc
         PState arr_seq sched tsk
         inst_88
         inst_91 ->
       forall
         task_intra_IBF : Prosa_Behavior_Time_duration ->
                          Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_IBF_SupplyTask_task_intra_interference_is_bounded_by Job
         inst_7 Task
         inst_3
         inst_13
         inst_17 jc
         PState arr_seq sched tsk
         inst_88
         inst_91
         task_intra_IBF ->
       Prosa_Analysis_Abstract_IBF_Supply_intra_interference_is_bounded_by Job
         inst_7 Task
         inst_3
         inst_13
         inst_17 jc
         PState arr_seq sched tsk
         inst_88
         inst_91
         (fun A _UU0394_ : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_10
                  inst_79
                  tsk
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_3
                  inst_10
                  tsk))
            (task_intra_IBF A _UU0394_))
```
