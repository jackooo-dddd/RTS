# `IBF_correct`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fifo.bounded_nps.IBF_correct`
- Lean: `Prosa.Results.Rta.Ideal.Fifo.BoundedNps.IBF_correct`
- Certificate: `IBF_correct_correspondence`

## Official Rocq

```coq
IBF_correct :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H2 : JobTask Job Task} {H3 : JobArrival Job} {H4 : JobCost Job} {H5 : JobPreemptable Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job H3 (ideal.processor_state Job) sched H4
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
@valid_preemption_model Job H4 H5 (ideal.processor_state Job) arr_seq sched ->
@priority_driven.respects_JLFP_policy_at_preemption_point Job H3 H4 (ideal.processor_state Job) H5
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched 
  (@fifo.FIFO Job H3) ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H0 ts L ->
@job_interference_is_bounded_by Job Task H2 H3 H4 (ideal.processor_state Job) arr_seq sched tsk
  (@ideal_jlfp_interference Job H3 arr_seq sched) (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched)
  (fun A : duration =>
   fun=> \sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A + 1) - @task_cost Task H tsk)
  (@relative_arrival_time_of_job_is_A Job H3 H4 (ideal.processor_state Job) sched
     (@ideal_jlfp_interference Job H3 arr_seq sched)
     (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched))

IBF_correct is not universe polymorphic
Arguments IBF_correct {Task H H0 Job H2 H3 H4 H5} arr_seq H_valid_arrival_sequence 
  H_valid_job_cost ts%seq_scope H_all_jobs_from_taskset H_is_arrival_curve H_valid_arrival_curve 
  tsk H_tsk_in_ts sched H_valid_schedule H_valid_preemption_model H_respects_policy_at_preemption_point 
  L H_L_positive H_fixed_point t1 t2 Δ j _ _ _ _ _ X _
IBF_correct is opaque
Expands to: Constant prosa.results.rta.ideal.fifo.bounded_nps.IBF_correct
Declared in library prosa.results.rta.ideal.fifo.bounded_nps, line 297, characters 8-19
@IBF_correct
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job) (H5 : JobPreemptable Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H2 arr_seq H0 ts ->
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H0) ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job H3 (ideal.processor_state Job) sched H4
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq ->
       @valid_preemption_model Job H4 H5 (ideal.processor_state Job) arr_seq sched ->
       @priority_driven.respects_JLFP_policy_at_preemption_point Job H3 H4 (ideal.processor_state Job) H5
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H3 H4) arr_seq sched
         (@fifo.FIFO Job H3) ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H0 ts L ->
       @job_interference_is_bounded_by Job Task H2 H3 H4 (ideal.processor_state Job) arr_seq sched tsk
         (@ideal_jlfp_interference Job H3 arr_seq sched)
         (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched)
         (fun A : duration =>
          fun=> \sum_(tsko <- ts) @task_request_bound_function Task H H0 tsko (A + 1) - @task_cost Task H tsk)
         (@relative_arrival_time_of_job_is_A Job H3 H4 (ideal.processor_state Job) sched
            (@ideal_jlfp_interference Job H3 arr_seq sched)
            (@ideal_jlfp_interfering_workload Job H3 H4 arr_seq sched))
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fifo.BoundedNps.IBF_correct : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (ts : List Task),
        Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
            Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts
                Prosa.Model.Task.Arrival.Curves.max_arrivals →
              ∀ (tsk : Task),
                decide (tsk ∈ ts) = true →
                  ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
                    Prosa.Behavior.Ready.valid_schedule sched arr_seq →
                      Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
                        Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                            (Prosa.Model.Priority.Fifo.FIFO Job) →
                          ∀ (L : Prosa.Behavior.Time.duration),
                            0 < L →
                              L = Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L →
                                Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk
                                  (fun A x =>
                                    (Prosa.Util.Sum.sumSeq ts fun tsko =>
                                        Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsko
                                          (A + 1)) -
                                      Prosa.Model.Task.Concept.task_cost tsk)
                                  (Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A sched)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fifo_BoundedNps_IBF_correct
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_26 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_20 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_23 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_7
         inst_16 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_16 arr_seq
         inst_13 ts ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_13) ->
       forall tsk : Task,
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
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_7
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_7),
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_7
         inst_20
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         sched inst_23
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_20
            inst_23)
         arr_seq ->
       Prosa_Model_Preemption_Parameter_valid_preemption_model_inst4 Job
         inst_7
         inst_23
         inst_26
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_7
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         inst_26
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_20
            inst_23)
         arr_seq sched
         (Prosa_Model_Priority_Fifo_FIFO Job
            inst_7
            inst_20) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_13 ts L) ->
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_20))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_23 arr_seq sched
            (Prosa_Model_Priority_Fifo_FIFO Job
               inst_7
               inst_20))
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched Task inst_3
         inst_16 tsk
         (fun A _ : Prosa_Behavior_Time_duration =>
          HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
            (Prosa_Util_Sum_sumSeq Task ts
               (fun tsko : Task =>
                Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_10
                  inst_13 tsko
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
            (Prosa_Model_Task_Concept_TaskCost_task_cost Task
               inst_3
               inst_10 tsk))
         (Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A_inst4 Job
            inst_7
            inst_20
            inst_23
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            sched
            (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
               inst_7 arr_seq sched
               (Prosa_Model_Priority_Fifo_FIFO Job
                  inst_7
                  inst_20))
            (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
               inst_7
               inst_23 arr_seq sched
               (Prosa_Model_Priority_Fifo_FIFO Job
                  inst_7
                  inst_20)))
```
