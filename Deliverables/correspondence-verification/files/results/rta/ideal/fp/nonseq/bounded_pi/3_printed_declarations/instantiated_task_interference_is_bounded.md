# `instantiated_task_interference_is_bounded`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_task_interference_is_bounded`
- Lean: `Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.instantiated_task_interference_is_bounded`
- Certificate: `instantiated_task_interference_is_bounded_correspondence`

## Official Rocq

```coq
instantiated_task_interference_is_bounded :
forall {Task : TaskType} {H : TaskCost Task} {MaxArrivals0 : MaxArrivals Task} {Job : JobType}
  {H1 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job}
  {JobReady0 : @JobReady Job (ideal.processor_state Job) Cost Arrival} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
@arrivals_have_valid_job_costs Task H Job H1 Cost arr_seq ->
forall {FP : FP_policy Task},
@reflexive_task_priorities Task FP ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost JobReady0 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H1 arr_seq MaxArrivals0 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall priority_inversion_bound : duration,
@priority_inversion_is_bounded_by Task Job H1 Arrival Cost (ideal.processor_state Job) arr_seq sched
  (@FP_to_JLFP Job Task H1 FP) tsk (@constant duration duration priority_inversion_bound) ->
forall L : duration,
is_true (0 < L) ->
L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk L ->
@job_interference_is_bounded_by Job Task H1 Arrival Cost (ideal.processor_state Job) arr_seq sched tsk
  (@ideal_jlfp_interference Task Job H1 arr_seq FP sched)
  (@ideal_jlfp_interfering_workload Task Job H1 Cost arr_seq FP sched)
  (@IBF Task H MaxArrivals0 FP ts tsk priority_inversion_bound)
  (@relative_arrival_time_of_job_is_A Job Arrival Cost (ideal.processor_state Job) sched
     (@ideal_jlfp_interference Task Job H1 arr_seq FP sched)
     (@ideal_jlfp_interfering_workload Task Job H1 Cost arr_seq FP sched))

instantiated_task_interference_is_bounded is not universe polymorphic
Arguments instantiated_task_interference_is_bounded {Task H MaxArrivals0 Job H1 Arrival Cost JobReady0}
  arr_seq H_valid_arrival_sequence H_valid_job_cost {FP} H_priority_is_reflexive 
  sched H_sched_valid ts%seq_scope H_all_jobs_from_taskset H_is_arrival_curve tsk 
  H_tsk_in_ts priority_inversion_bound H_priority_inversion_is_bounded L H_L_positive 
  H_fixed_point t1 t2 Δ j _ _ _ _ _ X _
instantiated_task_interference_is_bounded is opaque
Expands to: Constant prosa.results.rta.ideal.fp.nonseq.bounded_pi.instantiated_task_interference_is_bounded
Declared in library prosa.results.rta.ideal.fp.nonseq.bounded_pi, line 276, characters 8-49
@instantiated_task_interference_is_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (MaxArrivals0 : MaxArrivals Task) 
         (Job : JobType) (H1 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (JobReady0 : @JobReady Job (ideal.processor_state Job) Cost Arrival)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H1 Cost arr_seq ->
       forall FP : FP_policy Task,
       @reflexive_task_priorities Task FP ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost JobReady0 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq MaxArrivals0 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall priority_inversion_bound : duration,
       @priority_inversion_is_bounded_by Task Job H1 Arrival Cost (ideal.processor_state Job) arr_seq sched
         (@FP_to_JLFP Job Task H1 FP) tsk (@constant duration duration priority_inversion_bound) ->
       forall L : duration,
       is_true (0 < L) ->
       L = priority_inversion_bound + @total_hep_request_bound_function_FP Task H MaxArrivals0 ts FP tsk L ->
       @job_interference_is_bounded_by Job Task H1 Arrival Cost (ideal.processor_state Job) arr_seq sched tsk
         (@ideal_jlfp_interference Task Job H1 arr_seq FP sched)
         (@ideal_jlfp_interfering_workload Task Job H1 Cost arr_seq FP sched)
         (@IBF Task H MaxArrivals0 FP ts tsk priority_inversion_bound)
         (@relative_arrival_time_of_job_is_A Job Arrival Cost (ideal.processor_state Job) sched
            (@ideal_jlfp_interference Task Job H1 arr_seq FP sched)
            (@ideal_jlfp_interfering_workload Task Job H1 Cost arr_seq FP sched))
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.instantiated_task_interference_is_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  [inst_7 : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task),
        Prosa.Model.Priority.Definitions.reflexive_task_priorities FP →
          ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
            Prosa.Behavior.Ready.valid_schedule sched arr_seq →
              ∀ (ts : List Task),
                Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                  Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                    ∀ (tsk : Task),
                      decide (tsk ∈ ts) = true →
                        ∀ (priority_inversion_bound : Prosa.Behavior.Time.duration),
                          Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by arr_seq sched
                              tsk (Prosa.Util.Notation.constant priority_inversion_bound) →
                            ∀ (L : Prosa.Behavior.Time.duration),
                              0 < L →
                                L =
                                    priority_inversion_bound +
                                      Prosa.Analysis.Definitions.RequestBoundFunction.total_hep_request_bound_function_FP
                                        ts tsk L →
                                  Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by arr_seq sched tsk
                                    (Prosa.Results.Rta.Ideal.Fp.Nonseq.BoundedPi.IBF ts tsk priority_inversion_bound)
                                    (Prosa.Analysis.Abstract.AbstractRta.relative_arrival_time_of_job_is_A sched)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_instantiated_task_interference_is_bounded
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
          Prosa_Behavior_Ready_JobReady_inst4 Job
            inst_7
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            inst_23
            inst_20)
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
       forall
         FP : Prosa_Model_Priority_Definitions_FP_policy Task
                inst_3,
       Prosa_Model_Priority_Definitions_reflexive_task_priorities Task
         inst_3 FP ->
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
         inst_26 arr_seq ->
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
       forall priority_inversion_bound : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_16
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_7 Task
            inst_3
            inst_16 FP)
         tsk
         (Prosa_Util_Notation_constant_inst3 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            priority_inversion_bound) ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) priority_inversion_bound
            (Prosa_Analysis_Definitions_RequestBoundFunction_total_hep_request_bound_function_FP Task
               inst_3
               inst_10
               inst_13 ts FP tsk L)) ->
       Prosa_Analysis_Abstract_Definitions_job_interference_is_bounded_by_inst4 Job
         inst_7
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_7 Task
               inst_3
               inst_16 FP))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_23 arr_seq sched
            (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
               inst_7 Task
               inst_3
               inst_16 FP))
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched Task inst_3
         inst_16 tsk
         (Prosa_Results_Rta_Ideal_Fp_Nonseq_BoundedPi_IBF Task
            inst_3
            inst_10
            inst_13 FP ts tsk
            priority_inversion_bound)
         (Prosa_Analysis_Abstract_AbstractRta_relative_arrival_time_of_job_is_A_inst4 Job
            inst_7
            inst_20
            inst_23
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_7)
            sched
            (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
               inst_7 arr_seq sched
               (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
                  inst_7 Task
                  inst_3
                  inst_16 FP))
            (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
               inst_7
               inst_23 arr_seq sched
               (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
                  inst_7 Task
                  inst_3
                  inst_16 FP)))
```
