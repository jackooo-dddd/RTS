# `instantiated_task_interference_is_bounded`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.rta.ideal.gel.bounded_pi.instantiated_task_interference_is_bounded`
- Lean: `Prosa.Results.Rta.Ideal.Gel.BoundedPi.instantiated_task_interference_is_bounded`
- Certificate: `instantiated_task_interference_is_bounded_correspondence`

## Official Rocq

```coq
instantiated_task_interference_is_bounded :
forall {Task : TaskType} {H : TaskCost Task} {H2 : MaxArrivals Task} {Job : JobType} 
  {H3 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job} {H5 : gel.PriorityPoint Task}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
  (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
@arrivals_have_valid_job_costs Task H Job H3 Cost arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H3 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H3 arr_seq H2 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
forall priority_inversion_bound : duration -> duration,
@priority_inversion.priority_inversion_is_bounded_by Task Job H3 Arrival Cost (ideal.processor_state Job)
  arr_seq sched (@gel.GEL Job Task H5 Arrival H3) tsk priority_inversion_bound ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H2 ts L ->
@task_interference_is_bounded_by Job Task H3 Arrival Cost (ideal.processor_state Job) arr_seq sched tsk
  (@ideal_jlfp_interference Task Job H3 Arrival H5 arr_seq sched)
  (@ideal_jlfp_interfering_workload Task Job H3 Arrival Cost H5 arr_seq sched)
  (fun A R : duration =>
   priority_inversion_bound A +
   (fun A0 Δ : duration =>
    \sum_(tsk_o <- ts | tsk_o != tsk)
       @task_request_bound_function Task H H2 tsk_o
         (minn
            (ssrint.absz
               (@order.Order.max ssrnum.ring_display
                  (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                     ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                  (@ssralg.GRing.zero
                     (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                        ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                  ((fun (tsk_o0 : Equality.sort Task) (A1 : instant) =>
                    @ssralg.GRing.add
                      (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                         ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                      (@ssralg.GRing.add
                         (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                            ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                         (@ssralg.GRing.natmul
                            (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                               ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                            (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                            (A1 + 1))
                         (@gel.task_priority_point Task H5 tsk))
                      (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                         (@gel.task_priority_point Task H5 tsk_o0)))
                     tsk_o A0)))
            Δ))
     A R)

instantiated_task_interference_is_bounded is not universe polymorphic
Arguments instantiated_task_interference_is_bounded {Task H H2 Job H3 Arrival Cost H5} 
  arr_seq H_valid_arrival_sequence sched H_sched_valid H_valid_job_cost ts%seq_scope 
  H_all_jobs_from_taskset H_is_arrival_curve tsk H_tsk_in_ts priority_inversion_bound%function_scope
  H_priority_inversion_is_bounded L H_L_positive H_fixed_point t1 t2 Δ j _ _ _ _ 
  _ X _
instantiated_task_interference_is_bounded is opaque
Expands to: Constant prosa.results.rta.ideal.gel.bounded_pi.instantiated_task_interference_is_bounded
Declared in library prosa.results.rta.ideal.gel.bounded_pi, line 226, characters 12-53
@instantiated_task_interference_is_bounded
     : forall (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (Job : JobType)
         (H3 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H5 : gel.PriorityPoint Task) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @valid_schedule Job Arrival (ideal.processor_state Job) sched Cost
         (@basic.basic_ready_instance Job (ideal.processor_state Job) Arrival Cost) arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H3 Cost arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H3 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H3 arr_seq H2 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       forall priority_inversion_bound : duration -> duration,
       @priority_inversion.priority_inversion_is_bounded_by Task Job H3 Arrival Cost
         (ideal.processor_state Job) arr_seq sched (@gel.GEL Job Task H5 Arrival H3) tsk
         priority_inversion_bound ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H2 ts L ->
       @task_interference_is_bounded_by Job Task H3 Arrival Cost (ideal.processor_state Job) arr_seq sched
         tsk (@ideal_jlfp_interference Task Job H3 Arrival H5 arr_seq sched)
         (@ideal_jlfp_interfering_workload Task Job H3 Arrival Cost H5 arr_seq sched)
         (fun A R : duration =>
          priority_inversion_bound A +
          \sum_(tsk_o <- ts | tsk_o != tsk)
             @task_request_bound_function Task H H2 tsk_o
               (minn
                  (ssrint.absz
                     (@order.Order.max ssrnum.ring_display
                        (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
                           ssrint.ssrint_int__canonical__Num_POrderedZmodule)
                        (@ssralg.GRing.zero
                           (ssrnum.Num.POrderedZmodule.Exports.Num_POrderedZmodule__to__GRing_Nmodule
                              ssrint.ssrint_int__canonical__Num_POrderedZmodule))
                        (@ssralg.GRing.add
                           (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                              ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                           (@ssralg.GRing.add
                              (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                 ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                              (@ssralg.GRing.natmul
                                 (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                                    ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                                 (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) 
                                 (A + 1))
                              (@gel.task_priority_point Task H5 tsk))
                           (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                              (@gel.task_priority_point Task H5 tsk_o)))))
                  R))
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Gel.BoundedPi.instantiated_task_interference_is_bounded : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  [inst_7 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.valid_schedule sched arr_seq →
        Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
          ∀ (ts : List Task),
            Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
              Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                ∀ (tsk : Task),
                  decide (tsk ∈ ts) = true →
                    ∀ (priority_inversion_bound : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
                      Prosa.Analysis.Definitions.PriorityInversion.priority_inversion_is_bounded_by arr_seq sched tsk
                          priority_inversion_bound →
                        ∀ (L : Prosa.Behavior.Time.duration),
                          0 < L →
                            L = Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L →
                              Prosa.Analysis.Abstract.IBF.Task.task_interference_is_bounded_by arr_seq sched tsk
                                fun A R =>
                                priority_inversion_bound A +
                                  Prosa.Util.Sum.sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
                                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk_o
                                      (min
                                        (max 0
                                            (↑(A + 1) + Prosa.Model.Priority.Gel.task_priority_point tsk -
                                              Prosa.Model.Priority.Gel.task_priority_point tsk_o)).natAbs
                                        R)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_instantiated_task_interference_is_bounded
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
          Prosa_Model_Priority_Gel_PriorityPoint Task
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_20 arr_seq ->
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
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       forall priority_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration,
       Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by_inst8 Task
         inst_3 Job
         inst_7
         inst_16
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched
         (Prosa_Model_Priority_Gel_GEL Job
            inst_7 Task
            inst_3
            inst_26
            inst_20
            inst_16)
         tsk priority_inversion_bound ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_13 ts L) ->
       Prosa_Analysis_Abstract_IBF_Task_task_interference_is_bounded_by_inst8 Job
         inst_7 Task
         inst_3
         inst_16
         inst_20
         inst_23
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_7)
         arr_seq sched tsk
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interference Job
            inst_7 arr_seq sched
            (Prosa_Model_Priority_Gel_GEL Job
               inst_7 Task
               inst_3
               inst_26
               inst_20
               inst_16))
         (Prosa_Analysis_Abstract_Ideal_IwInstantiation_ideal_jlfp_interfering_workload Job
            inst_7
            inst_23 arr_seq sched
            (Prosa_Model_Priority_Gel_GEL Job
               inst_7 Task
               inst_3
               inst_26
               inst_20
               inst_16))
         (fun A R : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (priority_inversion_bound A)
            (Prosa_Util_Sum_sumFiltered Task ts
               (fun tsk_o : Task =>
                Decidable_decide (Ne Task tsk_o tsk)
                  (instDecidableNot (@eq Task tsk_o tsk)
                     (inst_3 tsk_o tsk)))
               (fun tsk_o : Task =>
                Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_10
                  inst_13 tsk_o
                  (Min_min_inst1 Prosa_Behavior_Time_duration instMinNat
                     (Int_natAbs
                        (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                           (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int
                              (instHSub_inst1 Int Int_instSub)
                              (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int
                                 (instHAdd_inst1 Int Int_instAdd)
                                 (Nat_cast_inst1 Int instNatCastInt
                                    (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat
                                       Prosa_Behavior_Time_duration
                                       (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                                       (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                                 (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                    inst_3
                                    inst_26
                                    tsk))
                              (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                 inst_3
                                 inst_26
                                 tsk_o))))
                     R))))
```
