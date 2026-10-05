# `total_workload_shorten_range`

- Kind (Rocq): Lemma
- Rocq: `prosa.results.rta.ideal.gel.bounded_pi.total_workload_shorten_range`
- Lean: `Prosa.Results.Rta.Ideal.Gel.BoundedPi.total_workload_shorten_range`
- Certificate: `total_workload_shorten_range_correspondence`

## Official Rocq

```coq
total_workload_shorten_range :
forall {Task : TaskType} {H : TaskCost Task} {H2 : MaxArrivals Task} {Job : JobType} 
  {H3 : JobTask Job Task} {Arrival : JobArrival Job} {Cost : JobCost Job} {H5 : gel.PriorityPoint Task}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job Arrival arr_seq ->
forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
forall L : duration,
is_true (0 < L) ->
L = @total_request_bound_function Task H H2 ts L ->
forall j : Equality.sort Job,
is_true (@job_of_task Job Task H3 tsk j) ->
is_true (@job_cost_positive Job Cost j) ->
forall t1 t2 Δ : duration,
is_true (t1 + Δ < t2) ->
forall tsk_o : Equality.sort Task,
is_true (tsk_o \in ts) ->
is_true (tsk_o != tsk) ->
is_true
  (@order.Order.le ssrnum.ring_display
     (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
        ssrint.ssrint_int__canonical__Num_POrderedZmodule)
     ((fun (tsk_o0 : Equality.sort Task) (A : instant) =>
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
               (A + 1))
            (@gel.task_priority_point Task H5 tsk))
         (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
            (@gel.task_priority_point Task H5 tsk_o0)))
        tsk_o (@job_arrival Job Arrival j - t1))
     (@ssralg.GRing.natmul
        (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
           (ssrnum.Num.NumDomain.Exports.join_Num_NumDomain_between_Num_POrderedZmodule_and_GRing_PzSemiRing
              ssrint.ssrint_int__canonical__Num_NumDomain))
        (ssralg.GRing.one
           (ssrnum.Num.NumDomain.Exports.join_Num_NumDomain_between_Num_POrderedZmodule_and_GRing_PzSemiRing
              ssrint.ssrint_int__canonical__Num_NumDomain))
        Δ)) ->
is_true
  (@workload_of_jobs Job Cost
     ((fun (tsk0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @hep_job Job (@gel.GEL Job Task H5 Arrival H3) jo j && (@job_task Job Task H3 jo == tsk0)) tsk_o)
     (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
   @workload_of_jobs Job Cost
     ((fun (tsk0 : Equality.sort Task) (jo : Equality.sort Job) =>
       @hep_job Job (@gel.GEL Job Task H5 Arrival H3) jo j && (@job_task Job Task H3 jo == tsk0)) tsk_o)
     (@arrivals_between Job arr_seq t1
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
                 (@ssralg.GRing.natmul
                    (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                       ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                    (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) t1)
                 ((fun (tsk_o0 : Equality.sort Task) (A : instant) =>
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
                           (A + 1))
                        (@gel.task_priority_point Task H5 tsk))
                     (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                        (@gel.task_priority_point Task H5 tsk_o0)))
                    tsk_o (@job_arrival Job Arrival j - t1)))))))

total_workload_shorten_range is not universe polymorphic
Arguments total_workload_shorten_range {Task H H2 Job H3 Arrival Cost H5} arr_seq 
  H_valid_arrival_sequence ts%seq_scope tsk H_tsk_in_ts L H_L_positive H_fixed_point 
  j H_job_of_tsk H_job_cost_positive t1 t2 Δ H_Δ_in_busy tsk_o H_tsko_in_ts H_neq 
  H_Δ_ge
total_workload_shorten_range is opaque
Expands to: Constant prosa.results.rta.ideal.gel.bounded_pi.total_workload_shorten_range
Declared in library prosa.results.rta.ideal.gel.bounded_pi, line 182, characters 12-40
@total_workload_shorten_range
     : forall (Task : TaskType) (H : TaskCost Task) (H2 : MaxArrivals Task) (Job : JobType)
         (H3 : JobTask Job Task) (Arrival : JobArrival Job) (Cost : JobCost Job)
         (H5 : gel.PriorityPoint Task) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job Arrival arr_seq ->
       forall (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       forall L : duration,
       is_true (0 < L) ->
       L = @total_request_bound_function Task H H2 ts L ->
       forall j : Equality.sort Job,
       is_true (@job_of_task Job Task H3 tsk j) ->
       is_true (@job_cost_positive Job Cost j) ->
       forall t1 t2 Δ : duration,
       is_true (t1 + Δ < t2) ->
       forall tsk_o : Equality.sort Task,
       is_true (tsk_o \in ts) ->
       is_true (tsk_o != tsk) ->
       is_true
         (@order.Order.le ssrnum.ring_display
            (ssrnum.Num.POrderedZmodule.Exports.join_Num_POrderedZmodule_between_GRing_Nmodule_and_Order_POrder
               ssrint.ssrint_int__canonical__Num_POrderedZmodule)
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
                     (@job_arrival Job Arrival j - t1 + 1))
                  (@gel.task_priority_point Task H5 tsk))
               (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                  (@gel.task_priority_point Task H5 tsk_o)))
            (@ssralg.GRing.natmul
               (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                  (ssrnum.Num.NumDomain.Exports.join_Num_NumDomain_between_Num_POrderedZmodule_and_GRing_PzSemiRing
                     ssrint.ssrint_int__canonical__Num_NumDomain))
               (ssralg.GRing.one
                  (ssrnum.Num.NumDomain.Exports.join_Num_NumDomain_between_Num_POrderedZmodule_and_GRing_PzSemiRing
                     ssrint.ssrint_int__canonical__Num_NumDomain))
               Δ)) ->
       is_true
         (@workload_of_jobs Job Cost
            (fun jo : Equality.sort Job =>
             @hep_job Job (@gel.GEL Job Task H5 Arrival H3) jo j && (@job_task Job Task H3 jo == tsk_o))
            (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
          @workload_of_jobs Job Cost
            (fun jo : Equality.sort Job =>
             @hep_job Job (@gel.GEL Job Task H5 Arrival H3) jo j && (@job_task Job Task H3 jo == tsk_o))
            (@arrivals_between Job arr_seq t1
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
                        (@ssralg.GRing.natmul
                           (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
                              ssrint.ssrint_int__canonical__GRing_PzSemiRing)
                           (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) t1)
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
                                 (@job_arrival Job Arrival j - t1 + 1))
                              (@gel.task_priority_point Task H5 tsk))
                           (@ssralg.GRing.opp ssrint.ssrint_int__canonical__GRing_Zmodule
                              (@gel.task_priority_point Task H5 tsk_o))))))))
```

## Lean

```lean
@Prosa.Results.Rta.Ideal.Gel.BoundedPi.total_workload_shorten_range : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.TaskCost Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobArrival Job]
  [inst_6 : Prosa.Behavior.Job.JobCost Job] [inst_7 : Prosa.Model.Priority.Gel.PriorityPoint Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : List Task) (tsk : Task),
      decide (tsk ∈ ts) = true →
        ∀ (L : Prosa.Behavior.Time.duration),
          0 < L →
            L = Prosa.Analysis.Definitions.RequestBoundFunction.total_request_bound_function ts L →
              ∀ (j : Job),
                Prosa.Model.Task.Concept.job_of_task tsk j = true →
                  Prosa.Model.Job.Properties.job_cost_positive j = true →
                    ∀ (t1 t2 Δ : Prosa.Behavior.Time.duration),
                      t1 + Δ < t2 →
                        ∀ (tsk_o : Task),
                          decide (tsk_o ∈ ts) = true →
                            decide (tsk_o ≠ tsk) = true →
                              decide
                                    (↑(Prosa.Behavior.Job.job_arrival j - t1 + 1) +
                                          Prosa.Model.Priority.Gel.task_priority_point tsk -
                                        Prosa.Model.Priority.Gel.task_priority_point tsk_o ≤
                                      ↑Δ) =
                                  true →
                                Prosa.Model.Aggregate.Workload.workload_of_jobs
                                    (fun jo =>
                                      Prosa.Model.Priority.Definitions.hep_job jo j &&
                                        decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
                                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ)) ≤
                                  Prosa.Model.Aggregate.Workload.workload_of_jobs
                                    (fun jo =>
                                      Prosa.Model.Priority.Definitions.hep_job jo j &&
                                        decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
                                    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1
                                      (max 0
                                          (↑t1 +
                                            (↑(Prosa.Behavior.Job.job_arrival j - t1 + 1) +
                                                Prosa.Model.Priority.Gel.task_priority_point tsk -
                                              Prosa.Model.Priority.Gel.task_priority_point tsk_o))).natAbs)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Gel_BoundedPi_total_workload_shorten_range
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
       forall (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk ts))
         Bool_true ->
       forall L : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) L ->
       @eq Prosa_Behavior_Time_duration L
         (Prosa_Analysis_Definitions_RequestBoundFunction_total_request_bound_function Task
            inst_3
            inst_10
            inst_13 ts L) ->
       forall j : Job,
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_16 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_23 j)
         Bool_true ->
       forall t1 t2 _UU0394_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1 _UU0394_)
         t2 ->
       forall tsk_o : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk_o)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3)
               tsk_o ts))
         Bool_true ->
       @eq Bool
         (Decidable_decide (Ne Task tsk_o tsk)
            (instDecidableNot (@eq Task tsk_o tsk)
               (inst_3 tsk_o tsk)))
         Bool_true ->
       @eq Bool
         (Decidable_decide
            (LE_le_inst1 Int Int_instLEInt
               (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
                  (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                     (Nat_cast_inst1 Int instNatCastInt
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                              Prosa_Behavior_Time_instant
                              (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                 inst_7
                                 inst_20
                                 j)
                              t1)
                           (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                     (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                        inst_3
                        inst_26 tsk))
                  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                     inst_3
                     inst_26 tsk_o))
               (Nat_cast_inst1 Int instNatCastInt _UU0394_))
            (Int_decLe
               (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHSub_inst1 Int Int_instSub)
                  (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
                     (Nat_cast_inst1 Int instNatCastInt
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                              Prosa_Behavior_Time_instant
                              (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                 inst_7
                                 inst_20
                                 j)
                              t1)
                           (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                     (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                        inst_3
                        inst_26 tsk))
                  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                     inst_3
                     inst_26 tsk_o))
               (Nat_cast_inst1 Int instNatCastInt _UU0394_)))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_23
            (fun jo : Job =>
             Bool_and
               (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_7
                  (Prosa_Model_Priority_Gel_GEL Job
                     inst_7 Task
                     inst_3
                     inst_26
                     inst_20
                     inst_16)
                  jo j)
               (Decidable_decide
                  (@eq Task
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_16 jo)
                     tsk_o)
                  (inst_3
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_16 jo)
                     tsk_o)))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
                  _UU0394_)))
         (Prosa_Model_Aggregate_Workload_workload_of_jobs Job
            inst_7
            inst_23
            (fun jo : Job =>
             Bool_and
               (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_7
                  (Prosa_Model_Priority_Gel_GEL Job
                     inst_7 Task
                     inst_3
                     inst_26
                     inst_20
                     inst_16)
                  jo j)
               (Decidable_decide
                  (@eq Task
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_16 jo)
                     tsk_o)
                  (inst_3
                     (Prosa_Model_Task_Concept_JobTask_job_task Job
                        inst_7 Task
                        inst_3
                        inst_16 jo)
                     tsk_o)))
            (Prosa_Behavior_Arrival_sequence_arrivals_between Job
               inst_7 arr_seq t1
               (Int_natAbs
                  (Max_max_inst1 Int Int_instMax (OfNat_ofNat_inst1 Int 0 (instOfNat 0))
                     (HAdd_hAdd_inst7 Int Int Int (instHAdd_inst1 Int Int_instAdd)
                        (Nat_cast_inst1 Int instNatCastInt t1)
                        (HSub_hSub_inst7 Int Prosa_Model_Priority_Gel_offset Int
                           (instHSub_inst1 Int Int_instSub)
                           (HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int
                              (instHAdd_inst1 Int Int_instAdd)
                              (Nat_cast_inst1 Int instNatCastInt
                                 (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                                    (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                                    (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                                       Prosa_Behavior_Time_instant
                                       (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                                       (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                          inst_7
                                          inst_20
                                          j)
                                       t1)
                                    (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
                              (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                                 inst_3
                                 inst_26
                                 tsk))
                           (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
                              inst_3
                              inst_26
                              tsk_o)))))))
```
