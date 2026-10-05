# `max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.ideal.abstract_seq_rta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis`
- Lean: `Prosa.Analysis.Abstract.Ideal.AbstractSeqRta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis`
- Certificate: `max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis_correspondence`

## Official Rocq

```coq
max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskRunToCompletionThreshold Task} 
  {Job : JobType} {H1 : JobTask Job Task} {H3 : JobCost Job} {H4 : JobPreemptable Job}
  (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
forall {H5 : MaxArrivals Task},
@valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
forall (L : duration) (task_IBF : duration -> duration -> duration) (R : duration),
(forall A : duration,
 is_in_search_space L
   (fun A0 Δ : duration =>
    @task_request_bound_function Task H H5 tsk (A0 + 1) - @task_cost Task H tsk + task_IBF A0 Δ)
   A ->
 exists F : duration,
   is_true
     (@task_request_bound_function Task H H5 tsk (A + 1) - (@task_cost Task H tsk - @task_rtct Task H0 tsk) +
      task_IBF A (A + F) <= A + F) /\
   is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
is_true (0 < @max_arrivals Task H5 tsk 1) ->
forall A : duration,
       (fun A1 Δ : duration =>
        @task_request_bound_function Task H H5 tsk (A1 + 1) - @task_cost Task H tsk + task_IBF A1 Δ)]
  A ->
exists F : duration,
  is_true
    (@task_rtct Task H0 tsk +
     (@task_request_bound_function Task H H5 tsk (A + 1) - @task_cost Task H tsk + task_IBF A (A + F)) <=
     A + F) /\
  is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)

max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis is not universe polymorphic
Arguments max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis {Task H H0 Job H1 H3 H4} 
  arr_seq ts%seq_scope tsk H_tsk_in_ts H_valid_run_to_completion_threshold {H5} H_valid_arrival_curve 
  L task_IBF%function_scope R H_R_is_maximum_seq%function_scope H_arrival_curve_pos 
  A _
max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis is opaque
Expands to: Constant
            prosa.analysis.abstract.ideal.abstract_seq_rta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis
Declared in library prosa.analysis.abstract.ideal.abstract_seq_rta, line 178, characters 10-64
@max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskRunToCompletionThreshold Task) 
         (Job : JobType) (H1 : JobTask Job Task) (H3 : JobCost Job) (H4 : JobPreemptable Job)
         (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @valid_task_run_to_completion_threshold Task H Job H1 H3 H4 H0 arr_seq tsk ->
       forall H5 : MaxArrivals Task,
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task H5) ->
       forall (L : duration) (task_IBF : duration -> duration -> duration) (R : duration),
       (forall A : duration,
        is_in_search_space L
          (fun A0 Δ : duration =>
           @task_request_bound_function Task H H5 tsk (A0 + 1) - @task_cost Task H tsk + task_IBF A0 Δ)
          A ->
        exists F : duration,
          is_true
            (@task_request_bound_function Task H H5 tsk (A + 1) -
             (@task_cost Task H tsk - @task_rtct Task H0 tsk) + task_IBF A (A + F) <= 
             A + F) /\
          is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)) ->
       is_true (0 < @max_arrivals Task H5 tsk 1) ->
       forall A : duration,
       is_in_search_space L
         (fun A0 Δ : duration =>
          @task_request_bound_function Task H H5 tsk (A0 + 1) - @task_cost Task H tsk + task_IBF A0 Δ)
         A ->
       exists F : duration,
         is_true
           (@task_rtct Task H0 tsk +
            (@task_request_bound_function Task H H5 tsk (A + 1) - @task_cost Task H tsk + task_IBF A (A + F)) <=
            A + F) /\
         is_true (F + (@task_cost Task H tsk - @task_rtct Task H0 tsk) <= R)
```

## Lean

```lean
@Prosa.Analysis.Abstract.Ideal.AbstractSeqRta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Preemption.Parameters.TaskRunToCompletionThreshold Task]
  [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_5 : Prosa.Behavior.Job.JobCost Job]
  [inst_6 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (ts : List Task) (tsk : Task),
  decide (tsk ∈ ts) = true →
    Prosa.Model.Task.Preemption.Parameters.valid_task_run_to_completion_threshold arr_seq tsk →
      ∀ [inst_7 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
        Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
          ∀ (L : Prosa.Behavior.Time.duration)
            (task_IBF : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration)
            (R : Prosa.Behavior.Time.duration),
            (∀ (A : Prosa.Behavior.Time.duration),
                Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                    (fun A0 Δ =>
                      Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A0 + 1) -
                          Prosa.Model.Task.Concept.task_cost tsk +
                        task_IBF A0 Δ)
                    A →
                  ∃ F,
                    Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) -
                            (Prosa.Model.Task.Concept.task_cost tsk -
                              Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) +
                          task_IBF A (A + F) ≤
                        A + F ∧
                      F +
                          (Prosa.Model.Task.Concept.task_cost tsk -
                            Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                        R) →
              0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1 →
                ∀ (A : Prosa.Behavior.Time.duration),
                  Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                      (fun A0 Δ =>
                        Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A0 + 1) -
                            Prosa.Model.Task.Concept.task_cost tsk +
                          task_IBF A0 Δ)
                      A →
                    ∃ F,
                      Prosa.Model.Task.Preemption.Parameters.task_rtct tsk +
                            (Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk (A + 1) -
                                Prosa.Model.Task.Concept.task_cost tsk +
                              task_IBF A (A + F)) ≤
                          A + F ∧
                        F +
                            (Prosa.Model.Task.Concept.task_cost tsk -
                              Prosa.Model.Task.Preemption.Parameters.task_rtct tsk) ≤
                          R
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Ideal_AbstractSeqRta_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_13 : 
          Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task
            inst_3)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (inst_23 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (ts : List Task) (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task
                  inst_3)
               tsk ts))
         Bool_true ->
       Prosa_Model_Task_Preemption_Parameters_valid_task_run_to_completion_threshold Task
         inst_3
         inst_10 Job
         inst_7
         inst_16
         inst_20
         inst_23
         inst_13 arr_seq tsk ->
       forall
         inst_50 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3,
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_50) ->
       forall (L : Prosa_Behavior_Time_duration)
         (task_IBF : Prosa_Behavior_Time_duration ->
                     Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
         (R : Prosa_Behavior_Time_duration),
       (forall A : Prosa_Behavior_Time_duration,
        Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
          (fun A0 _UU0394_ : Prosa_Behavior_Time_duration =>
           HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
             (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                   inst_3
                   inst_10
                   inst_50 tsk
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                      A0 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                   inst_3
                   inst_10 tsk))
             (task_IBF A0 _UU0394_))
          A ->
        Exists Prosa_Behavior_Time_duration
          (fun F : Prosa_Behavior_Time_duration =>
           And
             (LE_le_inst1 Nat instLENat
                (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                   (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                      (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                         inst_3
                         inst_10
                         inst_50 tsk
                         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                            Prosa_Behavior_Time_duration
                            (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                      (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                         Prosa_Behavior_Time_duration
                         (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                         (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                            inst_3
                            inst_10
                            tsk)
                         (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                            inst_3
                            inst_13
                            tsk)))
                   (task_IBF A
                      (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                         Prosa_Behavior_Time_duration
                         (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F)))
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
             (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                   Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) F
                   (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                      Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                      (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                         inst_3
                         inst_10 tsk)
                      (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                         inst_3
                         inst_13 tsk)))
                R))) ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_50 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))) ->
       forall A : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space L
         (fun A0 _UU0394_ : Prosa_Behavior_Time_duration =>
          HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
               (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                  inst_3
                  inst_10
                  inst_50 tsk
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A0
                     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
               (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                  inst_3
                  inst_10 tsk))
            (task_IBF A0 _UU0394_))
         A ->
       Exists Prosa_Behavior_Time_duration
         (fun F : Prosa_Behavior_Time_duration =>
          And
            (LE_le_inst1 Prosa_Behavior_Job_work instLENat
               (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
                  (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
                  (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                     inst_3
                     inst_13 tsk)
                  (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_duration Nat (instHAdd_inst1 Nat instAddNat)
                     (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat)
                        (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
                           inst_3
                           inst_10
                           inst_50
                           tsk
                           (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                              Prosa_Behavior_Time_duration
                              (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                              (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
                        (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                           inst_3
                           inst_10
                           tsk))
                     (task_IBF A
                        (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                           Prosa_Behavior_Time_duration
                           (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))))
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
            (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) F
                  (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Job_work
                     Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                     (Prosa_Model_Task_Concept_TaskCost_task_cost Task
                        inst_3
                        inst_10 tsk)
                     (Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold_task_rtct Task
                        inst_3
                        inst_13 tsk)))
               R))
```
