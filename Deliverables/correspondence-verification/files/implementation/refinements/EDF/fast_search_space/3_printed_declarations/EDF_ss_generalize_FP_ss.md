# `EDF_ss_generalize_FP_ss`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.EDF_ss_generalize_FP_ss`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.EDF_ss_generalize_FP_ss`
- Certificate: `EDF_ss_generalize_FP_ss_correspondence`

## Official Rocq

```coq
EDF_ss_generalize_FP_ss :
forall (L : duration) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
task_search_space_emax_EDF_h tsk tsk 0
  ((L + (task_deadline tsk - task_deadline tsk)) %/ get_horizon_of_task tsk).+1 =
search_space_emax_FP L tsk

EDF_ss_generalize_FP_ss is not universe polymorphic
Arguments EDF_ss_generalize_FP_ss L ts%_seq_scope tsk H_tsk_in_ts
EDF_ss_generalize_FP_ss is opaque
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.EDF_ss_generalize_FP_ss
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 104, characters 8-31
EDF_ss_generalize_FP_ss
     : forall (L : duration) (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       task_search_space_emax_EDF_h tsk tsk 0
         ((L + (task_deadline tsk - task_deadline tsk)) %/ get_horizon_of_task tsk).+1 =
       search_space_emax_FP L tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.EDF_ss_generalize_FP_ss : ∀ (L : Prosa.Behavior.Time.duration)
  (ts : List Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task),
  ∀ tsk ∈ ts,
    Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF_h tsk tsk 0
        ((L + (Prosa.Model.Task.Concept.task_deadline tsk - Prosa.Model.Task.Concept.task_deadline tsk)) /
            Prosa.Implementation.Refinements.ArrivalCurve.get_horizon_of_task tsk +
          1) =
      Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_FP L tsk
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_EDF_ss_generalize_FP_ss
     : forall (L : Prosa_Behavior_Time_duration)
         (ts : List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task)
         (tsk : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task),
       Membership_mem_inst3 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
         (List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task)
         (List_instMembership_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) ts tsk ->
       @eq (List_inst1 Nat)
         (Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF_h tsk tsk
            (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
               (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
               (HDiv_hDiv_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHDiv_inst1 Prosa_Behavior_Time_duration Nat_instDiv)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) L
                     (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
                           Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
                           Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                           Prosa_Implementation_Definitions_Task_TaskDeadline tsk)
                        (Prosa_Model_Task_Concept_TaskDeadline_task_deadline_inst1
                           Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task
                           Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                           Prosa_Implementation_Definitions_Task_TaskDeadline tsk)))
                  (Prosa_Implementation_Refinements_ArrivalCurve_get_horizon_of_task tsk))
               (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
         (Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_FP L tsk)
```
