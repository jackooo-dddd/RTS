# `sched_nonpreemptive_next`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive_next`
- Lean: `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_nonpreemptive_next`
- Certificate: `sched_nonpreemptive_next_correspondence`

## Official Rocq

```coq
sched_nonpreemptive_next :
forall (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t : instant),
is_true (@scheduled_at Job (processor_state Job) (sched arr_seq) j t) ->
is_true (~~ @completed_by Job (processor_state Job) (sched arr_seq) task.JobCost j t.+1) ->
is_true (@scheduled_at Job (processor_state Job) (sched arr_seq) j t.+1)

sched_nonpreemptive_next is not universe polymorphic
Arguments sched_nonpreemptive_next arr_seq j t _ _
sched_nonpreemptive_next is opaque
Expands to: Constant prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive_next
Declared in library prosa.implementation.refinements.EDF.nonpreemptive_sched, line 62, characters 8-32
sched_nonpreemptive_next
     : forall (arr_seq : arrival_sequence Job) (j : Equality.sort Job) (t : instant),
       is_true (@scheduled_at Job (processor_state Job) (sched arr_seq) j t) ->
       is_true (~~ @completed_by Job (processor_state Job) (sched arr_seq) task.JobCost j t.+1) ->
       is_true (@scheduled_at Job (processor_state Job) (sched arr_seq) j t.+1)
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_nonpreemptive_next : ∀
  (arr_seq :
    Prosa.Behavior.Arrival_sequence.arrival_sequence Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.Job)
  (j : Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.scheduled_at (Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched arr_seq) j t =
      true →
    (!Prosa.Behavior.Service.completed_by (Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched arr_seq) j
            (t + 1)) =
        true →
      Prosa.Behavior.Service.scheduled_at (Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched arr_seq) j
          (t + 1) =
        true
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched_nonpreemptive_next
     : forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
                      Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
                      Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (j : Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst7
            Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
            (Prosa_Model_Processor_Ideal_processor_state_inst1
               Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
            (Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched arr_seq) j t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by_inst7
               Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
               (Prosa_Model_Processor_Ideal_processor_state_inst1
                  Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
               (Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched arr_seq)
               Prosa_Implementation_Definitions_Task_JobCost j
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst7
            Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
            (Prosa_Model_Processor_Ideal_processor_state_inst1
               Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
            (Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched arr_seq) j
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
         Bool_true
```
