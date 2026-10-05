# `preemption_time_interval_case`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.preemption.preemption_time_interval_case`
- Lean: `Prosa.Analysis.Facts.Model.Preemption.preemption_time_interval_case`
- Certificate: `preemption_time_interval_case_correspondence`

## Official Rocq

```coq
preemption_time_interval_case :
forall {Job : JobType} {H1 : JobPreemptable Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState) (t1 t2 : nat),
(forall t : nat, is_true (t1 <= t < t2) -> is_true (~~ @preemption_time Job H1 arr_seq PState sched t)) \/
(exists t : nat,
   is_true (t1 <= t < t2) /\
   is_true (@preemption_time Job H1 arr_seq PState sched t) /\
   (forall t' : nat,
    is_true (t1 <= t') -> is_true (@preemption_time Job H1 arr_seq PState sched t') -> is_true (t <= t')))

preemption_time_interval_case is not universe polymorphic
Arguments preemption_time_interval_case {Job H1} arr_seq {PState} sched (t1 t2)%nat_scope
preemption_time_interval_case is opaque
Expands to: Constant prosa.analysis.facts.model.preemption.preemption_time_interval_case
Declared in library prosa.analysis.facts.model.preemption, line 40, characters 8-37
@preemption_time_interval_case
     : forall (Job : JobType) (H1 : JobPreemptable Job) (arr_seq : arrival_sequence Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (t1 t2 : nat),
       (forall t : nat, is_true (t1 <= t < t2) -> is_true (~~ @preemption_time Job H1 arr_seq PState sched t)) \/
       (exists t : nat,
          is_true (t1 <= t < t2) /\
          is_true (@preemption_time Job H1 arr_seq PState sched t) /\
          (forall t' : nat,
           is_true (t1 <= t') ->
           is_true (@preemption_time Job H1 arr_seq PState sched t') -> is_true (t <= t')))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Preemption.preemption_time_interval_case : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (t1 t2 : ℕ),
  (∀ (t : ℕ),
      (decide (t1 ≤ t) && decide (t < t2)) = true →
        (!Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t) = true) ∨
    ∃ t,
      (decide (t1 ≤ t) && decide (t < t2)) = true ∧
        Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t = true ∧
          ∀ (t' : ℕ), t1 ≤ t' → Prosa.Model.Schedule.PreemptionTime.preemption_time arr_seq sched t' = true → t ≤ t'
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Preemption_preemption_time_interval_case
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t1 t2 : Nat),
       Or
         (forall t : Nat,
          @eq Bool
            (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
               (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
            Bool_true ->
          @eq Bool
            (Bool_not
               (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                  inst_3
                  inst_6 arr_seq PState
                  sched t))
            Bool_true)
         (Exists Nat
            (fun t : Nat =>
             And
               (@eq Bool
                  (Bool_and (Decidable_decide (LE_le_inst1 Nat instLENat t1 t) (Nat_decLe t1 t))
                     (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
                  Bool_true)
               (And
                  (@eq Bool
                     (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                        inst_3
                        inst_6 arr_seq
                        PState sched t)
                     Bool_true)
                  (forall t' : Nat,
                   LE_le_inst1 Nat instLENat t1 t' ->
                   @eq Bool
                     (Prosa_Model_Schedule_PreemptionTime_preemption_time Job
                        inst_3
                        inst_6 arr_seq
                        PState sched t')
                     Bool_true ->
                   LE_le_inst1 Nat instLENat t t'))))
```
