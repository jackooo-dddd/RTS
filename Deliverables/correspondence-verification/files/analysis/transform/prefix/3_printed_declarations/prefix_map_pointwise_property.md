# `prefix_map_pointwise_property`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.transform.prefix.prefix_map_pointwise_property`
- Lean: `Prosa.Analysis.Transform.Prefix.prefix_map_pointwise_property`
- Certificate: `prefix_map_pointwise_property_correspondence`

## Official Rocq

```coq
prefix_map_pointwise_property :
forall {Job : JobType} {PState : ProcessorState Job} (P : @schedule Job PState -> Prop)
  (Q : @schedule Job PState -> instant -> Prop) (f : @schedule Job PState -> instant -> @schedule Job PState),
(forall (sched : @schedule Job PState) (t_ref : instant), P sched -> P (f sched t_ref)) ->
(forall (sched : @schedule Job PState) (t_ref : nat),
 P sched ->
 (forall t' : nat, is_true (t' < t_ref) -> Q sched t') ->
 forall t' : nat, is_true (t' <= t_ref) -> Q (f sched t_ref) t') ->
forall (sched : @schedule Job PState) (horizon : nat),
P sched -> forall t : nat, is_true (t < horizon) -> Q (@prefix_map Job PState sched f horizon) t

prefix_map_pointwise_property is not universe polymorphic
Arguments prefix_map_pointwise_property {Job PState} (P Q f H_f_maintains_P H_f_grows_Q)%function_scope 
  sched horizon%nat_scope _ t%nat_scope _
prefix_map_pointwise_property is opaque
Expands to: Constant prosa.analysis.transform.prefix.prefix_map_pointwise_property
Declared in library prosa.analysis.transform.prefix, line 86, characters 10-39
@prefix_map_pointwise_property
     : forall (Job : JobType) (PState : ProcessorState Job) (P : @schedule Job PState -> Prop)
         (Q : @schedule Job PState -> instant -> Prop)
         (f : @schedule Job PState -> instant -> @schedule Job PState),
       (forall (sched : @schedule Job PState) (t_ref : instant), P sched -> P (f sched t_ref)) ->
       (forall (sched : @schedule Job PState) (t_ref : nat),
        P sched ->
        (forall t' : nat, is_true (t' < t_ref) -> Q sched t') ->
        forall t' : nat, is_true (t' <= t_ref) -> Q (f sched t_ref) t') ->
       forall (sched : @schedule Job PState) (horizon : nat),
       P sched -> forall t : nat, is_true (t < horizon) -> Q (@prefix_map Job PState sched f horizon) t
```

## Lean

```lean
@Prosa.Analysis.Transform.Prefix.prefix_map_pointwise_property : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (P : Prosa.Behavior.Schedule.schedule PState → Prop)
  (Q : Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prop)
  (f : Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prosa.Behavior.Schedule.schedule PState),
  (∀ (sched : Prosa.Behavior.Schedule.schedule PState) (t_ref : Prosa.Behavior.Time.instant),
      P sched → P (f sched t_ref)) →
    (∀ (sched : Prosa.Behavior.Schedule.schedule PState) (t_ref : ℕ),
        P sched → (∀ t' < t_ref, Q sched t') → ∀ t' ≤ t_ref, Q (f sched t_ref) t') →
      ∀ (sched : Prosa.Behavior.Schedule.schedule PState) (horizon : ℕ),
        P sched → ∀ t < horizon, Q (Prosa.Analysis.Transform.Prefix.prefix_map sched f horizon) t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_Prefix_prefix_map_pointwise_property
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (P : Prosa_Behavior_Schedule_schedule Job
                inst_3 PState ->
              SProp)
         (Q : Prosa_Behavior_Schedule_schedule Job
                inst_3 PState ->
              Prosa_Behavior_Time_instant -> SProp)
         (f : Prosa_Behavior_Schedule_schedule Job
                inst_3 PState ->
              Prosa_Behavior_Time_instant ->
              Prosa_Behavior_Schedule_schedule Job
                inst_3 PState),
       (forall
          (sched : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
          (t_ref : Prosa_Behavior_Time_instant),
        P sched -> P (f sched t_ref)) ->
       (forall
          (sched : Prosa_Behavior_Schedule_schedule Job
                     inst_3 PState)
          (t_ref : Nat),
        P sched ->
        (forall t' : Nat, LT_lt_inst1 Nat instLTNat t' t_ref -> Q sched t') ->
        forall t' : Nat, LE_le_inst1 Nat instLENat t' t_ref -> Q (f sched t_ref) t') ->
       forall
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (horizon : Nat),
       P sched ->
       forall t : Nat,
       LT_lt_inst1 Nat instLTNat t horizon ->
       Q
         (Prosa_Analysis_Transform_Prefix_prefix_map Job
            inst_3 PState sched f horizon)
         t
```
