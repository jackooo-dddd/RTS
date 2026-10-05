# `priority_inversion_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_bound`
- Lean: `Prosa.Results.Rta.Ideal.Elf.BoundedPi.priority_inversion_bound`
- Certificate: `priority_inversion_bound_correspondence`

## Official Rocq

```coq
priority_inversion_bound : duration -> (duration -> duration) -> duration -> nat

priority_inversion_bound is not universe polymorphic
Arguments priority_inversion_bound priority_inversion_lp_tasks_bound
  priority_inversion_ep_tasks_bound%function_scope A
priority_inversion_bound is transparent
Expands to: Constant prosa.results.rta.ideal.elf.bounded_pi.priority_inversion_bound
Declared in library prosa.results.rta.ideal.elf.bounded_pi, line 184, characters 13-37
priority_inversion_bound
     : duration -> (duration -> duration) -> duration -> nat
```

Body:

```coq
priority_inversion_bound =
fun (priority_inversion_lp_tasks_bound : duration) (priority_inversion_ep_tasks_bound : duration -> duration)
  (A : duration) =>
maxn priority_inversion_lp_tasks_bound (priority_inversion_ep_tasks_bound A)
     : duration -> (duration -> duration) -> duration -> nat

Arguments priority_inversion_bound priority_inversion_lp_tasks_bound
  priority_inversion_ep_tasks_bound%function_scope A
```

## Lean

```lean
Prosa.Results.Rta.Ideal.Elf.BoundedPi.priority_inversion_bound : Prosa.Behavior.Time.duration →
  (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Results.Rta.Ideal.Elf.BoundedPi.priority_inversion_bound : Prosa.Behavior.Time.duration →
  (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) → Prosa.Behavior.Time.duration → ℕ :=
fun priority_inversion_lp_tasks_bound priority_inversion_ep_tasks_bound A =>
  Nat.max priority_inversion_lp_tasks_bound (priority_inversion_ep_tasks_bound A)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_priority_inversion_bound
     : Prosa_Behavior_Time_duration ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Results_Rta_Ideal_Elf_BoundedPi_priority_inversion_bound@{} =
fun (priority_inversion_lp_tasks_bound : Prosa_Behavior_Time_duration)
  (priority_inversion_ep_tasks_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
  (A : Prosa_Behavior_Time_duration) =>
Nat_max priority_inversion_lp_tasks_bound (priority_inversion_ep_tasks_bound A)
     : Prosa_Behavior_Time_duration ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Results_Rta_Ideal_Elf_BoundedPi_priority_inversion_bound priority_inversion_lp_tasks_bound
  priority_inversion_ep_tasks_bound%_function_scope a____at____internal__hyg0
```
