# `task_intra_IBF`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.restricted_supply.task_ibf_readiness.task_intra_IBF`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness.task_intra_IBF`
- Certificate: `task_intra_IBF_correspondence`

## Official Rocq

```coq
task_intra_IBF :
(duration -> duration) ->
(duration -> duration -> duration) -> (duration -> duration -> duration) -> duration -> duration -> nat

task_intra_IBF is not universe polymorphic
Arguments task_intra_IBF
  (service_inversion_bound athep_workload_bound readiness_interference_bound)%function_scope 
  A R
task_intra_IBF is transparent
Expands to: Constant prosa.analysis.abstract.restricted_supply.task_ibf_readiness.task_intra_IBF
Declared in library prosa.analysis.abstract.restricted_supply.task_ibf_readiness, line 75, characters 13-27
task_intra_IBF
     : (duration -> duration) ->
       (duration -> duration -> duration) ->
       (duration -> duration -> duration) -> duration -> duration -> nat
```

Body:

```coq
task_intra_IBF =
fun (service_inversion_bound : duration -> duration)
  (athep_workload_bound readiness_interference_bound : duration -> duration -> duration) 
  (A R : duration) =>
athep_workload_bound A R + service_inversion_bound A + readiness_interference_bound A R
     : (duration -> duration) ->
       (duration -> duration -> duration) ->
       (duration -> duration -> duration) -> duration -> duration -> nat

Arguments task_intra_IBF
  (service_inversion_bound athep_workload_bound readiness_interference_bound)%function_scope 
  A R
```

## Lean

```lean
Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness.task_intra_IBF : (Prosa.Behavior.Time.duration →
    Prosa.Behavior.Time.duration) →
  (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
    (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
      Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness.task_intra_IBF : (Prosa.Behavior.Time.duration →
    Prosa.Behavior.Time.duration) →
  (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
    (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
      Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ :=
fun service_inversion_bound athep_workload_bound readiness_interference_bound A R =>
  athep_workload_bound A R + service_inversion_bound A + readiness_interference_bound A R
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_task_intra_IBF
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_task_intra_IBF@{} =
fun (service_inversion_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
  (athep_workload_bound
   readiness_interference_bound : Prosa_Behavior_Time_duration ->
                                  Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
  (A R : Prosa_Behavior_Time_duration) =>
HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
  (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) (athep_workload_bound A R)
     (service_inversion_bound A))
  (readiness_interference_bound A R)
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Abstract_RestrictedSupply_TaskIbfReadiness_task_intra_IBF
  (service_inversion_bound athep_workload_bound readiness_interference_bound)%_function_scope 
  A a____at____internal__hyg0
```
