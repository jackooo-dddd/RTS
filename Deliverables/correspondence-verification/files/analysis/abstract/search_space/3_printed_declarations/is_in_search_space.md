# `is_in_search_space`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.search_space.is_in_search_space`
- Lean: `Prosa.Analysis.Abstract.SearchSpace.is_in_search_space`
- Certificate: `ss_search_space_correspondence`

## Official Rocq

```coq
is_in_search_space : time.duration -> (time.duration -> time.duration -> time.duration) -> nat -> Prop

is_in_search_space is not universe polymorphic
Arguments is_in_search_space B interference_bound_function%function_scope A%nat_scope
is_in_search_space is transparent
Expands to: Constant prosa.analysis.abstract.search_space.is_in_search_space
Declared in library prosa.analysis.abstract.search_space, line 62, characters 13-31
is_in_search_space
     : time.duration -> (time.duration -> time.duration -> time.duration) -> nat -> Prop
```

Body:

```coq
is_in_search_space =
fun (B : time.duration) (interference_bound_function : time.duration -> time.duration -> time.duration)
  (A : nat) =>
A = 0 \/
is_true (0 < A < B) /\
@are_not_equivalent_at_values_less_than Datatypes_nat__canonical__eqtype_Equality
  (interference_bound_function (A - 1)) (interference_bound_function A) B
     : time.duration -> (time.duration -> time.duration -> time.duration) -> nat -> Prop

Arguments is_in_search_space B interference_bound_function%function_scope A%nat_scope
```

## Lean

```lean
Prosa.Analysis.Abstract.SearchSpace.is_in_search_space : Prosa.Behavior.Time.duration →
  (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
    Prosa.Behavior.Time.duration → Prop
```

Body:

```lean
def Prosa.Analysis.Abstract.SearchSpace.is_in_search_space : Prosa.Behavior.Time.duration →
  (Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration) →
    Prosa.Behavior.Time.duration → Prop :=
fun B interference_bound_function A =>
  A = 0 ∨
    0 < A ∧
      A < B ∧
        Prosa.Analysis.Abstract.SearchSpace.are_not_equivalent_at_values_less_than (interference_bound_function (A - 1))
          (interference_bound_function A) B
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
     : Prosa_Behavior_Time_duration ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Time_duration -> SProp
```

Body:

```coq
Prosa_Analysis_Abstract_SearchSpace_is_in_search_space@{} =
fun (B : Prosa_Behavior_Time_duration)
  (interference_bound_function : Prosa_Behavior_Time_duration ->
                                 Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
  (A : Prosa_Behavior_Time_duration) =>
Or (@eq Prosa_Behavior_Time_duration A (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
  (And
     (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
        (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)) A)
     (And (LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat A B)
        (Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than_inst1
           Prosa_Behavior_Time_duration instDecidableEqNat
           (interference_bound_function
              (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                 Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat) A
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1))))
           (interference_bound_function A) B)))
     : Prosa_Behavior_Time_duration ->
       (Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration) ->
       Prosa_Behavior_Time_duration -> SProp

Arguments Prosa_Analysis_Abstract_SearchSpace_is_in_search_space B
  interference_bound_function%_function_scope A
```
