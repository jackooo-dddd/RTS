# `representative_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.search_space.representative_exists`
- Lean: `Prosa.Analysis.Abstract.SearchSpace.representative_exists`
- Certificate: `ss_representative_statement_correspondence`

## Official Rocq

```coq
representative_exists :
forall (B : time.duration) (interference_bound_function : time.duration -> time.duration -> time.duration)
  (A : time.duration),
is_true (A < B) ->
exists A_sp : nat,
  is_true (A_sp <= A) /\
  @are_equivalent_at_values_less_than Datatypes_nat__canonical__eqtype_Equality
    (interference_bound_function A) (interference_bound_function A_sp) B /\
  is_in_search_space B interference_bound_function A_sp

representative_exists is not universe polymorphic
Arguments representative_exists B interference_bound_function%function_scope A H_A_less_than_B
representative_exists is opaque
Expands to: Constant prosa.analysis.abstract.search_space.representative_exists
Declared in library prosa.analysis.abstract.search_space, line 82, characters 10-31
representative_exists
     : forall (B : time.duration)
         (interference_bound_function : time.duration -> time.duration -> time.duration) 
         (A : time.duration),
       is_true (A < B) ->
       exists A_sp : nat,
         is_true (A_sp <= A) /\
         @are_equivalent_at_values_less_than Datatypes_nat__canonical__eqtype_Equality
           (interference_bound_function A) (interference_bound_function A_sp) B /\
         is_in_search_space B interference_bound_function A_sp
```

## Lean

```lean
Prosa.Analysis.Abstract.SearchSpace.representative_exists : ∀ (B : Prosa.Behavior.Time.duration)
  (interference_bound_function :
    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
  ∀ A < B,
    ∃ A_sp ≤ A,
      Prosa.Analysis.Abstract.SearchSpace.are_equivalent_at_values_less_than (interference_bound_function A)
          (interference_bound_function A_sp) B ∧
        Prosa.Analysis.Abstract.SearchSpace.is_in_search_space B interference_bound_function A_sp
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_SearchSpace_representative_exists
     : forall (B : Prosa_Behavior_Time_duration)
         (interference_bound_function : Prosa_Behavior_Time_duration ->
                                        Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
         (A : Prosa_Behavior_Time_duration),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat A B ->
       Exists Prosa_Behavior_Time_duration
         (fun A_sp : Prosa_Behavior_Time_duration =>
          And (LE_le_inst1 Prosa_Behavior_Time_duration instLENat A_sp A)
            (And
               (Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than_inst1
                  Prosa_Behavior_Time_duration instDecidableEqNat (interference_bound_function A)
                  (interference_bound_function A_sp) B)
               (Prosa_Analysis_Abstract_SearchSpace_is_in_search_space B interference_bound_function A_sp)))
```
