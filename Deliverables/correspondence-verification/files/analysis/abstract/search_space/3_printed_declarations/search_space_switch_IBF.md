# `search_space_switch_IBF`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.search_space.search_space_switch_IBF`
- Lean: `Prosa.Analysis.Abstract.SearchSpace.search_space_switch_IBF`
- Certificate: `ss_switch_statement_correspondence`

## Official Rocq

```coq
search_space_switch_IBF :
forall (B : time.duration) (IBF1 IBF2 : nat -> time.duration -> time.duration),
(forall (A : nat) (Δ : time.duration), is_true (A < B) -> IBF1 A Δ = IBF2 A Δ) ->
forall A : nat, is_in_search_space B IBF1 A -> is_in_search_space B IBF2 A

search_space_switch_IBF is not universe polymorphic
Arguments search_space_switch_IBF B (IBF1 IBF2 _)%function_scope A%nat_scope _
search_space_switch_IBF is opaque
Expands to: Constant prosa.analysis.abstract.search_space.search_space_switch_IBF
Declared in library prosa.analysis.abstract.search_space, line 184, characters 8-31
search_space_switch_IBF
     : forall (B : time.duration) (IBF1 IBF2 : nat -> time.duration -> time.duration),
       (forall (A : nat) (Δ : time.duration), is_true (A < B) -> IBF1 A Δ = IBF2 A Δ) ->
       forall A : nat, is_in_search_space B IBF1 A -> is_in_search_space B IBF2 A
```

## Lean

```lean
Prosa.Analysis.Abstract.SearchSpace.search_space_switch_IBF : ∀ (B : Prosa.Behavior.Time.duration)
  (IBF1 IBF2 : Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration),
  (∀ (A Δ : Prosa.Behavior.Time.duration), A < B → IBF1 A Δ = IBF2 A Δ) →
    ∀ (A : Prosa.Behavior.Time.duration),
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space B IBF1 A →
        Prosa.Analysis.Abstract.SearchSpace.is_in_search_space B IBF2 A
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_SearchSpace_search_space_switch_IBF
     : forall (B : Prosa_Behavior_Time_duration)
         (IBF1
          IBF2 : Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration),
       (forall A _UU0394_ : Prosa_Behavior_Time_duration,
        LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat A B ->
        @eq Prosa_Behavior_Time_duration (IBF1 A _UU0394_) (IBF2 A _UU0394_)) ->
       forall A : Prosa_Behavior_Time_duration,
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space B IBF1 A ->
       Prosa_Analysis_Abstract_SearchSpace_is_in_search_space B IBF2 A
```
