# `filter_last_mem`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.filter_last_mem`
- Lean: `Prosa.Util.List.filter_last_mem`
- Certificate: `filter_last_mem_statement_certificate`

## Official Rocq

```coq
filter_last_mem :
forall {X : eqType} (xs : seq (Equality.sort X)) (d : Equality.sort X) (P : pred (Equality.sort X)),
is_true (@has (Equality.sort X) P xs) -> is_true (@last (Equality.sort X) d [seq x <- xs | P x] \in xs)

filter_last_mem is not universe polymorphic
Arguments filter_last_mem {X} xs%seq_scope d P _
filter_last_mem is opaque
Expands to: Constant prosa.util.list.filter_last_mem
Declared in library prosa.util.list, line 551, characters 6-21
@filter_last_mem
     : forall (X : eqType) (xs : seq (Equality.sort X)) (d : Equality.sort X) (P : pred (Equality.sort X)),
       is_true (@has (Equality.sort X) P xs) ->
       is_true (@last (Equality.sort X) d [seq x <- xs | P x] \in xs)
```

## Lean

```lean
@Prosa.Util.List.filter_last_mem : ∀ {X : Type u_1} [DecidableEq X] (xs : List X) (d : X) (P : X → Bool),
  xs.any P = true → (List.filter P xs).getLastD d ∈ xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_filter_last_mem
     : forall X : Type,
       DecidableEq X ->
       forall (xs : List X) (d : X) (P : X -> Bool),
       @eq Bool (List_any X xs P) Bool_true ->
       Membership_mem X (List X) (List_instMembership X) xs (List_getLastD X (List_filter X P xs) d)
```
