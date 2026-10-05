# `refine_foldr_lemma`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.refinements.refine_foldr_lemma`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_foldr_lemma`
- Certificate: `refine_foldr_lemma_correspondence`

## Official Rocq

```coq
refine_foldr_lemma :
@refines ((nat -> nat -> nat) -> nat -> seq nat -> nat) ((N -> N -> N) -> N -> seq N -> N)
  ((Rnat ==> Rnat ==> Rnat) ==> Rnat ==> @list_R nat N Rnat ==> Rnat) (@foldr nat nat) 
  (@foldr N N)

refine_foldr_lemma is not universe polymorphic
refine_foldr_lemma is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_foldr_lemma
Declared in library prosa.implementation.refinements.refinements, line 410, characters 6-24
refine_foldr_lemma
     : @refines ((nat -> nat -> nat) -> nat -> seq nat -> nat) ((N -> N -> N) -> N -> seq N -> N)
         ((Rnat ==> Rnat ==> Rnat) ==> Rnat ==> @list_R nat N Rnat ==> Rnat) (@foldr nat nat) 
         (@foldr N N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_foldr_lemma : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
        Prosa.Implementation.Refinements.Refinements.Rnat))
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.hrespectful
        (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)
        Prosa.Implementation.Refinements.Refinements.Rnat)))
  List.foldr List.foldr
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_foldr_lemma
     : Prosa_Implementation_Refinements_Refinements_refines
         ((Nat -> Nat -> Nat) -> Nat -> List_inst1 Nat -> Nat)
         ((Prosa_Implementation_Refinements_Refinements_N ->
           Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N) ->
          Prosa_Implementation_Refinements_Refinements_N ->
          List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful (Nat -> Nat -> Nat)
            (Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N -> Prosa_Implementation_Refinements_Refinements_N)
            (Nat -> List_inst1 Nat -> Nat)
            (Prosa_Implementation_Refinements_Refinements_N ->
             List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
             Prosa_Implementation_Refinements_Refinements_N)
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N (Nat -> Nat)
               (Prosa_Implementation_Refinements_Refinements_N ->
                Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Refinements_Rnat
               (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
                  Prosa_Implementation_Refinements_Refinements_N Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat
                  Prosa_Implementation_Refinements_Refinements_Rnat))
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N (List_inst1 Nat -> Nat)
               (List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
                Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Refinements_Rnat
               (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 Nat)
                  (List_inst1 Prosa_Implementation_Refinements_Refinements_N) Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  (Prosa_Implementation_Refinements_Refinements_list_R Nat
                     Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_Rnat)
                  Prosa_Implementation_Refinements_Refinements_Rnat)))
         (List_foldr_inst3 Nat Nat)
         (List_foldr_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N)
```
