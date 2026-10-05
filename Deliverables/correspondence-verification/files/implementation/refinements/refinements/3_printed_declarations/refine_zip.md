# `refine_zip`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_zip`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_zip`
- Certificate: `refine_zip_correspondence`

## Official Rocq

```coq
refine_zip :
@refines (seq nat -> seq nat -> seq (nat * nat)) (seq N -> seq N -> seq (N * N))
  (@list_R nat N Rnat ==> @list_R nat N Rnat ==> @list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat))
  (@zip nat nat) (@zip N N)

refine_zip is not universe polymorphic
refine_zip is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_zip
Declared in library prosa.implementation.refinements.refinements, line 277, characters 16-26
refine_zip
     : @refines (seq nat -> seq nat -> seq (nat * nat)) (seq N -> seq N -> seq (N * N))
         (@list_R nat N Rnat ==>
          @list_R nat N Rnat ==> @list_R (nat * nat) (N * N) (@prod_R nat N Rnat nat N Rnat))
         (@zip nat nat) (@zip N N)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_zip : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful
    (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)
    (Prosa.Implementation.Refinements.Refinements.hrespectful
      (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)
      (Prosa.Implementation.Refinements.Refinements.list_R
        (Prosa.Implementation.Refinements.Refinements.prod_R Prosa.Implementation.Refinements.Refinements.Rnat
          Prosa.Implementation.Refinements.Refinements.Rnat))))
  List.zip List.zip
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_zip
     : Prosa_Implementation_Refinements_Refinements_refines
         (List_inst1 Nat -> List_inst1 Nat -> List_inst1 (Prod_inst3 Nat Nat))
         (List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
          List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
          List_inst1
            (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_N))
         (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 Nat)
            (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
            (List_inst1 Nat -> List_inst1 (Prod_inst3 Nat Nat))
            (List_inst1 Prosa_Implementation_Refinements_Refinements_N ->
             List_inst1
               (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_N))
            (Prosa_Implementation_Refinements_Refinements_list_R Nat
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_Rnat)
            (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 Nat)
               (List_inst1 Prosa_Implementation_Refinements_Refinements_N) (List_inst1 (Prod_inst3 Nat Nat))
               (List_inst1
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N))
               (Prosa_Implementation_Refinements_Refinements_list_R Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat)
               (Prosa_Implementation_Refinements_Refinements_list_R (Prod_inst3 Nat Nat)
                  (Prod_inst3 Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_N)
                  (Prosa_Implementation_Refinements_Refinements_prod_R Nat
                     Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_Rnat Nat
                     Prosa_Implementation_Refinements_Refinements_N
                     Prosa_Implementation_Refinements_Refinements_Rnat))))
         (List_zip_inst3 Nat Nat)
         (List_zip_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N)
```
