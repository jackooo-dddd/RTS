# `refine_iota`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_iota`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_iota`
- Certificate: `refine_iota_correspondence`

## Official Rocq

```coq
refine_iota :
@refines (nat -> nat -> seq nat) (N -> N -> seq N) (Rnat ==> Rnat ==> @list_R nat N Rnat) iota
  (fun a b : N => @iota_T N one_N add_N a (nat_of_bin b))

refine_iota is not universe polymorphic
refine_iota is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_iota
Declared in library prosa.implementation.refinements.refinements, line 352, characters 16-27
refine_iota
     : @refines (nat -> nat -> seq nat) (N -> N -> seq N) (Rnat ==> Rnat ==> @list_R nat N Rnat) iota
         (fun a b : N => @iota_T N one_N add_N a (nat_of_bin b))
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_iota : Prosa.Implementation.Refinements.Refinements.refines
  (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
    (Prosa.Implementation.Refinements.Refinements.hrespectful Prosa.Implementation.Refinements.Refinements.Rnat
      (Prosa.Implementation.Refinements.Refinements.list_R Prosa.Implementation.Refinements.Refinements.Rnat)))
  (fun a b => List.range' a b) fun a b =>
  Prosa.Implementation.Refinements.Refinements.iota_T a (Prosa.Implementation.Refinements.Refinements.nat_of_bin b)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_iota
     : Prosa_Implementation_Refinements_Refinements_refines (Nat -> Nat -> List_inst1 Nat)
         (Prosa_Implementation_Refinements_Refinements_N ->
          Prosa_Implementation_Refinements_Refinements_N ->
          List_inst1 Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
            Prosa_Implementation_Refinements_Refinements_N (Nat -> List_inst1 Nat)
            (Prosa_Implementation_Refinements_Refinements_N ->
             List_inst1 Prosa_Implementation_Refinements_Refinements_N)
            Prosa_Implementation_Refinements_Refinements_Rnat
            (Prosa_Implementation_Refinements_Refinements_hrespectful Nat
               Prosa_Implementation_Refinements_Refinements_N (List_inst1 Nat)
               (List_inst1 Prosa_Implementation_Refinements_Refinements_N)
               Prosa_Implementation_Refinements_Refinements_Rnat
               (Prosa_Implementation_Refinements_Refinements_list_R Nat
                  Prosa_Implementation_Refinements_Refinements_N
                  Prosa_Implementation_Refinements_Refinements_Rnat)))
         (fun a b : Nat => List_range' a b (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
         (fun a b : Prosa_Implementation_Refinements_Refinements_N =>
          Prosa_Implementation_Refinements_Refinements_iota_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N a
            (Prosa_Implementation_Refinements_Refinements_nat_of_bin b))
```
