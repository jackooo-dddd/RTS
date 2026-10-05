# `refine_map`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_map`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_map`
- Certificate: `refine_map_correspondence`

## Official Rocq

```coq
refine_map :
forall {A A' B B' : Type} (F : A -> B) (F' : A' -> B') (rA : A -> A' -> Type) (rB : B -> B' -> Type)
  (xs : seq A) (xs' : seq A'),
@refines (seq A) (seq A') (@list_R A A' rA) xs xs' ->
@refines (A -> B) (A' -> B') (rA ==> rB) F F' ->
@refines (seq B) (seq B') (@list_R B B' rB) [seq F i | i <- xs] [seq F' i | i <- xs']

refine_map is not universe polymorphic
Arguments refine_map {A A' B B'}%_type_scope (F F' rA rB)%_function_scope (xs xs')%_seq_scope _ _
refine_map is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_map
Declared in library prosa.implementation.refinements.refinements, line 262, characters 16-26
@refine_map
     : forall (A A' B B' : Type) (F : A -> B) (F' : A' -> B') (rA : A -> A' -> Type) 
         (rB : B -> B' -> Type) (xs : seq A) (xs' : seq A'),
       @refines (seq A) (seq A') (@list_R A A' rA) xs xs' ->
       @refines (A -> B) (A' -> B') (rA ==> rB) F F' ->
       @refines (seq B) (seq B') (@list_R B B' rB) [seq F i | i <- xs] [seq F' i | i <- xs']
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.refine_map : {A A' B B' : Type} →
  (F : A → B) →
    (F' : A' → B') →
      (rA : A → A' → Type) →
        (rB : B → B' → Type) →
          (xs : List A) →
            (xs' : List A') →
              Prosa.Implementation.Refinements.Refinements.refines
                  (Prosa.Implementation.Refinements.Refinements.list_R rA) xs xs' →
                Prosa.Implementation.Refinements.Refinements.refines
                    (Prosa.Implementation.Refinements.Refinements.hrespectful rA rB) F F' →
                  Prosa.Implementation.Refinements.Refinements.refines
                    (Prosa.Implementation.Refinements.Refinements.list_R rB) (List.map F xs) (List.map F' xs')
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_map
     : forall (A A' B B' : Type) (F : A -> B) (F' : A' -> B') (rA : A -> A' -> Type) 
         (rB : B -> B' -> Type) (xs : List_inst1 A) (xs' : List_inst1 A'),
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 A) (List_inst1 A')
         (Prosa_Implementation_Refinements_Refinements_list_R A A' rA) xs xs' ->
       Prosa_Implementation_Refinements_Refinements_refines (A -> B) (A' -> B')
         (Prosa_Implementation_Refinements_Refinements_hrespectful A A' B B' rA rB) F F' ->
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 B) (List_inst1 B')
         (Prosa_Implementation_Refinements_Refinements_list_R B B' rB) (List_map_inst3 A B F xs)
         (List_map_inst3 A' B' F' xs')
```
