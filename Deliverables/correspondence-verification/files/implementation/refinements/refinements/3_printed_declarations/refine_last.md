# `refine_last`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_last`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_last`
- Certificate: `refine_last_correspondence`

## Official Rocq

```coq
refine_last :
forall {A B : Type} (rA : A -> B -> Type),
@refines (A -> seq A -> A) (B -> seq B -> B) (rA ==> @list_R A B rA ==> rA) (@last A) (@last B)

refine_last is not universe polymorphic
Arguments refine_last {A B}%_type_scope rA%_function_scope
refine_last is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_last
Declared in library prosa.implementation.refinements.refinements, line 315, characters 16-27
@refine_last
     : forall (A B : Type) (rA : A -> B -> Type),
       @refines (A -> seq A -> A) (B -> seq B -> B) (rA ==> @list_R A B rA ==> rA) (@last A) (@last B)
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.refine_last : {A B : Type} →
  (rA : A → B → Type) →
    Prosa.Implementation.Refinements.Refinements.refines
      (Prosa.Implementation.Refinements.Refinements.hrespectful rA
        (Prosa.Implementation.Refinements.Refinements.hrespectful
          (Prosa.Implementation.Refinements.Refinements.list_R rA) rA))
      Prosa.Implementation.Refinements.Refinements.seq_last Prosa.Implementation.Refinements.Refinements.seq_last
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_last
     : forall (A B : Type) (rA : A -> B -> Type),
       Prosa_Implementation_Refinements_Refinements_refines (A -> List_inst1 A -> A) 
         (B -> List_inst1 B -> B)
         (Prosa_Implementation_Refinements_Refinements_hrespectful A B (List_inst1 A -> A)
            (List_inst1 B -> B) rA
            (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 A) 
               (List_inst1 B) A B (Prosa_Implementation_Refinements_Refinements_list_R A B rA) rA))
         (Prosa_Implementation_Refinements_Refinements_seq_last A)
         (Prosa_Implementation_Refinements_Refinements_seq_last B)
```
