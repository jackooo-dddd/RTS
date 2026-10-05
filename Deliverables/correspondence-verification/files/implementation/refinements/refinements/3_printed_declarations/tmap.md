# `tmap`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.refinements.tmap`
- Lean: `Prosa.Implementation.Refinements.Refinements.tmap`
- Certificate: `tmap_correspondence`

## Official Rocq

```coq
tmap : forall {X Y : Type}, (X -> Y) -> X * X -> Y * Y

tmap is not universe polymorphic
Arguments tmap {X Y}%_type_scope f%_function_scope t
tmap is transparent
Expands to: Constant prosa.implementation.refinements.refinements.tmap
Declared in library prosa.implementation.refinements.refinements, line 41, characters 11-15
@tmap
     : forall X Y : Type, (X -> Y) -> X * X -> Y * Y
```

Body:

```coq
tmap =
fun (X Y : Type) (f : X -> Y) (t : X * X) => (f t.1, f t.2)
     : forall {X Y : Type}, (X -> Y) -> X * X -> Y * Y

Arguments tmap {X Y}%_type_scope f%_function_scope t
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.tmap : {X Y : Type} → (X → Y) → X × X → Y × Y
```

Body:

```lean
def Prosa.Implementation.Refinements.Refinements.tmap : {X Y : Type} → (X → Y) → X × X → Y × Y :=
fun {X Y} f t => (f t.1, f t.2)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_tmap
     : forall X Y : Type, (X -> Y) -> Prod_inst3 X X -> Prod_inst3 Y Y
```

Body:

```coq
Prosa_Implementation_Refinements_Refinements_tmap@{} =
fun (X Y : Type) (f : X -> Y) (t : Prod_inst3 X X) =>
Prod_mk_inst3 Y Y (f (Prod_fst_inst3 X X t)) (f (Prod_snd_inst3 X X t))
     : forall X Y : Type, (X -> Y) -> Prod_inst3 X X -> Prod_inst3 Y Y

Arguments Prosa_Implementation_Refinements_Refinements_tmap (X Y)%_type_scope f%_function_scope t
```
