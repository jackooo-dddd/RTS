# `mem_bigcat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.mem_bigcat`
- Lean: `Prosa.Util.Bigcat.mem_bigcat`
- Certificate: `mem_bigcat_statement_certificate`

## Official Rocq

```coq
mem_bigcat :
forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) (x : Equality.sort X)
  (y : Equality.sort Y) (s : @pred_sort (Equality.sort X) (seq_predType X)),
is_true (x \in s) ->
is_true (y \in f x) ->
is_true
  (y
     \in @bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] s
           (fun x0 : Equality.sort X =>
            @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) x0 (@cat (Equality.sort Y)) true (f x0)))

mem_bigcat is not universe polymorphic
Arguments mem_bigcat X Y f%function_scope x y s _ _
mem_bigcat is opaque
Expands to: Constant prosa.util.bigcat.mem_bigcat
Declared in library prosa.util.bigcat, line 157, characters 8-18
mem_bigcat
     : forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) (x : Equality.sort X)
         (y : Equality.sort Y) (s : @pred_sort (Equality.sort X) (seq_predType X)),
       is_true (x \in s) ->
       is_true (y \in f x) ->
       is_true
         (y
            \in @bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] s
                  (fun x0 : Equality.sort X =>
                   @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) x0 (@cat (Equality.sort Y)) true
                     (f x0)))
```

## Lean

```lean
@Prosa.Util.Bigcat.mem_bigcat : ∀ {X : Type u_1} {Y : Type u_2} [DecidableEq X] [DecidableEq Y] (f : X → List Y) (x : X)
  (y : Y) (s : List X), x ∈ s → y ∈ f x → y ∈ Prosa.Util.Bigcat.bigCatSeqAll s f
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_mem_bigcat
     : forall X Y : Type,
       DecidableEq X ->
       DecidableEq Y ->
       forall (f : X -> List Y) (x : X) (y : Y) (s : List X),
       Membership_mem X (List X) (List_instMembership X) s x ->
       Membership_mem Y (List Y) (List_instMembership Y) (f x) y ->
       Membership_mem Y (List Y) (List_instMembership Y) (Prosa_Util_Bigcat_bigCatSeqAll X Y s f) y
```
