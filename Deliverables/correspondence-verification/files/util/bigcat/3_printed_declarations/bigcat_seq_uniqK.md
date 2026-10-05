# `bigcat_seq_uniqK`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.bigcat_seq_uniqK`
- Lean: `Prosa.Util.Bigcat.bigcat_seq_uniqK`
- Certificate: `bigcat_seq_uniqK_statement_certificate`

## Official Rocq

```coq
bigcat_seq_uniqK :
forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) (g : Equality.sort Y -> Equality.sort X),
(forall (x : Equality.sort X) (y : Equality.sort Y), is_true (y \in f x) -> g y = x) ->
forall (y : Equality.sort X) (xs : @pred_sort (Equality.sort X) (seq_predType X)),
is_true (y \in xs) ->
is_true (@uniq X xs) ->
@bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] xs
  (fun x : Equality.sort X =>
   @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) x (@cat (Equality.sort Y)) true
     [seq x' <- f x | g x' == y]) =
f y

bigcat_seq_uniqK is not universe polymorphic
Arguments bigcat_seq_uniqK X Y (f g H_g_cancels_f)%function_scope y xs _ _
bigcat_seq_uniqK is opaque
Expands to: Constant prosa.util.bigcat.bigcat_seq_uniqK
Declared in library prosa.util.bigcat, line 275, characters 10-26
bigcat_seq_uniqK
     : forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y))
         (g : Equality.sort Y -> Equality.sort X),
       (forall (x : Equality.sort X) (y : Equality.sort Y), is_true (y \in f x) -> g y = x) ->
       forall (y : Equality.sort X) (xs : @pred_sort (Equality.sort X) (seq_predType X)),
       is_true (y \in xs) ->
       is_true (@uniq X xs) ->
       @bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] xs
         (fun x : Equality.sort X =>
          @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) x (@cat (Equality.sort Y)) true
            [seq x' <- f x | g x' == y]) =
       f y
```

## Lean

```lean
@Prosa.Util.Bigcat.bigcat_seq_uniqK : ∀ {X : Type u_1} {Y : Type u_2} [inst : DecidableEq X] [DecidableEq Y]
  (f : X → List Y) (g : Y → X),
  (∀ (x : X), ∀ y ∈ f x, g y = x) →
    ∀ (y : X) (xs : List X),
      y ∈ xs →
        xs.Nodup → (Prosa.Util.Bigcat.bigCatSeqAll xs fun x => List.filter (fun x' => decide (g x' = y)) (f x)) = f y
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_bigcat_seq_uniqK
     : forall (X Y : Type) (inst_4 : DecidableEq X),
       DecidableEq Y ->
       forall (f : X -> List Y) (g : Y -> X),
       (forall (x : X) (y : Y), Membership_mem Y (List Y) (List_instMembership Y) (f x) y -> @eq X (g y) x) ->
       forall (y : X) (xs : List X),
       Membership_mem X (List X) (List_instMembership X) xs y ->
       List_Nodup X xs ->
       @eq (List Y)
         (Prosa_Util_Bigcat_bigCatSeqAll X Y xs
            (fun x : X =>
             List_filter Y
               (fun x' : Y =>
                Decidable_decide (@eq X (g x') y)
                  (inst_4 (g x') y))
               (f x)))
         (f y)
```
