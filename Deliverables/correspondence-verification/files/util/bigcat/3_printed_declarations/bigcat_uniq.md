# `bigcat_uniq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.bigcat_uniq`
- Lean: `Prosa.Util.Bigcat.bigcat_uniq`
- Certificate: `bigcat_uniq_statement_certificate`

## Official Rocq

```coq
bigcat_uniq :
forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) {xs : seq (Equality.sort X)}
  {P : pred (Equality.sort X)},
(forall x : Equality.sort X, is_true (P x) -> is_true (@uniq Y (f x))) ->
(forall (x : Equality.sort Y) (y z : Equality.sort X), is_true (x \in f y) -> is_true (x \in f z) -> y = z) ->
is_true (@uniq X xs) ->
is_true
  (@uniq Y
     (@bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] xs
        (fun x : Equality.sort X =>
         @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) x (@cat (Equality.sort Y)) (P x) (f x))))

bigcat_uniq is not universe polymorphic
Arguments bigcat_uniq X Y f%function_scope {xs}%seq_scope {P}
  (H_uniq_f H_no_elements_in_common)%function_scope _
bigcat_uniq is opaque
Expands to: Constant prosa.util.bigcat.bigcat_uniq
Declared in library prosa.util.bigcat, line 224, characters 10-21
bigcat_uniq
     : forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) (xs : seq (Equality.sort X))
         (P : pred (Equality.sort X)),
       (forall x : Equality.sort X, is_true (P x) -> is_true (@uniq Y (f x))) ->
       (forall (x : Equality.sort Y) (y z : Equality.sort X),
        is_true (x \in f y) -> is_true (x \in f z) -> y = z) ->
       is_true (@uniq X xs) ->
       is_true
         (@uniq Y
            (@bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] xs
               (fun x : Equality.sort X =>
                @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) x (@cat (Equality.sort Y)) 
                  (P x) (f x))))
```

## Lean

```lean
@Prosa.Util.Bigcat.bigcat_uniq : ∀ {X : Type u_1} {Y : Type u_2} [DecidableEq X] [DecidableEq Y] (f : X → List Y)
  {xs : List X} {P : X → Bool},
  (∀ (x : X), P x = true → (f x).Nodup) →
    (∀ (x : Y) (y z : X), x ∈ f y → x ∈ f z → y = z) → xs.Nodup → (Prosa.Util.Bigcat.bigCatSeq xs P f).Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_bigcat_uniq
     : forall X Y : Type,
       DecidableEq X ->
       DecidableEq Y ->
       forall (f : X -> List Y) (xs : List X) (P : X -> Bool),
       (forall x : X, @eq Bool (P x) Bool_true -> List_Nodup Y (f x)) ->
       (forall (x : Y) (y z : X),
        Membership_mem Y (List Y) (List_instMembership Y) (f y) x ->
        Membership_mem Y (List Y) (List_instMembership Y) (f z) x -> @eq X y z) ->
       List_Nodup X xs -> List_Nodup Y (Prosa_Util_Bigcat_bigCatSeq X Y xs P f)
```
