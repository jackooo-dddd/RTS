# `bigcat_filter_eq_filter_bigcat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.bigcat_filter_eq_filter_bigcat`
- Lean: `Prosa.Util.Bigcat.bigcat_filter_eq_filter_bigcat`
- Certificate: `bigcat_filter_eq_filter_bigcat_statement_certificate`

## Official Rocq

```coq
bigcat_filter_eq_filter_bigcat :
forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) (xss : seq (Equality.sort X))
  (P : Equality.sort Y -> bool),
            (fun xs : Equality.sort X =>
             @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) xs (@cat (Equality.sort Y)) true (f xs))
   | P x] =
@bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] xss
  (fun xs : Equality.sort X =>
   @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) xs (@cat (Equality.sort Y)) true
     [seq x <- f xs | P x])

bigcat_filter_eq_filter_bigcat is not universe polymorphic
Arguments bigcat_filter_eq_filter_bigcat X Y f%function_scope xss%seq_scope P%function_scope
bigcat_filter_eq_filter_bigcat is opaque
Expands to: Constant prosa.util.bigcat.bigcat_filter_eq_filter_bigcat
Declared in library prosa.util.bigcat, line 193, characters 8-38
bigcat_filter_eq_filter_bigcat
     : forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) (xss : seq (Equality.sort X))
         (P : Equality.sort Y -> bool),
       [seq x <- @bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] xss
                   (fun xs : Equality.sort X =>
                    @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) xs (@cat (Equality.sort Y)) true
                      (f xs))
          | P x] =
       @bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] xss
         (fun xs : Equality.sort X =>
          @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) xs (@cat (Equality.sort Y)) true
            [seq x <- f xs | P x])
```

## Lean

```lean
@Prosa.Util.Bigcat.bigcat_filter_eq_filter_bigcat : ∀ {X : Type u_1} {Y : Type u_2} [DecidableEq X] [DecidableEq Y]
  (f : X → List Y) (xss : List X) (P : Y → Bool),
  List.filter P (Prosa.Util.Bigcat.bigCatSeqAll xss f) = Prosa.Util.Bigcat.bigCatSeqAll xss fun x => List.filter P (f x)
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_bigcat_filter_eq_filter_bigcat
     : forall X Y : Type,
       DecidableEq X ->
       DecidableEq Y ->
       forall (f : X -> List Y) (xss : List X) (P : Y -> Bool),
       @eq (List Y) (List_filter Y P (Prosa_Util_Bigcat_bigCatSeqAll X Y xss f))
         (Prosa_Util_Bigcat_bigCatSeqAll X Y xss (fun x : X => List_filter Y P (f x)))
```
