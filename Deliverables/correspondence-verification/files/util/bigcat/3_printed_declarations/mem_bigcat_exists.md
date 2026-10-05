# `mem_bigcat_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.mem_bigcat_exists`
- Lean: `Prosa.Util.Bigcat.mem_bigcat_exists`
- Certificate: `mem_bigcat_exists_statement_certificate`

## Official Rocq

```coq
mem_bigcat_exists :
forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) {P : Equality.sort X -> bool}
  (s : seq (Equality.sort X)) (y : Equality.sort Y),
is_true
  (y
     \in @bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] s
           (fun x : Equality.sort X =>
            @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) x (@cat (Equality.sort Y)) (P x) (f x))) ->
exists x : Equality.sort X, is_true (x \in s) /\ is_true (y \in f x)

mem_bigcat_exists is not universe polymorphic
Arguments mem_bigcat_exists X Y f%function_scope {P}%function_scope s%seq_scope y _
mem_bigcat_exists is opaque
Expands to: Constant prosa.util.bigcat.mem_bigcat_exists
Declared in library prosa.util.bigcat, line 173, characters 8-25
mem_bigcat_exists
     : forall (X Y : eqType) (f : Equality.sort X -> seq (Equality.sort Y)) (P : Equality.sort X -> bool)
         (s : seq (Equality.sort X)) (y : Equality.sort Y),
       is_true
         (y
            \in @bigop.bigop.body (seq (Equality.sort Y)) (Equality.sort X) [::] s
                  (fun x : Equality.sort X =>
                   @bigop.BigBody (seq (Equality.sort Y)) (Equality.sort X) x (@cat (Equality.sort Y)) 
                     (P x) (f x))) ->
       exists x : Equality.sort X, is_true (x \in s) /\ is_true (y \in f x)
```

## Lean

```lean
@Prosa.Util.Bigcat.mem_bigcat_exists : ∀ {X : Type u_1} {Y : Type u_2} [DecidableEq X] [DecidableEq Y] (f : X → List Y)
  (P : X → Bool) (s : List X), ∀ y ∈ Prosa.Util.Bigcat.bigCatSeq s P f, ∃ x ∈ s, y ∈ f x
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_mem_bigcat_exists
     : forall X Y : Type,
       DecidableEq X ->
       DecidableEq Y ->
       forall (f : X -> List Y) (P : X -> Bool) (s : List X) (y : Y),
       Membership_mem Y (List Y) (List_instMembership Y) (Prosa_Util_Bigcat_bigCatSeq X Y s P f) y ->
       Exists X
         (fun x : X =>
          And (Membership_mem X (List X) (List_instMembership X) s x)
            (Membership_mem Y (List Y) (List_instMembership Y) (f x) y))
```
