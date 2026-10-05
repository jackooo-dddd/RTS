# `nodup_sort_2cons_eq`

- Kind (Rocq): Remark
- Rocq: `prosa.util.nondecreasing.nodup_sort_2cons_eq`
- Lean: `Prosa.Util.Nondecreasing.nodup_sort_2cons_eq`
- Certificate: `nodup_sort_2cons_eq_correspondence_certificate`

## Official Rocq

```coq
nodup_sort_2cons_eq :
forall {X : eqType} (x : Equality.sort X) (xs : seq (Equality.sort X)),
@undup X [:: x, x & xs] = @undup X (x :: xs)

nodup_sort_2cons_eq is not universe polymorphic
Arguments nodup_sort_2cons_eq {X} x xs%seq_scope
nodup_sort_2cons_eq is opaque
Expands to: Constant prosa.util.nondecreasing.nodup_sort_2cons_eq
Declared in library prosa.util.nondecreasing, line 314, characters 9-28
@nodup_sort_2cons_eq
     : forall (X : eqType) (x : Equality.sort X) (xs : seq (Equality.sort X)),
       @undup X [:: x, x & xs] = @undup X (x :: xs)
```

## Lean

```lean
@Prosa.Util.Nondecreasing.nodup_sort_2cons_eq : ∀ {X : Type u_1} [inst : DecidableEq X] (x : X) (xs : List X),
  (x :: x :: xs).dedup = (x :: xs).dedup
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_nodup_sort_2cons_eq
     : forall (X : Type) (inst_3 : DecidableEq X)
         (x : X) (xs : List X),
       @eq (List X)
         (List_dedup X inst_3
            (List_cons X x (List_cons X x xs)))
         (List_dedup X inst_3 (List_cons X x xs))
```
