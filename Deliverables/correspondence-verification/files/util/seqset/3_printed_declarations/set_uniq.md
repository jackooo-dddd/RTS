# `set_uniq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.seqset.set_uniq`
- Lean: `Prosa.Util.Seqset.set_uniq`
- Certificate: `seqset_set_uniq_statement_correspondence_certificate`

## Official Rocq

```coq
set_uniq : forall {T : eqType} (s : {setEquality.sort T}), is_true (@uniq T (@_set_seq T s))

set_uniq is not universe polymorphic
Arguments set_uniq {T} s
set_uniq is opaque
Expands to: Constant prosa.util.seqset.set_uniq
Declared in library prosa.util.seqset, line 39, characters 8-16
@set_uniq
     : forall (T : eqType) (s : {setEquality.sort T}), is_true (@uniq T (@_set_seq T s))
```

## Lean

```lean
@Prosa.Util.Seqset.set_uniq : ∀ {T : Type u_1} [inst : DecidableEq T] (s : Prosa.Util.Seqset.set T), s.val.Nodup
```

## Lean, imported into Rocq

```coq
Prosa_Util_Seqset_set_uniq
     : forall (T : Type) (inst_3 : DecidableEq T)
         (s : Prosa_Util_Seqset_set T inst_3),
       List_Nodup T (Prosa_Util_Seqset_set_val T inst_3 s)
```
