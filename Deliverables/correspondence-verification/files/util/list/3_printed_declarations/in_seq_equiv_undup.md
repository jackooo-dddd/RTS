# `in_seq_equiv_undup`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.in_seq_equiv_undup`
- Lean: `Prosa.Util.List.in_seq_equiv_undup`
- Certificate: `in_seq_equiv_undup_statement_certificate`

## Official Rocq

```coq
in_seq_equiv_undup :
forall {X : eqType} (xs : seq (Equality.sort X)) (x : Equality.sort X), (x \in @undup X xs) = (x \in xs)

in_seq_equiv_undup is not universe polymorphic
Arguments in_seq_equiv_undup {X} xs%seq_scope x
in_seq_equiv_undup is opaque
Expands to: Constant prosa.util.list.in_seq_equiv_undup
Declared in library prosa.util.list, line 286, characters 6-24
@in_seq_equiv_undup
     : forall (X : eqType) (xs : seq (Equality.sort X)) (x : Equality.sort X),
       (x \in @undup X xs) = (x \in xs)
```

## Lean

```lean
@Prosa.Util.List.in_seq_equiv_undup : ∀ {T : Type u_1} [inst : DecidableEq T] (xs : List T) (x : T),
  decide (x ∈ xs.eraseDups) = decide (x ∈ xs)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_in_seq_equiv_undup
     : forall (T : Type) (inst_3 : DecidableEq T) 
         (xs : List T) (x : T),
       @eq Bool
         (Decidable_decide
            (Membership_mem T (List T) (List_instMembership T)
               (List_eraseDups T
                  (instBEqOfDecidableEq T inst_3) xs)
               x)
            (List_instDecidableMemOfLawfulBEq T
               (instBEqOfDecidableEq T inst_3)
               (instLawfulBEq T inst_3) x
               (List_eraseDups T
                  (instBEqOfDecidableEq T inst_3) xs)))
         (Decidable_decide (Membership_mem T (List T) (List_instMembership T) xs x)
            (List_instDecidableMemOfLawfulBEq T
               (instBEqOfDecidableEq T inst_3)
               (instLawfulBEq T inst_3) x xs))
```
