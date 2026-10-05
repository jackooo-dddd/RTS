# `count_predUI'`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.count_predUI'`
- Lean: `Prosa.Util.List.count_predUI'`
- Certificate: `count_predUI_statement_certificate`

## Official Rocq

```coq
count_predUI' :
forall (P1 P2 : pred nat) (xs : seq nat),
@count nat (pred_of_simpl (@predU nat P1 P2)) xs =
@count nat P1 xs + @count nat P2 xs - @count nat (pred_of_simpl (@predI nat P1 P2)) xs

count_predUI' is not universe polymorphic
Arguments count_predUI' P1 P2 xs%seq_scope
count_predUI' is opaque
Expands to: Constant prosa.util.list.count_predUI'
Declared in library prosa.util.list, line 859, characters 6-19
count_predUI'
     : forall (P1 P2 : pred nat) (xs : seq nat),
       @count nat (pred_of_simpl (@predU nat P1 P2)) xs =
       @count nat P1 xs + @count nat P2 xs - @count nat (pred_of_simpl (@predI nat P1 P2)) xs
```

## Lean

```lean
Prosa.Util.List.count_predUI' : ∀ (P₁ P₂ : ℕ → Bool) (xs : List ℕ),
  List.countP (fun x => P₁ x || P₂ x) xs =
    List.countP P₁ xs + List.countP P₂ xs - List.countP (fun x => P₁ x && P₂ x) xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_count_predUI'
     : forall (P_UU2081_ P_UU2082_ : Nat -> Bool) (xs : List_inst1 Nat),
       @eq Nat (List_countP_inst1 Nat (fun x : Nat => Bool_or (P_UU2081_ x) (P_UU2082_ x)) xs)
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
            (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (List_countP_inst1 Nat P_UU2081_ xs)
               (List_countP_inst1 Nat P_UU2082_ xs))
            (List_countP_inst1 Nat (fun x : Nat => Bool_and (P_UU2081_ x) (P_UU2082_ x)) xs))
```
