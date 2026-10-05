# `iota_is_increasing_sequence`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.iota_is_increasing_sequence`
- Lean: `Prosa.Util.Nondecreasing.iota_is_increasing_sequence`
- Certificate: `iota_is_increasing_sequence_correspondence_certificate`

## Official Rocq

```coq
iota_is_increasing_sequence :
forall (a b : nat) (P : nat -> bool), increasing_sequence [seq x <- bigop.index_iota a b | P x]

iota_is_increasing_sequence is not universe polymorphic
Arguments iota_is_increasing_sequence (a b)%nat_scope P%function_scope n1 n2 _
iota_is_increasing_sequence is opaque
Expands to: Constant prosa.util.nondecreasing.iota_is_increasing_sequence
Declared in library prosa.util.nondecreasing, line 40, characters 8-35
iota_is_increasing_sequence
     : forall (a b : nat) (P : nat -> bool), increasing_sequence [seq x <- bigop.index_iota a b | P x]
```

## Lean

```lean
Prosa.Util.Nondecreasing.iota_is_increasing_sequence : ∀ (a b : ℕ) (P : ℕ → Bool),
  Prosa.Util.Nondecreasing.increasing_sequence (List.filter (fun x => P x) (Prosa.Util.List.index_iota a b))
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_iota_is_increasing_sequence
     : forall (a b : Nat) (P : Nat -> Bool),
       Prosa_Util_Nondecreasing_increasing_sequence
         (List_filter_inst1 Nat
            (fun n____at___Init_Prelude427477602__hygCtx__hyg40 : Nat =>
             P n____at___Init_Prelude427477602__hygCtx__hyg40)
            (Prosa_Util_List_index_iota a b))
```
