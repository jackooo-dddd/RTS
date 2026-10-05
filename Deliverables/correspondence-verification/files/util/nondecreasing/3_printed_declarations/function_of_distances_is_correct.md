# `function_of_distances_is_correct`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.nondecreasing.function_of_distances_is_correct`
- Lean: `Prosa.Util.Nondecreasing.function_of_distances_is_correct`
- Certificate: `function_of_distances_is_correct_correspondence_certificate`

## Official Rocq

```coq
function_of_distances_is_correct :
forall (xs : seq nat) (n : nat), @nth nat 0 (distances xs) n = @nth nat 0 xs n.+1 - @nth nat 0 xs n

function_of_distances_is_correct is not universe polymorphic
Arguments function_of_distances_is_correct xs%seq_scope n%nat_scope
function_of_distances_is_correct is opaque
Expands to: Constant prosa.util.nondecreasing.function_of_distances_is_correct
Declared in library prosa.util.nondecreasing, line 515, characters 8-40
function_of_distances_is_correct
     : forall (xs : seq nat) (n : nat), @nth nat 0 (distances xs) n = @nth nat 0 xs n.+1 - @nth nat 0 xs n
```

## Lean

```lean
Prosa.Util.Nondecreasing.function_of_distances_is_correct : ∀ (xs : List ℕ) (n : ℕ),
  Prosa.Util.Nondecreasing.nthD✝ (Prosa.Util.Nondecreasing.distances xs) n =
    Prosa.Util.Nondecreasing.nthD✝ xs (n + 1) - Prosa.Util.Nondecreasing.nthD✝ xs n
```

## Lean, imported into Rocq

```coq
Prosa_Util_Nondecreasing_function_of_distances_is_correct
     : forall (xs : List_inst1 Nat) (n : Nat),
       @eq Nat
         (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD
            (Prosa_Util_Nondecreasing_distances xs) n)
         (HSub_hSub_inst7 Nat Nat Nat (instHSub_inst1 Nat instSubNat)
            (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs
               (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
                  (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
            (_private_Prosa_Util_Nondecreasing0_Prosa_Util_Nondecreasing_nthD xs n))
```
