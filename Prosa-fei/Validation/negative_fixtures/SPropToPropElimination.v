(** This file is expected not to compile. It records the kernel restriction
    that motivates the sole axiom in PropSPropFoundation. *)
Variant ProbeStrictTruth (P : Prop) : SProp :=
| probe_strict_truth : P -> ProbeStrictTruth P.

Arguments probe_strict_truth {P} _.

Definition forbidden_sprop_to_prop (P : Prop) :
    ProbeStrictTruth P -> P :=
  fun h =>
    match h with
    | probe_strict_truth p => p
    end.
