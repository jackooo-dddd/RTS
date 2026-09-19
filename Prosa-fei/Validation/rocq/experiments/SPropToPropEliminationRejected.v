(** Negative kernel probe for the sole Prop/SProp foundation axiom. *)
Variant ProbeStrictTruth (P : Prop) : SProp :=
| probe_strict_truth : P -> ProbeStrictTruth P.

Arguments probe_strict_truth {P} _.

Fail Definition forbidden_sprop_to_prop (P : Prop) :
    ProbeStrictTruth P -> P :=
  fun h =>
    match h with
    | probe_strict_truth p => p
    end.
