(** Isolated theorem-level trust boundary between Rocq [Prop] and the [SProp]
    used by rocq-lean-import for Lean propositions.

    This is the minimal fragment of the lf-lean approach required here:
    [StrictlyInhabited P] embeds the truth of [P] in [SProp], while the single
    axiom below permits elimination back into [Prop]. *)

Variant StrictlyInhabited (P : Prop) : SProp :=
| strictly_inhabits : P -> StrictlyInhabited P.

Arguments strictly_inhabits {P} _.

(** TRUST BOUNDARY. Every theorem using it must carry the dedicated status
    [CERTIFIED_WITH_PROP_SPROP_BRIDGE]. *)
Axiom prop_sprop_trusted_elim :
  forall P : Prop, StrictlyInhabited P -> P.

Record PropSPropRel (P : Prop) (Q : SProp) : Prop := {
  prop_to_sprop : P -> Q;
  sprop_to_prop : Q -> P
}.

Definition prop_sprop_rel_intro (P : Prop) (Q : SProp)
    (toQ : P -> Q) (toStrictP : Q -> StrictlyInhabited P) :
    PropSPropRel P Q :=
  {| prop_to_sprop := toQ;
     sprop_to_prop := fun q => prop_sprop_trusted_elim P (toStrictP q) |}.

Print Assumptions prop_sprop_rel_intro.
