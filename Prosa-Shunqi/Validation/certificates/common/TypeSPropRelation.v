From LeanImport Require Import Lean.

(** Some MathComp theorem statements expose an informative view (notably a
    universally quantified [reflect]) whose closed statement lives in
    [Type]. This relation records the deliberate translation of that view to
    an imported Lean proposition. Individual certificates must still
    construct both directions structurally; the relation itself introduces
    no axiom. It is kept in its own module so extending the bridge library does
    not invalidate certificates that depend only on [LogicalRelation]. *)
Record TypeSPropRel (A : Type) (Q : SProp) : Type := {
  type_to_sprop : A -> Q;
  sprop_to_type : Q -> A
}.

Print Assumptions TypeSPropRel.
