From mathcomp Require Import ssreflect ssrbool ssrnat eqtype fintype.

Definition BoolRel (bR bL : bool) : Prop := bR = bL.

Definition BoolPropRel (b : bool) (p : Prop) : Prop := b = true <-> p.

Definition NatRel (nR nL : nat) : Prop := nR = nL.

Definition FunRel {AR AL BR BL}
    (RA : AR -> AL -> Prop) (RB : BR -> BL -> Prop)
    (fR : AR -> BR) (fL : AL -> BL) : Prop :=
  forall xR xL, RA xR xL -> RB (fR xR) (fL xL).

Definition PredRel {AR AL}
    (RA : AR -> AL -> Prop) (pR : AR -> Prop) (pL : AL -> Prop) : Prop :=
  forall xR xL, RA xR xL -> (pR xR <-> pL xL).
