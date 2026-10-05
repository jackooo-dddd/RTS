From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedUnitGrowth.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  UnitGrowthCorrespondence.
Require Import GeneratedUnitGrowthSource.

(** Exact target-type guards. These guards bind the independently checked
    statements to the actual theorem constants. The semantic certificates
    below never reference a guard or target/source theorem proof. *)
Definition imported_unit_growth_function_k_steps_bounded_type_guard :
  forall f : Lean.Nat -> Lean.Nat,
    ug_unit_growth_target f -> forall x k : Lean.Nat,
      ug_le (f (ug_add x k)) (ug_add k (f x)) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_unit_growth_function_k_steps_bounded.

Definition imported_slowed_respects_pointwise_leq_type_guard :
  forall (f F : Lean.Nat -> Lean.Nat) (delta : Lean.Nat),
    ug_unit_growth_target f ->
    (forall x : Lean.Nat, ug_le x delta -> ug_le (f x) (F x)) ->
    ug_le (f delta)
      (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed F delta) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed_respects_pointwise_leq.

Definition imported_slowed_is_unit_step_type_guard :
  forall f : Lean.Nat -> Lean.Nat,
    ug_unit_growth_target
      (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed f) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed_is_unit_step.

Definition imported_slowed_respects_monotone_type_guard :
  forall f : Lean.Nat -> Lean.Nat,
    ug_monotone_target f ->
    ug_monotone_target
      (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed f) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed_respects_monotone.

Definition imported_slowed_never_exceeds_type_guard :
  forall (f : Lean.Nat -> Lean.Nat) (x : Lean.Nat),
    ug_le (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed f x) (f x) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed_never_exceeds.

Definition imported_exists_intermediate_point_type_guard :
  forall f : Lean.Nat -> Lean.Nat,
    ug_unit_growth_target f ->
    forall x1 x2 : Lean.Nat, ug_le x1 x2 ->
    forall y : Lean.Nat,
      Lean.And (ug_le (f x1) y) (ug_lt y (f x2)) ->
      ImportedUnitGrowth.Exists Lean.Nat (fun xmid =>
        Lean.And (Lean.And (ug_le x1 xmid) (ug_lt xmid x2))
          (Lean.eq (f xmid) y)) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_exists_intermediate_point.

Definition imported_exists_intermediate_point_leq_type_guard :
  forall f : Lean.Nat -> Lean.Nat,
    ug_unit_growth_target f ->
    forall x1 x2 : Lean.Nat, ug_le x1 x2 ->
    forall y : Lean.Nat,
      Lean.And (ug_le (f x1) y) (ug_le y (f x2)) ->
      ImportedUnitGrowth.Exists Lean.Nat (fun xmid =>
        Lean.And (Lean.And (ug_le x1 xmid) (ug_le xmid x2))
          (Lean.eq (f xmid) y)) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_exists_intermediate_point_leq.

Definition imported_exists_first_intermediate_point_type_guard :
  forall (P : Lean.Nat -> ImportedUnitGrowth.Bool)
      (t1 t2 : Lean.Nat),
    ug_le t1 t2 ->
    Lean.eq (P t1) ImportedUnitGrowth.Bool_false ->
    Lean.eq (P t2) ImportedUnitGrowth.Bool_true ->
    ImportedUnitGrowth.Exists Lean.Nat (fun t =>
      Lean.And (Lean.And (ug_lt t1 t) (ug_le t t2))
        (Lean.And
          (forall x : Lean.Nat,
            Lean.And (ug_le t1 x) (ug_lt x t) ->
            Lean.eq (P x) ImportedUnitGrowth.Bool_false)
          (Lean.eq (P t) ImportedUnitGrowth.Bool_true))) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_exists_first_intermediate_point.

Definition imported_bound_preserved_under_slowed_type_guard :
  forall (f : Lean.Nat -> Lean.Nat) (delta A F : Lean.Nat),
    ug_le A (ug_sub F (f delta)) ->
    ug_le A
      (ug_sub F (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed f delta)) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_bound_preserved_under_slowed.

Definition imported_slowed_subtraction_value_preservation_type_guard :
  forall (f : Lean.Nat -> Lean.Nat) (Delta : Lean.Nat),
    ug_monotone_target f ->
    ImportedUnitGrowth.Exists Lean.Nat (fun delta =>
      Lean.And (ug_le delta Delta)
        (Lean.eq (ug_sub Delta (f Delta))
          (ug_sub delta
            (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed f delta)))) :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed_subtraction_value_preservation.

Lemma unit_growth_function_k_steps_bounded_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (GeneratedUnitGrowthSource.unit_growth_function fR ->
       forall x k : nat, is_true (leq (fR (x + k)) (k + fR x)))
      (ug_unit_growth_target fL ->
       forall x k : Lean.Nat,
         ug_le (fL (ug_add x k)) (ug_add k (fL x))).
Proof.
  intros fR fL Hf. apply prop_sprop_rel_intro.
  - intros HR HunitL xL kL.
    set (xR := sub_nat_to_rocq xL).
    set (kR := sub_nat_to_rocq kL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hk : SubNatRel kR kL := sub_nat_rel_surjective kL.
    have HunitR := sprop_to_prop _ _
      (ug_unit_growth_correspondence fR fL Hf) HunitL.
    have Hxk := ug_add_correspondence _ _ _ _ Hx Hk.
    have Hfxk := Hf _ _ Hxk.
    have Hfx := Hf _ _ Hx.
    have Hright := ug_add_correspondence _ _ _ _ Hk Hfx.
    exact (prop_to_sprop _ _
      (ug_le_correspondence _ _ _ _ Hfxk Hright)
      (HR HunitR xR kR)).
  - intro HL. apply strictly_inhabits. intros HunitR xR kR.
    have Hx := sub_nat_rel_canonical xR.
    have Hk := sub_nat_rel_canonical kR.
    have HunitL := prop_to_sprop _ _
      (ug_unit_growth_correspondence fR fL Hf) HunitR.
    have Hxk := ug_add_correspondence _ _ _ _ Hx Hk.
    have Hfxk := Hf _ _ Hxk.
    have Hfx := Hf _ _ Hx.
    have Hright := ug_add_correspondence _ _ _ _ Hk Hfx.
    exact (sprop_to_prop _ _
      (ug_le_correspondence _ _ _ _ Hfxk Hright)
      (HL HunitL (sub_nat_to_imported xR) (sub_nat_to_imported kR))).
Qed.

Lemma ug_strict_interval_witness_correspondence :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall x1R x1L x2R x2L yR yL,
      SubNatRel x1R x1L -> SubNatRel x2R x2L -> SubNatRel yR yL ->
      PropSPropRel
        (exists xmid : nat,
          (is_true (leq x1R xmid) /\ is_true (ltn xmid x2R)) /\
          Logic.eq (fR xmid) yR)
        (ImportedUnitGrowth.Exists Lean.Nat (fun xmid =>
          Lean.And (Lean.And (ug_le x1L xmid) (ug_lt xmid x2L))
            (Lean.eq (fL xmid) yL))).
Proof.
  intros fR fL Hf x1R x1L x2R x2L yR yL Hx1 Hx2 Hy.
  apply prop_sprop_rel_intro.
  - intros [xR [[HloR HhiR] HeqR]].
    have Hx := sub_nat_rel_canonical xR.
    have Hfx := Hf _ _ Hx.
    exact (ImportedUnitGrowth.Exists_intro Lean.Nat _ (sub_nat_to_imported xR)
      (Lean.And_intro _ _
        (Lean.And_intro _ _
          (prop_to_sprop _ _
            (ug_le_correspondence _ _ _ _ Hx1 Hx) HloR)
          (prop_to_sprop _ _
            (ug_lt_correspondence _ _ _ _ Hx Hx2) HhiR))
        (prop_to_sprop _ _
          (ug_eq_correspondence _ _ _ _ Hfx Hy) HeqR))).
  - intro HL. destruct HL as [xL Hbody].
    destruct Hbody as [Hrange HeqL]. destruct Hrange as [HloL HhiL].
    apply strictly_inhabits.
    set (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hfx := Hf _ _ Hx.
    exists xR. split; first split.
    + exact (sprop_to_prop _ _
        (ug_le_correspondence _ _ _ _ Hx1 Hx) HloL).
    + exact (sprop_to_prop _ _
        (ug_lt_correspondence _ _ _ _ Hx Hx2) HhiL).
    + exact (sprop_to_prop _ _
        (ug_eq_correspondence _ _ _ _ Hfx Hy) HeqL).
Qed.

Lemma ug_closed_interval_witness_correspondence :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall x1R x1L x2R x2L yR yL,
      SubNatRel x1R x1L -> SubNatRel x2R x2L -> SubNatRel yR yL ->
      PropSPropRel
        (exists xmid : nat,
          (is_true (leq x1R xmid) /\ is_true (leq xmid x2R)) /\
          Logic.eq (fR xmid) yR)
        (ImportedUnitGrowth.Exists Lean.Nat (fun xmid =>
          Lean.And (Lean.And (ug_le x1L xmid) (ug_le xmid x2L))
            (Lean.eq (fL xmid) yL))).
Proof.
  intros fR fL Hf x1R x1L x2R x2L yR yL Hx1 Hx2 Hy.
  apply prop_sprop_rel_intro.
  - intros [xR [[HloR HhiR] HeqR]].
    have Hx := sub_nat_rel_canonical xR.
    have Hfx := Hf _ _ Hx.
    exact (ImportedUnitGrowth.Exists_intro Lean.Nat _ (sub_nat_to_imported xR)
      (Lean.And_intro _ _
        (Lean.And_intro _ _
          (prop_to_sprop _ _
            (ug_le_correspondence _ _ _ _ Hx1 Hx) HloR)
          (prop_to_sprop _ _
            (ug_le_correspondence _ _ _ _ Hx Hx2) HhiR))
        (prop_to_sprop _ _
          (ug_eq_correspondence _ _ _ _ Hfx Hy) HeqR))).
  - intro HL. destruct HL as [xL Hbody].
    destruct Hbody as [Hrange HeqL]. destruct Hrange as [HloL HhiL].
    apply strictly_inhabits.
    set (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hfx := Hf _ _ Hx.
    exists xR. split; first split.
    + exact (sprop_to_prop _ _
        (ug_le_correspondence _ _ _ _ Hx1 Hx) HloL).
    + exact (sprop_to_prop _ _
        (ug_le_correspondence _ _ _ _ Hx Hx2) HhiL).
    + exact (sprop_to_prop _ _
        (ug_eq_correspondence _ _ _ _ Hfx Hy) HeqL).
Qed.

Lemma exists_intermediate_point_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall x1R x1L x2R x2L yR yL,
      SubNatRel x1R x1L -> SubNatRel x2R x2L -> SubNatRel yR yL ->
      PropSPropRel
        (GeneratedUnitGrowthSource.unit_growth_function fR ->
         is_true (leq x1R x2R) ->
         (is_true (leq (fR x1R) yR) /\
          is_true (ltn yR (fR x2R))) ->
         exists xmid : nat,
           (is_true (leq x1R xmid) /\ is_true (ltn xmid x2R)) /\
           Logic.eq (fR xmid) yR)
        (ug_unit_growth_target fL -> ug_le x1L x2L ->
         Lean.And (ug_le (fL x1L) yL) (ug_lt yL (fL x2L)) ->
         ImportedUnitGrowth.Exists Lean.Nat (fun xmid =>
           Lean.And (Lean.And (ug_le x1L xmid) (ug_lt xmid x2L))
             (Lean.eq (fL xmid) yL))).
Proof.
  intros fR fL Hf x1R x1L x2R x2L yR yL Hx1 Hx2 Hy.
  have Hunit := ug_unit_growth_correspondence fR fL Hf.
  have Hinter := ug_le_correspondence _ _ _ _ Hx1 Hx2.
  have Hfx1 := Hf _ _ Hx1. have Hfx2 := Hf _ _ Hx2.
  have Hlo := ug_le_correspondence _ _ _ _ Hfx1 Hy.
  have Hhi := ug_lt_correspondence _ _ _ _ Hy Hfx2.
  have Hexists := ug_strict_interval_witness_correspondence
    fR fL Hf x1R x1L x2R x2L yR yL Hx1 Hx2 Hy.
  apply prop_sprop_rel_intro.
  - intros HR HunitL HinterL HbetweenL.
    destruct HbetweenL as [HloL HhiL].
    apply (prop_to_sprop _ _ Hexists).
    apply HR.
    + exact (sprop_to_prop _ _ Hunit HunitL).
    + exact (sprop_to_prop _ _ Hinter HinterL).
    + split; [exact (sprop_to_prop _ _ Hlo HloL) |
              exact (sprop_to_prop _ _ Hhi HhiL)].
  - intro HL. apply strictly_inhabits.
    intros HunitR HinterR [HloR HhiR].
    apply (sprop_to_prop _ _ Hexists).
    apply HL.
    + exact (prop_to_sprop _ _ Hunit HunitR).
    + exact (prop_to_sprop _ _ Hinter HinterR).
    + exact (Lean.And_intro _ _
        (prop_to_sprop _ _ Hlo HloR)
        (prop_to_sprop _ _ Hhi HhiR)).
Qed.

Lemma exists_intermediate_point_leq_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall x1R x1L x2R x2L yR yL,
      SubNatRel x1R x1L -> SubNatRel x2R x2L -> SubNatRel yR yL ->
      PropSPropRel
        (GeneratedUnitGrowthSource.unit_growth_function fR ->
         is_true (leq x1R x2R) ->
         (is_true (leq (fR x1R) yR) /\
          is_true (leq yR (fR x2R))) ->
         exists xmid : nat,
           (is_true (leq x1R xmid) /\ is_true (leq xmid x2R)) /\
           Logic.eq (fR xmid) yR)
        (ug_unit_growth_target fL -> ug_le x1L x2L ->
         Lean.And (ug_le (fL x1L) yL) (ug_le yL (fL x2L)) ->
         ImportedUnitGrowth.Exists Lean.Nat (fun xmid =>
           Lean.And (Lean.And (ug_le x1L xmid) (ug_le xmid x2L))
             (Lean.eq (fL xmid) yL))).
Proof.
  intros fR fL Hf x1R x1L x2R x2L yR yL Hx1 Hx2 Hy.
  have Hunit := ug_unit_growth_correspondence fR fL Hf.
  have Hinter := ug_le_correspondence _ _ _ _ Hx1 Hx2.
  have Hfx1 := Hf _ _ Hx1. have Hfx2 := Hf _ _ Hx2.
  have Hlo := ug_le_correspondence _ _ _ _ Hfx1 Hy.
  have Hhi := ug_le_correspondence _ _ _ _ Hy Hfx2.
  have Hexists := ug_closed_interval_witness_correspondence
    fR fL Hf x1R x1L x2R x2L yR yL Hx1 Hx2 Hy.
  apply prop_sprop_rel_intro.
  - intros HR HunitL HinterL HbetweenL.
    destruct HbetweenL as [HloL HhiL].
    apply (prop_to_sprop _ _ Hexists).
    apply HR.
    + exact (sprop_to_prop _ _ Hunit HunitL).
    + exact (sprop_to_prop _ _ Hinter HinterL).
    + split; [exact (sprop_to_prop _ _ Hlo HloL) |
              exact (sprop_to_prop _ _ Hhi HhiL)].
  - intro HL. apply strictly_inhabits.
    intros HunitR HinterR [HloR HhiR].
    apply (sprop_to_prop _ _ Hexists).
    apply HL.
    + exact (prop_to_sprop _ _ Hunit HunitR).
    + exact (prop_to_sprop _ _ Hinter HinterR).
    + exact (Lean.And_intro _ _
        (prop_to_sprop _ _ Hlo HloR)
        (prop_to_sprop _ _ Hhi HhiR)).
Qed.

(** This source shell deliberately retains MathComp's Boolean conjunctions.
    The following guard is definitionally equal to the exact post-Section
    type acquired from the pinned v0.6 source. *)
Definition ug_source_exists_first_result
    (P : nat -> bool) (t1 t2 : nat) : Prop :=
  exists t : nat,
    is_true (ltn t1 t && leq t t2) /\
    (forall x : nat,
      is_true (leq t1 x && ltn x t) -> is_true (~~ P x)) /\
    is_true (P t).

Definition ug_source_exists_first_statement
    (P : nat -> bool) (t1 t2 : nat) : Prop :=
  is_true (leq t1 t2) ->
  is_true (~~ P t1) ->
  is_true (P t2) ->
  ug_source_exists_first_result P t1 t2.

Definition generated_exists_first_intermediate_point_type_guard :
  Logic.eq
    GeneratedUnitGrowthSource.statement_exists_first_intermediate_point
    (forall (P : nat -> bool) (t1 t2 : nat),
      ug_source_exists_first_statement P t1 t2) :=
  Logic.eq_refl _.

Definition ug_target_exists_first_result
    (P : Lean.Nat -> ImportedUnitGrowth.Bool)
    (t1 t2 : Lean.Nat) : SProp :=
  ImportedUnitGrowth.Exists Lean.Nat (fun t =>
    Lean.And (Lean.And (ug_lt t1 t) (ug_le t t2))
      (Lean.And
        (forall x : Lean.Nat,
          Lean.And (ug_le t1 x) (ug_lt x t) ->
          Lean.eq (P x) ImportedUnitGrowth.Bool_false)
        (Lean.eq (P t) ImportedUnitGrowth.Bool_true))).

Definition ug_target_exists_first_statement
    (P : Lean.Nat -> ImportedUnitGrowth.Bool)
    (t1 t2 : Lean.Nat) : SProp :=
  ug_le t1 t2 ->
  Lean.eq (P t1) ImportedUnitGrowth.Bool_false ->
  Lean.eq (P t2) ImportedUnitGrowth.Bool_true ->
  ug_target_exists_first_result P t1 t2.

Lemma ug_first_result_backward_strict :
  forall (PR : nat -> bool)
      (PL : Lean.Nat -> ImportedUnitGrowth.Bool),
    UgBoolFunRel PR PL ->
    forall t1R t1L t2R t2L,
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      ug_target_exists_first_result PL t1L t2L ->
      StrictlyInhabited (ug_source_exists_first_result PR t1R t2R).
Proof.
  intros PR PL Hpred t1R t1L t2R t2L Ht1 Ht2 HresultL.
  destruct HresultL as [tL HbodyL].
  destruct HbodyL as [HboundsL HrestL].
  destruct HboundsL as [HlowerL HupperL].
  destruct HrestL as [HallL HtrueL].
  set (tR := sub_nat_to_rocq tL).
  have Ht : SubNatRel tR tL := sub_nat_rel_surjective tL.
  apply strictly_inhabits. exists tR. split.
  - apply/andP. split.
    + exact (sprop_to_prop _ _
        (ug_lt_correspondence _ _ _ _ Ht1 Ht) HlowerL).
    + exact (sprop_to_prop _ _
        (ug_le_correspondence _ _ _ _ Ht Ht2) HupperL).
  - split.
    + intros xR HboundsR. move/andP: HboundsR => [HlowerR HupperR].
      have Hx := sub_nat_rel_canonical xR.
      have HfalseL := HallL (sub_nat_to_imported xR)
        (Lean.And_intro _ _
          (prop_to_sprop _ _
            (ug_le_correspondence _ _ _ _ Ht1 Hx) HlowerR)
          (prop_to_sprop _ _
            (ug_lt_correspondence _ _ _ _ Hx Ht) HupperR)).
      exact (sprop_to_prop _ _
        (ug_bool_false_correspondence _ _ (Hpred _ _ Hx)) HfalseL).
    + exact (sprop_to_prop _ _
        (ug_bool_true_correspondence _ _ (Hpred _ _ Ht)) HtrueL).
Qed.

Lemma exists_first_intermediate_point_statement_certificate :
  forall (PR : nat -> bool)
      (PL : Lean.Nat -> ImportedUnitGrowth.Bool),
    UgBoolFunRel PR PL ->
    forall t1R t1L t2R t2L,
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      PropSPropRel
        (ug_source_exists_first_statement PR t1R t2R)
        (ug_target_exists_first_statement PL t1L t2L).
Proof.
  intros PR PL Hpred t1R t1L t2R t2L Ht1 Ht2.
  have Hinterval := ug_le_correspondence _ _ _ _ Ht1 Ht2.
  have HPt1 := Hpred _ _ Ht1.
  have HPt2 := Hpred _ _ Ht2.
  apply prop_sprop_rel_intro.
  - intros HR HintervalL HfalseL HtrueL.
    have HresultR := HR
      (sprop_to_prop _ _ Hinterval HintervalL)
      (sprop_to_prop _ _
        (ug_bool_false_correspondence _ _ HPt1) HfalseL)
      (sprop_to_prop _ _
        (ug_bool_true_correspondence _ _ HPt2) HtrueL).
    destruct HresultR as [tR [HboundsR [HallR HtrueR]]].
    have HlowerR := ug_and_left _ _ HboundsR.
    have HupperR := ug_and_right _ _ HboundsR.
    have Ht := sub_nat_rel_canonical tR.
    exact (ImportedUnitGrowth.Exists_intro Lean.Nat _
      (sub_nat_to_imported tR)
      (Lean.And_intro _ _
        (Lean.And_intro _ _
          (prop_to_sprop _ _
            (ug_lt_correspondence _ _ _ _ Ht1 Ht) HlowerR)
          (prop_to_sprop _ _
            (ug_le_correspondence _ _ _ _ Ht Ht2) HupperR))
        (Lean.And_intro _ _
          (fun xL HboundsL =>
            let xR := sub_nat_to_rocq xL in
            let Hx : SubNatRel xR xL := sub_nat_rel_surjective xL in
            let Hpx := Hpred xR xL Hx in
            match HboundsL with
            | Lean.And_intro HlowerL HupperL =>
                prop_to_sprop _ _
                  (ug_bool_false_correspondence _ _ Hpx)
                  (HallR xR
                    (ug_and_intro _ _
                      (sprop_to_prop _ _
                        (ug_le_correspondence _ _ _ _ Ht1 Hx) HlowerL)
                      (sprop_to_prop _ _
                        (ug_lt_correspondence _ _ _ _ Hx Ht) HupperL)))
            end)
          (prop_to_sprop _ _
            (ug_bool_true_correspondence _ _ (Hpred _ _ Ht)) HtrueR)))).
  - intro HL. apply strictly_inhabits.
    intros HintervalR HfalseR HtrueR.
    have HresultL := HL
      (prop_to_sprop _ _ Hinterval HintervalR)
      (prop_to_sprop _ _
        (ug_bool_false_correspondence _ _ HPt1) HfalseR)
      (prop_to_sprop _ _
        (ug_bool_true_correspondence _ _ HPt2) HtrueR).
    exact (interpret_strict _
      (ug_first_result_backward_strict
        PR PL Hpred t1R t1L t2R t2L Ht1 Ht2 HresultL)).
Qed.

Lemma ug_pointwise_le_up_to_correspondence :
  forall (fR FR : nat -> nat) (fL FL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL -> SubNatFunRel FR FL ->
    forall deltaR deltaL, SubNatRel deltaR deltaL ->
    PropSPropRel
      (forall x : nat, is_true (leq x deltaR) ->
        is_true (leq (fR x) (FR x)))
      (forall x : Lean.Nat, ug_le x deltaL -> ug_le (fL x) (FL x)).
Proof.
  intros fR FR fL FL Hf HF deltaR deltaL Hdelta.
  apply prop_sprop_rel_intro.
  - intros HR xL HxL. set (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have HxR := sprop_to_prop _ _
      (ug_le_correspondence _ _ _ _ Hx Hdelta) HxL.
    have Hfx := Hf _ _ Hx. have HFx := HF _ _ Hx.
    exact (prop_to_sprop _ _
      (ug_le_correspondence _ _ _ _ Hfx HFx) (HR xR HxR)).
  - intro HL. apply strictly_inhabits. intros xR HxR.
    have Hx := sub_nat_rel_canonical xR.
    have HxL := prop_to_sprop _ _
      (ug_le_correspondence _ _ _ _ Hx Hdelta) HxR.
    have Hfx := Hf _ _ Hx. have HFx := HF _ _ Hx.
    exact (sprop_to_prop _ _
      (ug_le_correspondence _ _ _ _ Hfx HFx) (HL _ HxL)).
Qed.

Lemma slowed_respects_pointwise_leq_statement_certificate :
  forall (fR FR : nat -> nat) (fL FL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL -> SubNatFunRel FR FL ->
    forall deltaR deltaL, SubNatRel deltaR deltaL ->
    PropSPropRel
      (GeneratedUnitGrowthSource.unit_growth_function fR ->
       (forall x : nat, is_true (leq x deltaR) ->
          is_true (leq (fR x) (FR x))) ->
       is_true (leq (fR deltaR)
         (GeneratedUnitGrowthSource.slowed FR deltaR)))
      (ug_unit_growth_target fL ->
       (forall x : Lean.Nat, ug_le x deltaL -> ug_le (fL x) (FL x)) ->
       ug_le (fL deltaL)
         (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed FL deltaL)).
Proof.
  intros fR FR fL FL Hf HF deltaR deltaL Hdelta.
  have HslowF := ug_slowed_correspondence FR FL HF.
  apply prop_sprop_rel_intro.
  - intros HR HunitL HpointL.
    have HunitR := sprop_to_prop _ _
      (ug_unit_growth_correspondence fR fL Hf) HunitL.
    have HpointR := sprop_to_prop _ _
      (ug_pointwise_le_up_to_correspondence
        fR FR fL FL Hf HF deltaR deltaL Hdelta) HpointL.
    have HresultR := HR HunitR HpointR.
    have Hfdelta := Hf _ _ Hdelta.
    have Hslowdelta := HslowF _ _ Hdelta.
    exact (prop_to_sprop _ _
      (ug_le_correspondence _ _ _ _ Hfdelta Hslowdelta) HresultR).
  - intro HL. apply strictly_inhabits. intros HunitR HpointR.
    have HunitL := prop_to_sprop _ _
      (ug_unit_growth_correspondence fR fL Hf) HunitR.
    have HresultL := HL HunitL (prop_to_sprop _ _
      (ug_pointwise_le_up_to_correspondence
        fR FR fL FL Hf HF deltaR deltaL Hdelta) HpointR).
    have Hfdelta := Hf _ _ Hdelta.
    have Hslowdelta := HslowF _ _ Hdelta.
    exact (sprop_to_prop _ _
      (ug_le_correspondence _ _ _ _ Hfdelta Hslowdelta) HresultL).
Qed.

Lemma slowed_is_unit_step_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (GeneratedUnitGrowthSource.unit_growth_function
        (GeneratedUnitGrowthSource.slowed fR))
      (ug_unit_growth_target
        (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed fL)).
Proof.
  intros fR fL Hf. apply ug_unit_growth_correspondence.
  exact (ug_slowed_correspondence fR fL Hf).
Qed.

Lemma slowed_respects_monotone_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    PropSPropRel
      (prosa.util.rel.monotone leq fR ->
       prosa.util.rel.monotone leq
         (GeneratedUnitGrowthSource.slowed fR))
      (ug_monotone_target fL ->
       ug_monotone_target
         (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed fL)).
Proof.
  intros fR fL Hf. have Hmono := ug_monotone_correspondence fR fL Hf.
  have Hslow := ug_slowed_correspondence fR fL Hf.
  have HslowMono := ug_monotone_correspondence _ _ Hslow.
  apply prop_sprop_rel_intro.
  - intros HR HmonoL. apply (prop_to_sprop _ _ HslowMono).
    apply HR. exact (sprop_to_prop _ _ Hmono HmonoL).
  - intro HL. apply strictly_inhabits. intro HmonoR.
    apply (sprop_to_prop _ _ HslowMono).
    apply HL. exact (prop_to_sprop _ _ Hmono HmonoR).
Qed.

Lemma slowed_never_exceeds_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall xR xL, SubNatRel xR xL ->
    PropSPropRel
      (is_true (leq (GeneratedUnitGrowthSource.slowed fR xR) (fR xR)))
      (ug_le (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed fL xL)
        (fL xL)).
Proof.
  intros fR fL Hf xR xL Hx.
  have Hslow := ug_slowed_correspondence fR fL Hf _ _ Hx.
  have Hfx := Hf _ _ Hx.
  exact (ug_le_correspondence _ _ _ _ Hslow Hfx).
Qed.

Lemma bound_preserved_under_slowed_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall deltaR deltaL AR AL FR FL,
      SubNatRel deltaR deltaL -> SubNatRel AR AL -> SubNatRel FR FL ->
      PropSPropRel
        (is_true (leq AR (FR - fR deltaR)) ->
         is_true (leq AR
           (FR - GeneratedUnitGrowthSource.slowed fR deltaR)))
        (ug_le AL (ug_sub FL (fL deltaL)) ->
         ug_le AL
           (ug_sub FL
             (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed fL deltaL))).
Proof.
  intros fR fL Hf deltaR deltaL AR AL FR FL Hdelta HA HF.
  have Hfdelta := Hf _ _ Hdelta.
  have Hslowdelta := ug_slowed_correspondence fR fL Hf _ _ Hdelta.
  have HsubF := ug_sub_correspondence _ _ _ _ HF Hfdelta.
  have HsubSlow := ug_sub_correspondence _ _ _ _ HF Hslowdelta.
  have Hleft := ug_le_correspondence _ _ _ _ HA HsubF.
  have Hright := ug_le_correspondence _ _ _ _ HA HsubSlow.
  apply prop_sprop_rel_intro.
  - intros HR HpremL. apply (prop_to_sprop _ _ Hright).
    apply HR. exact (sprop_to_prop _ _ Hleft HpremL).
  - intro HL. apply strictly_inhabits. intro HpremR.
    apply (sprop_to_prop _ _ Hright).
    apply HL. exact (prop_to_sprop _ _ Hleft HpremR).
Qed.

Lemma ug_subtraction_witness_correspondence :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall DeltaR DeltaL, SubNatRel DeltaR DeltaL ->
    PropSPropRel
      (exists delta : nat,
        is_true (leq delta DeltaR) /\
        Logic.eq (DeltaR - fR DeltaR)
          (delta - GeneratedUnitGrowthSource.slowed fR delta))
      (ImportedUnitGrowth.Exists Lean.Nat (fun delta =>
        Lean.And (ug_le delta DeltaL)
          (Lean.eq (ug_sub DeltaL (fL DeltaL))
            (ug_sub delta
              (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed fL delta))))).
Proof.
  intros fR fL Hf DeltaR DeltaL HDelta.
  have Hslow := ug_slowed_correspondence fR fL Hf.
  apply prop_sprop_rel_intro.
  - intros [deltaR [HleR HeqR]].
    have Hdelta := sub_nat_rel_canonical deltaR.
    have HfDelta := Hf _ _ HDelta.
    have Hfslow := Hslow _ _ Hdelta.
    have Hleft := ug_sub_correspondence _ _ _ _ HDelta HfDelta.
    have Hright := ug_sub_correspondence _ _ _ _ Hdelta Hfslow.
    exact (ImportedUnitGrowth.Exists_intro Lean.Nat _
      (sub_nat_to_imported deltaR)
      (Lean.And_intro _ _
        (prop_to_sprop _ _
          (ug_le_correspondence _ _ _ _ Hdelta HDelta) HleR)
        (prop_to_sprop _ _
          (ug_eq_correspondence _ _ _ _ Hleft Hright) HeqR))).
  - intro HL. destruct HL as [deltaL Hbody].
    destruct Hbody as [HleL HeqL]. apply strictly_inhabits.
    set (deltaR := sub_nat_to_rocq deltaL).
    have Hdelta : SubNatRel deltaR deltaL := sub_nat_rel_surjective deltaL.
    have HfDelta := Hf _ _ HDelta.
    have Hfslow := Hslow _ _ Hdelta.
    have Hleft := ug_sub_correspondence _ _ _ _ HDelta HfDelta.
    have Hright := ug_sub_correspondence _ _ _ _ Hdelta Hfslow.
    exists deltaR. split.
    + exact (sprop_to_prop _ _
        (ug_le_correspondence _ _ _ _ Hdelta HDelta) HleL).
    + exact (sprop_to_prop _ _
        (ug_eq_correspondence _ _ _ _ Hleft Hright) HeqL).
Qed.

Lemma slowed_subtraction_value_preservation_statement_certificate :
  forall (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat),
    SubNatFunRel fR fL ->
    forall DeltaR DeltaL, SubNatRel DeltaR DeltaL ->
    PropSPropRel
      (prosa.util.rel.monotone leq fR ->
       exists delta : nat,
         is_true (leq delta DeltaR) /\
         Logic.eq (DeltaR - fR DeltaR)
           (delta - GeneratedUnitGrowthSource.slowed fR delta))
      (ug_monotone_target fL ->
       ImportedUnitGrowth.Exists Lean.Nat (fun delta =>
         Lean.And (ug_le delta DeltaL)
           (Lean.eq (ug_sub DeltaL (fL DeltaL))
             (ug_sub delta
               (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed fL delta))))).
Proof.
  intros fR fL Hf DeltaR DeltaL HDelta.
  have Hmono := ug_monotone_correspondence fR fL Hf.
  have Hexists := ug_subtraction_witness_correspondence
    fR fL Hf DeltaR DeltaL HDelta.
  apply prop_sprop_rel_intro.
  - intros HR HmonoL. apply (prop_to_sprop _ _ Hexists).
    apply HR. exact (sprop_to_prop _ _ Hmono HmonoL).
  - intro HL. apply strictly_inhabits. intro HmonoR.
    apply (sprop_to_prop _ _ Hexists).
    apply HL. exact (prop_to_sprop _ _ Hmono HmonoR).
Qed.

Print Assumptions unit_growth_function_k_steps_bounded_statement_certificate.
Print Assumptions slowed_respects_pointwise_leq_statement_certificate.
Print Assumptions slowed_is_unit_step_statement_certificate.
Print Assumptions slowed_respects_monotone_statement_certificate.
Print Assumptions slowed_never_exceeds_statement_certificate.
Print Assumptions exists_intermediate_point_statement_certificate.
Print Assumptions exists_intermediate_point_leq_statement_certificate.
Print Assumptions exists_first_intermediate_point_statement_certificate.
Print Assumptions bound_preserved_under_slowed_statement_certificate.
Print Assumptions slowed_subtraction_value_preservation_statement_certificate.
