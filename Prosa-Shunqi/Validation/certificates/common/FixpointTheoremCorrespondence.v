From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFixpoint.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence FixpointBaseCorrespondence
  FixpointMonotoneCorrespondence.
Require Import GeneratedFixpointSourceAll.

(** Exact compiled theorem-type guard.  It is deliberately separate from the
    semantic certificate, which never uses the target theorem proof. *)
Definition fixpoint_ffpf_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat) (h s x fuel : Lean.Nat),
    Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
      f s h fuel)
      (ImportedFixpoint.Option_some_inst1 Lean.Nat x) ->
    Lean.eq x (f x).

Definition fixpoint_ffpf_exact_type_guard : fixpoint_ffpf_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_ffpf_finds_fixpoint.

Lemma fixpoint_ffpf_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_ffpf_finds_fixpoint
    fixpoint_ffpf_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL sL xL fuelL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (sR := sub_nat_to_rocq sL).
    set (xR := sub_nat_to_rocq xL).
    set (fuelR := sub_nat_to_rocq fuelL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hs := sub_nat_rel_surjective sL.
    have Hx := sub_nat_rel_surjective xL.
    have Hfuel := sub_nat_rel_surjective fuelL.
    have Hbody := fixpoint_ffpf_body_correspondence
      fR fL sR hR fuelR xR sL hL fuelL xL Hf Hs Hh Hfuel Hx.
    exact (prop_to_sprop _ _ Hbody (HR fR hR sR xR fuelR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR sR xR fuelR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hs := sub_nat_rel_canonical sR.
    have Hx := sub_nat_rel_canonical xR.
    have Hfuel := sub_nat_rel_canonical fuelR.
    have Hbody := fixpoint_ffpf_body_correspondence
      fR fL sR hR fuelR xR
      (sub_nat_to_imported sR) (sub_nat_to_imported hR)
      (sub_nat_to_imported fuelR) (sub_nat_to_imported xR)
      Hf Hs Hh Hfuel Hx.
    exact (sprop_to_prop _ _ Hbody
      (HL fL (sub_nat_to_imported hR) (sub_nat_to_imported sR)
        (sub_nat_to_imported xR) (sub_nat_to_imported fuelR))).
Qed.

Print Assumptions fixpoint_ffpf_statement_certificate.

Definition fixpoint_ffp_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat) (h x : Lean.Nat),
    Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint f h)
      (ImportedFixpoint.Option_some_inst1 Lean.Nat x) ->
    Lean.eq x (f x).

Definition fixpoint_ffp_exact_type_guard : fixpoint_ffp_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_ffp_finds_fixpoint.

Lemma fixpoint_ffp_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_ffp_finds_fixpoint
    fixpoint_ffp_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL xL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (xR := sub_nat_to_rocq xL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hx := sub_nat_rel_surjective xL.
    have Hbody := fixpoint_ffp_body_correspondence
      fR fL hR xR hL xL Hf Hh Hx.
    exact (prop_to_sprop _ _ Hbody (HR fR hR xR)).
  - intro HL. apply strictly_inhabits. intros fR hR xR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hx := sub_nat_rel_canonical xR.
    have Hbody := fixpoint_ffp_body_correspondence
      fR fL hR xR (sub_nat_to_imported hR) (sub_nat_to_imported xR)
      Hf Hh Hx.
    exact (sprop_to_prop _ _ Hbody
      (HL fL (sub_nat_to_imported hR) (sub_nat_to_imported xR))).
Qed.

Print Assumptions fixpoint_ffp_statement_certificate.

Definition fixpoint_no_skipped_target_type : SProp :=
  forall f : Lean.Nat -> Lean.Nat,
    fixpoint_target_monotone f ->
    fixpoint_target_lt Lean.Nat_zero
      (f (Lean.Nat_succ Lean.Nat_zero)) ->
    forall a c : Lean.Nat, Lean.eq c (f a) ->
    forall b : Lean.Nat,
      fixpoint_target_le a b -> fixpoint_target_lt b c ->
      ImportedFixpoint.Ne Lean.Nat b (f b).

Definition fixpoint_no_skipped_exact_type_guard :
    fixpoint_no_skipped_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_no_fixpoint_skipped.

Lemma fixpoint_no_skipped_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_no_fixpoint_skipped
    fixpoint_no_skipped_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL HmonoL HposL aL cL HeqL bL HleL HltL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (aR := sub_nat_to_rocq aL).
    set (bR := sub_nat_to_rocq bL).
    set (cR := sub_nat_to_rocq cL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Ha := sub_nat_rel_surjective aL.
    have Hb := sub_nat_rel_surjective bL.
    have Hc := sub_nat_rel_surjective cL.
    have HmonoR := sprop_to_prop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoL.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposL.
    have Hfa := Hf aR aL Ha.
    have HeqR := sprop_to_prop _ _
      (sub_nat_eq_correspondence cR cL (fR aR) (fL aL) Hc Hfa)
      HeqL.
    have HleR := sprop_to_prop _ _
      (fixpoint_le_correspondence aR aL bR bL Ha Hb) HleL.
    have HltR := sprop_to_prop _ _
      (fixpoint_lt_correspondence bR bL cR cL Hb Hc) HltL.
    have HrangeR : is_true (leq aR bR && ltn bR cR).
    { apply/andP. split; assumption. }
    have Hfb := Hf bR bL Hb.
    exact (prop_to_sprop _ _
      (fixpoint_ne_correspondence bR bL (fR bR) (fL bL) Hb Hfb)
      (HR fR HmonoR HposR aR cR HeqR bR HrangeR)).
  - intro HL. apply strictly_inhabits.
    intros fR HmonoR HposR aR cR HeqR bR HrangeR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Ha := sub_nat_rel_canonical aR.
    have Hb := sub_nat_rel_canonical bR.
    have Hc := sub_nat_rel_canonical cR.
    have HmonoL := prop_to_sprop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoR.
    have Hf1 := Hf (S O) (sub_nat_to_imported (S O))
      (sub_nat_rel_canonical (S O)).
    have HposL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (sub_nat_to_imported (S O)))
        (sub_nat_rel_canonical O) Hf1) HposR.
    have Hfa := Hf aR (sub_nat_to_imported aR) Ha.
    have HeqL := prop_to_sprop _ _
      (sub_nat_eq_correspondence cR (sub_nat_to_imported cR)
        (fR aR) (fL (sub_nat_to_imported aR)) Hc Hfa) HeqR.
    move/andP: HrangeR => [HleR HltR].
    have HleL := prop_to_sprop _ _
      (fixpoint_le_correspondence aR (sub_nat_to_imported aR)
        bR (sub_nat_to_imported bR) Ha Hb) HleR.
    have HltL := prop_to_sprop _ _
      (fixpoint_lt_correspondence bR (sub_nat_to_imported bR)
        cR (sub_nat_to_imported cR) Hb Hc) HltR.
    have Hfb := Hf bR (sub_nat_to_imported bR) Hb.
    exact (sprop_to_prop _ _
      (fixpoint_ne_correspondence bR (sub_nat_to_imported bR)
        (fR bR) (fL (sub_nat_to_imported bR)) Hb Hfb)
      (HL fL HmonoL HposL (sub_nat_to_imported aR)
        (sub_nat_to_imported cR) HeqL (sub_nat_to_imported bR)
        HleL HltL)).
Qed.

Print Assumptions fixpoint_no_skipped_statement_certificate.

Definition fixpoint_ffp_none_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat) (h : Lean.Nat),
    fixpoint_target_monotone f ->
    fixpoint_target_lt Lean.Nat_zero
      (f (Lean.Nat_succ Lean.Nat_zero)) ->
    Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint f h)
      (ImportedFixpoint.Option_none_inst1 Lean.Nat) ->
    forall x : Lean.Nat,
      Lean.And (fixpoint_target_lt Lean.Nat_zero x)
        (fixpoint_target_lt x h) ->
      ImportedFixpoint.Ne Lean.Nat x (f x).

Definition fixpoint_ffp_none_exact_type_guard :
    fixpoint_ffp_none_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_ffp_finds_none.

Lemma fixpoint_ffp_none_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_ffp_finds_none
    fixpoint_ffp_none_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL HmonoL HposL HnoneL xL HrangeL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (xR := sub_nat_to_rocq xL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hx := sub_nat_rel_surjective xL.
    have HmonoR := sprop_to_prop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoL.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposL.
    have HnoneR := sprop_to_prop _ _
      (fixpoint_none_eq_correspondence fR fL hR hL Hf Hh) HnoneL.
    destruct HrangeL as [HloL HhiL].
    have HloR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero xR xL
        (sub_nat_rel_canonical O) Hx) HloL.
    have HhiR := sprop_to_prop _ _
      (fixpoint_lt_correspondence xR xL hR hL Hx Hh) HhiL.
    have HrangeR : is_true (ltn O xR && ltn xR hR).
    { apply/andP. split; assumption. }
    have Hfx := Hf xR xL Hx.
    exact (prop_to_sprop _ _
      (fixpoint_ne_correspondence xR xL (fR xR) (fL xL) Hx Hfx)
      (HR fR hR HmonoR HposR HnoneR xR HrangeR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR HmonoR HposR HnoneR xR HrangeR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hx := sub_nat_rel_canonical xR.
    have HmonoL := prop_to_sprop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoR.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposR.
    have HnoneL := prop_to_sprop _ _
      (fixpoint_none_eq_correspondence fR fL hR
        (sub_nat_to_imported hR) Hf Hh) HnoneR.
    move/andP: HrangeR => [HloR HhiR].
    have HloL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero xR
        (sub_nat_to_imported xR) (sub_nat_rel_canonical O) Hx) HloR.
    have HhiL := prop_to_sprop _ _
      (fixpoint_lt_correspondence xR (sub_nat_to_imported xR)
        hR (sub_nat_to_imported hR) Hx Hh) HhiR.
    have Hfx := Hf xR (sub_nat_to_imported xR) Hx.
    exact (sprop_to_prop _ _
      (fixpoint_ne_correspondence xR (sub_nat_to_imported xR)
        (fR xR) (fL (sub_nat_to_imported xR)) Hx Hfx)
      (HL fL (sub_nat_to_imported hR) HmonoL HposL HnoneL
        (sub_nat_to_imported xR) (Lean.And_intro _ _ HloL HhiL))).
Qed.

Print Assumptions fixpoint_ffp_none_statement_certificate.

Definition fixpoint_ffpf_none_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat) (h : Lean.Nat),
    fixpoint_target_monotone f ->
    fixpoint_target_lt Lean.Nat_zero
      (f (Lean.Nat_succ Lean.Nat_zero)) ->
    forall s fuel : Lean.Nat,
      fixpoint_target_le s (f s) ->
      fixpoint_target_le (fixpoint_target_sub h s) fuel ->
      Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
        f s h fuel) (ImportedFixpoint.Option_none_inst1 Lean.Nat) ->
      forall x : Lean.Nat,
        Lean.And (fixpoint_target_le s x) (fixpoint_target_lt x h) ->
        ImportedFixpoint.Ne Lean.Nat x (f x).

Definition fixpoint_ffpf_none_exact_type_guard :
    fixpoint_ffpf_none_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_ffpf_finds_none.

Lemma fixpoint_ffpf_none_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_ffpf_finds_none
    fixpoint_ffpf_none_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL HmonoL HposL sL fuelL HstepL HfuelL
      HnoneL xL HrangeL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (sR := sub_nat_to_rocq sL).
    set (fuelR := sub_nat_to_rocq fuelL).
    set (xR := sub_nat_to_rocq xL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hs := sub_nat_rel_surjective sL.
    have Hfuel := sub_nat_rel_surjective fuelL.
    have Hx := sub_nat_rel_surjective xL.
    have HmonoR := sprop_to_prop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoL.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposL.
    have Hfs := Hf sR sL Hs.
    have HstepR := sprop_to_prop _ _
      (fixpoint_le_correspondence sR sL (fR sR) (fL sL)
        Hs Hfs) HstepL.
    have Hsub := fixpoint_sub_correspondence hR hL sR sL Hh Hs.
    have HfuelR := sprop_to_prop _ _
      (fixpoint_le_correspondence (hR - sR)
        (fixpoint_target_sub hL sL) fuelR fuelL Hsub Hfuel) HfuelL.
    have HnoneR := sprop_to_prop _ _
      (fixpoint_from_none_eq_correspondence
        fR fL sR hR fuelR sL hL fuelL Hf Hs Hh Hfuel) HnoneL.
    destruct HrangeL as [HloL HhiL].
    have HloR := sprop_to_prop _ _
      (fixpoint_le_correspondence sR sL xR xL Hs Hx) HloL.
    have HhiR := sprop_to_prop _ _
      (fixpoint_lt_correspondence xR xL hR hL Hx Hh) HhiL.
    have HrangeR : is_true (leq sR xR && ltn xR hR).
    { apply/andP. split; assumption. }
    have Hfx := Hf xR xL Hx.
    exact (prop_to_sprop _ _
      (fixpoint_ne_correspondence xR xL (fR xR) (fL xL) Hx Hfx)
      (HR fR hR HmonoR HposR sR fuelR HstepR HfuelR
        HnoneR xR HrangeR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR HmonoR HposR sR fuelR HstepR HfuelR
      HnoneR xR HrangeR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hs := sub_nat_rel_canonical sR.
    have Hfuel := sub_nat_rel_canonical fuelR.
    have Hx := sub_nat_rel_canonical xR.
    have HmonoL := prop_to_sprop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoR.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposR.
    have Hfs := Hf sR (sub_nat_to_imported sR) Hs.
    have HstepL := prop_to_sprop _ _
      (fixpoint_le_correspondence sR (sub_nat_to_imported sR)
        (fR sR) (fL (sub_nat_to_imported sR)) Hs Hfs) HstepR.
    have Hsub := fixpoint_sub_correspondence hR
      (sub_nat_to_imported hR) sR (sub_nat_to_imported sR) Hh Hs.
    have HfuelL := prop_to_sprop _ _
      (fixpoint_le_correspondence (hR - sR)
        (fixpoint_target_sub (sub_nat_to_imported hR)
          (sub_nat_to_imported sR)) fuelR
        (sub_nat_to_imported fuelR) Hsub Hfuel) HfuelR.
    have HnoneL := prop_to_sprop _ _
      (fixpoint_from_none_eq_correspondence fR fL sR hR fuelR
        (sub_nat_to_imported sR) (sub_nat_to_imported hR)
        (sub_nat_to_imported fuelR) Hf Hs Hh Hfuel) HnoneR.
    move/andP: HrangeR => [HloR HhiR].
    have HloL := prop_to_sprop _ _
      (fixpoint_le_correspondence sR (sub_nat_to_imported sR)
        xR (sub_nat_to_imported xR) Hs Hx) HloR.
    have HhiL := prop_to_sprop _ _
      (fixpoint_lt_correspondence xR (sub_nat_to_imported xR)
        hR (sub_nat_to_imported hR) Hx Hh) HhiR.
    have Hfx := Hf xR (sub_nat_to_imported xR) Hx.
    exact (sprop_to_prop _ _
      (fixpoint_ne_correspondence xR (sub_nat_to_imported xR)
        (fR xR) (fL (sub_nat_to_imported xR)) Hx Hfx)
      (HL fL (sub_nat_to_imported hR) HmonoL HposL
        (sub_nat_to_imported sR) (sub_nat_to_imported fuelR)
        HstepL HfuelL HnoneL (sub_nat_to_imported xR)
        (Lean.And_intro _ _ HloL HhiL))).
Qed.

Print Assumptions fixpoint_ffpf_none_statement_certificate.

Definition fixpoint_ffpf_least_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat) (h : Lean.Nat),
    fixpoint_target_monotone f ->
    fixpoint_target_lt Lean.Nat_zero
      (f (Lean.Nat_succ Lean.Nat_zero)) ->
    forall y s fuel : Lean.Nat,
      Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
        f s h fuel) (ImportedFixpoint.Option_some_inst1 Lean.Nat y) ->
      forall x : Lean.Nat,
        Lean.And (fixpoint_target_le s x) (fixpoint_target_lt x y) ->
        ImportedFixpoint.Ne Lean.Nat x (f x).

Definition fixpoint_ffpf_least_exact_type_guard :
    fixpoint_ffpf_least_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_ffpf_finds_least_fixpoint.

Lemma fixpoint_ffpf_least_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_ffpf_finds_least_fixpoint
    fixpoint_ffpf_least_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL HmonoL HposL yL sL fuelL HfoundL xL HrangeL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (sR := sub_nat_to_rocq sL).
    set (yR := sub_nat_to_rocq yL).
    set (xR := sub_nat_to_rocq xL).
    set (fuelR := sub_nat_to_rocq fuelL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hs := sub_nat_rel_surjective sL.
    have Hy := sub_nat_rel_surjective yL.
    have Hx := sub_nat_rel_surjective xL.
    have Hfuel := sub_nat_rel_surjective fuelL.
    have HmonoR := sprop_to_prop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoL.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposL.
    have HfoundR := sprop_to_prop _ _
      (fixpoint_from_some_eq_correspondence
        fR fL sR hR fuelR yR sL hL fuelL yL
        Hf Hs Hh Hfuel Hy) HfoundL.
    destruct HrangeL as [HleL HltL].
    have HleR := sprop_to_prop _ _
      (fixpoint_le_correspondence sR sL xR xL Hs Hx) HleL.
    have HltR := sprop_to_prop _ _
      (fixpoint_lt_correspondence xR xL yR yL Hx Hy) HltL.
    have HrangeR : is_true (leq sR xR && ltn xR yR).
    { apply/andP. split; assumption. }
    have Hfx := Hf xR xL Hx.
    exact (prop_to_sprop _ _
      (fixpoint_ne_correspondence xR xL (fR xR) (fL xL) Hx Hfx)
      (HR fR hR HmonoR HposR yR sR fuelR HfoundR xR HrangeR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR HmonoR HposR yR sR fuelR HfoundR xR HrangeR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hs := sub_nat_rel_canonical sR.
    have Hy := sub_nat_rel_canonical yR.
    have Hx := sub_nat_rel_canonical xR.
    have Hfuel := sub_nat_rel_canonical fuelR.
    have HmonoL := prop_to_sprop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoR.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_from_some_eq_correspondence
        fR fL sR hR fuelR yR
        (sub_nat_to_imported sR) (sub_nat_to_imported hR)
        (sub_nat_to_imported fuelR) (sub_nat_to_imported yR)
        Hf Hs Hh Hfuel Hy) HfoundR.
    move/andP: HrangeR => [HleR HltR].
    have HleL := prop_to_sprop _ _
      (fixpoint_le_correspondence sR (sub_nat_to_imported sR)
        xR (sub_nat_to_imported xR) Hs Hx) HleR.
    have HltL := prop_to_sprop _ _
      (fixpoint_lt_correspondence xR (sub_nat_to_imported xR)
        yR (sub_nat_to_imported yR) Hx Hy) HltR.
    have Hfx := Hf xR (sub_nat_to_imported xR) Hx.
    exact (sprop_to_prop _ _
      (fixpoint_ne_correspondence xR (sub_nat_to_imported xR)
        (fR xR) (fL (sub_nat_to_imported xR)) Hx Hfx)
      (HL fL (sub_nat_to_imported hR) HmonoL HposL
        (sub_nat_to_imported yR) (sub_nat_to_imported sR)
        (sub_nat_to_imported fuelR) HfoundL
        (sub_nat_to_imported xR) (Lean.And_intro _ _ HleL HltL))).
Qed.

Print Assumptions fixpoint_ffpf_least_statement_certificate.

Definition fixpoint_ffp_least_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat) (h : Lean.Nat),
    fixpoint_target_monotone f ->
    fixpoint_target_lt Lean.Nat_zero
      (f (Lean.Nat_succ Lean.Nat_zero)) ->
    forall x y : Lean.Nat,
      Lean.And (fixpoint_target_lt Lean.Nat_zero x)
        (fixpoint_target_lt x y) ->
      Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint f h)
        (ImportedFixpoint.Option_some_inst1 Lean.Nat y) ->
      ImportedFixpoint.Ne Lean.Nat x (f x).

Definition fixpoint_ffp_least_exact_type_guard :
    fixpoint_ffp_least_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_ffp_finds_least_fixpoint.

Lemma fixpoint_ffp_least_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_ffp_finds_least_fixpoint
    fixpoint_ffp_least_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL HmonoL HposL xL yL HrangeL HfoundL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (xR := sub_nat_to_rocq xL).
    set (yR := sub_nat_to_rocq yL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hx := sub_nat_rel_surjective xL.
    have Hy := sub_nat_rel_surjective yL.
    have HmonoR := sprop_to_prop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoL.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposL.
    destruct HrangeL as [HloL HhiL].
    have HloR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero xR xL
        (sub_nat_rel_canonical O) Hx) HloL.
    have HhiR := sprop_to_prop _ _
      (fixpoint_lt_correspondence xR xL yR yL Hx Hy) HhiL.
    have HrangeR : is_true (ltn O xR && ltn xR yR).
    { apply/andP. split; assumption. }
    have HfoundR := sprop_to_prop _ _
      (fixpoint_some_eq_correspondence
        fR fL hR yR hL yL Hf Hh Hy) HfoundL.
    have Hfx := Hf xR xL Hx.
    exact (prop_to_sprop _ _
      (fixpoint_ne_correspondence xR xL (fR xR) (fL xL) Hx Hfx)
      (HR fR hR HmonoR HposR xR yR HrangeR HfoundR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR HmonoR HposR xR yR HrangeR HfoundR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hx := sub_nat_rel_canonical xR.
    have Hy := sub_nat_rel_canonical yR.
    have HmonoL := prop_to_sprop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoR.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposR.
    move/andP: HrangeR => [HloR HhiR].
    have HloL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        xR (sub_nat_to_imported xR)
        (sub_nat_rel_canonical O) Hx) HloR.
    have HhiL := prop_to_sprop _ _
      (fixpoint_lt_correspondence xR (sub_nat_to_imported xR)
        yR (sub_nat_to_imported yR) Hx Hy) HhiR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_some_eq_correspondence
        fR fL hR yR (sub_nat_to_imported hR)
        (sub_nat_to_imported yR) Hf Hh Hy) HfoundR.
    have Hfx := Hf xR (sub_nat_to_imported xR) Hx.
    exact (sprop_to_prop _ _
      (fixpoint_ne_correspondence xR (sub_nat_to_imported xR)
        (fR xR) (fL (sub_nat_to_imported xR)) Hx Hfx)
      (HL fL (sub_nat_to_imported hR) HmonoL HposL
        (sub_nat_to_imported xR) (sub_nat_to_imported yR)
        (Lean.And_intro _ _ HloL HhiL) HfoundL)).
Qed.

Print Assumptions fixpoint_ffp_least_statement_certificate.

Definition fixpoint_ffpf_positive_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat) (h : Lean.Nat),
    fixpoint_target_monotone f ->
    fixpoint_target_lt Lean.Nat_zero
      (f (Lean.Nat_succ Lean.Nat_zero)) ->
    forall s fuel x : Lean.Nat,
      Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat x)
        (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint_from
          f s h fuel) ->
      fixpoint_target_lt Lean.Nat_zero s ->
      fixpoint_target_lt Lean.Nat_zero x.

Definition fixpoint_ffpf_positive_exact_type_guard :
    fixpoint_ffpf_positive_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_ffpf_finds_positive_fixpoint.

Lemma fixpoint_ffpf_positive_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_ffpf_finds_positive_fixpoint
    fixpoint_ffpf_positive_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL HmonoL HposL sL fuelL xL HfoundL HsposL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (sR := sub_nat_to_rocq sL).
    set (fuelR := sub_nat_to_rocq fuelL).
    set (xR := sub_nat_to_rocq xL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hs := sub_nat_rel_surjective sL.
    have Hfuel := sub_nat_rel_surjective fuelL.
    have Hx := sub_nat_rel_surjective xL.
    have HmonoR := sprop_to_prop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoL.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposL.
    have HfoundR := sprop_to_prop _ _
      (fixpoint_from_some_eq_reverse_correspondence
        fR fL sR hR fuelR xR sL hL fuelL xL
        Hf Hs Hh Hfuel Hx) HfoundL.
    have HsposR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero sR sL
        (sub_nat_rel_canonical O) Hs) HsposL.
    exact (prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero xR xL
        (sub_nat_rel_canonical O) Hx)
      (HR fR hR HmonoR HposR sR fuelR xR HfoundR HsposR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR HmonoR HposR sR fuelR xR HfoundR HsposR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hs := sub_nat_rel_canonical sR.
    have Hfuel := sub_nat_rel_canonical fuelR.
    have Hx := sub_nat_rel_canonical xR.
    have HmonoL := prop_to_sprop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoR.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_from_some_eq_reverse_correspondence
        fR fL sR hR fuelR xR
        (sub_nat_to_imported sR) (sub_nat_to_imported hR)
        (sub_nat_to_imported fuelR) (sub_nat_to_imported xR)
        Hf Hs Hh Hfuel Hx) HfoundR.
    have HsposL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        sR (sub_nat_to_imported sR)
        (sub_nat_rel_canonical O) Hs) HsposR.
    exact (sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        xR (sub_nat_to_imported xR)
        (sub_nat_rel_canonical O) Hx)
      (HL fL (sub_nat_to_imported hR) HmonoL HposL
        (sub_nat_to_imported sR) (sub_nat_to_imported fuelR)
        (sub_nat_to_imported xR) HfoundL HsposL)).
Qed.

Print Assumptions fixpoint_ffpf_positive_statement_certificate.

Definition fixpoint_ffp_positive_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat) (h : Lean.Nat),
    fixpoint_target_monotone f ->
    fixpoint_target_lt Lean.Nat_zero
      (f (Lean.Nat_succ Lean.Nat_zero)) ->
    forall x : Lean.Nat,
      Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat x)
        (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint f h) ->
      fixpoint_target_lt Lean.Nat_zero x.

Definition fixpoint_ffp_positive_exact_type_guard :
    fixpoint_ffp_positive_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_ffp_finds_positive_fixpoint.

Lemma fixpoint_ffp_positive_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_ffp_finds_positive_fixpoint
    fixpoint_ffp_positive_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL hL HmonoL HposL xL HfoundL.
    set (fR := fixpoint_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (xR := sub_nat_to_rocq xL).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hx := sub_nat_rel_surjective xL.
    have HmonoR := sprop_to_prop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoL.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposR := sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposL.
    have HfoundR := sprop_to_prop _ _
      (fixpoint_some_eq_reverse_correspondence
        fR fL hR xR hL xL Hf Hh Hx) HfoundL.
    exact (prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero xR xL
        (sub_nat_rel_canonical O) Hx)
      (HR fR hR HmonoR HposR xR HfoundR)).
  - intro HL. apply strictly_inhabits.
    intros fR hR HmonoR HposR xR HfoundR.
    set (fL := fixpoint_fun_to_imported fR).
    have Hf : SubNatFunRel fR fL := fixpoint_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hx := sub_nat_rel_canonical xR.
    have HmonoL := prop_to_sprop _ _
      (fixpoint_monotone_correspondence fR fL Hf) HmonoR.
    have Hf1 := Hf (S O) (Lean.Nat_succ Lean.Nat_zero)
      (sub_nat_rel_canonical (S O)).
    have HposL := prop_to_sprop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        (fR (S O)) (fL (Lean.Nat_succ Lean.Nat_zero))
        (sub_nat_rel_canonical O) Hf1) HposR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_some_eq_reverse_correspondence
        fR fL hR xR (sub_nat_to_imported hR)
        (sub_nat_to_imported xR) Hf Hh Hx) HfoundR.
    exact (sprop_to_prop _ _
      (fixpoint_lt_correspondence O Lean.Nat_zero
        xR (sub_nat_to_imported xR)
        (sub_nat_rel_canonical O) Hx)
      (HL fL (sub_nat_to_imported hR) HmonoL HposL
        (sub_nat_to_imported xR) HfoundL)).
Qed.

Print Assumptions fixpoint_ffp_positive_statement_certificate.
