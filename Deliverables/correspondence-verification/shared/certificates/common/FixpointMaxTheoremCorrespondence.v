From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFixpoint.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  FixpointBaseCorrespondence FixpointMonotoneCorrespondence
  FixpointMaxOperations.
Require Import GeneratedFixpointSourceAll.

(** The guards use the actual compiled Lean theorem constants only to check
    exact types.  None of the semantic proofs below use those constants. *)

Definition fixpoint_fmfs_finds_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat -> Lean.Nat)
         (sp : ImportedFixpoint.List_inst1 Lean.Nat)
         (h x : Lean.Nat),
    ImportedFixpoint.Ne (ImportedFixpoint.List_inst1 Lean.Nat) sp
      (ImportedFixpoint.List_nil_inst1 Lean.Nat) ->
    Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint_of_seq
      f sp h) (ImportedFixpoint.Option_some_inst1 Lean.Nat x) ->
    ImportedFixpoint.Exists Lean.Nat (fun a =>
      Lean.And
        (ImportedFixpoint.Membership_mem_inst3 Lean.Nat
          (ImportedFixpoint.List_inst1 Lean.Nat)
          (ImportedFixpoint.List_instMembership_inst1 Lean.Nat) sp a)
        (Lean.eq x (f a x))).

Definition fixpoint_fmfs_finds_exact_type_guard :
    fixpoint_fmfs_finds_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_fmfs_finds_fixpoint.

Lemma fixpoint_fmfs_finds_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_fmfs_finds_fixpoint
    fixpoint_fmfs_finds_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL spL hL xL HnonnullL HfoundL.
    set (fR := fixpoint_binary_fun_to_rocq fL).
    set (spR := fixpoint_nat_list_to_rocq spL).
    set (hR := sub_nat_to_rocq hL).
    set (xR := sub_nat_to_rocq xL).
    have Hf : FixpointBinaryFunRel fR fL :=
      fixpoint_binary_fun_to_rocq_rel fL.
    have Hsp : FixpointNatListRel spR spL :=
      fixpoint_nat_list_target_roundtrip spL.
    have Hh := sub_nat_rel_surjective hL.
    have Hx := sub_nat_rel_surjective xL.
    have HnonnullR := sprop_to_prop _ _
      (fixpoint_nonnil_correspondence spR spL Hsp) HnonnullL.
    have HfoundR := sprop_to_prop _ _
      (fixpoint_max_of_seq_some_eq_correspondence
        fR fL spR spL hR xR hL xL Hf Hsp Hh Hx) HfoundL.
    destruct (HR fR spR hR xR HnonnullR HfoundR)
      as [aR HmemberR HeqR].
    set (aL := sub_nat_to_imported aR).
    have Ha := sub_nat_rel_canonical aR.
    have HmemberL := prop_to_sprop _ _
      (fixpoint_membership_correspondence aR aL spR spL Ha Hsp)
      HmemberR.
    have Hfa := Hf aR aL Ha xR xL Hx.
    have HeqL := prop_to_sprop _ _
      (sub_nat_eq_correspondence xR xL
        (fR aR xR) (fL aL xL) Hx Hfa) HeqR.
    exact (ImportedFixpoint.Exists_intro Lean.Nat _ aL
      (Lean.And_intro _ _ HmemberL HeqL)).
  - intro HL. apply strictly_inhabits.
    intros fR spR hR xR HnonnullR HfoundR.
    set (fL := fixpoint_binary_fun_to_imported fR).
    set (spL := fixpoint_nat_list_to_imported spR).
    set (hL := sub_nat_to_imported hR).
    set (xL := sub_nat_to_imported xR).
    have Hf : FixpointBinaryFunRel fR fL :=
      fixpoint_binary_fun_to_imported_rel fR.
    have Hsp : FixpointNatListRel spR spL :=
      @Lean.eq_refl _ _.
    have Hh := sub_nat_rel_canonical hR.
    have Hx := sub_nat_rel_canonical xR.
    have HnonnullL := prop_to_sprop _ _
      (fixpoint_nonnil_correspondence spR spL Hsp) HnonnullR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_max_of_seq_some_eq_correspondence
        fR fL spR spL hR xR hL xL Hf Hsp Hh Hx) HfoundR.
    apply (interpret_strict _).
    destruct (HL fL spL hL xL HnonnullL HfoundL)
      as [aL [HmemberL HeqL]].
    set (aR := sub_nat_to_rocq aL).
    have Ha := sub_nat_rel_surjective aL.
    have HmemberR := sprop_to_prop _ _
      (fixpoint_membership_correspondence aR aL spR spL Ha Hsp)
      HmemberL.
    have Hfa := Hf aR aL Ha xR xL Hx.
    have HeqR := sprop_to_prop _ _
      (sub_nat_eq_correspondence xR xL
        (fR aR xR) (fL aL xL) Hx Hfa) HeqL.
    apply strictly_inhabits. exists aR; assumption.
Qed.

Print Assumptions fixpoint_fmfs_finds_statement_certificate.

Lemma fixpoint_maximum_witness_correspondence
    (fR : nat -> nat -> nat) (fL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (sR hR rR : nat) (sL hL rL : Lean.Nat) :
  FixpointBinaryFunRel fR fL ->
  SubNatRel sR sL -> SubNatRel hR hL -> SubNatRel rR rL ->
  PropSPropRel
    (exists2 v : nat,
      Logic.eq (Some v)
        (GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.find_fixpoint
          (fR sR) hR) & is_true (leq v rR))
    (ImportedFixpoint.Exists Lean.Nat (fun v =>
      Lean.And
        (Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat v)
          (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint
            (fL sL) hL))
        (ImportedFixpoint.LE_le_inst1 Lean.Nat
          ImportedFixpoint.instLENat v rL))).
Proof.
  intros Hf Hs Hh Hr.
  have Hfs := Hf sR sL Hs.
  apply prop_sprop_rel_intro.
  - intros [vR HfoundR HleR].
    set (vL := sub_nat_to_imported vR).
    have Hv := sub_nat_rel_canonical vR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_some_eq_reverse_correspondence
        (fR sR) (fL sL) hR vR hL vL Hfs Hh Hv) HfoundR.
    have HleL := prop_to_sprop _ _
      (fixpoint_le_correspondence vR vL rR rL Hv Hr) HleR.
    exact (ImportedFixpoint.Exists_intro Lean.Nat _ vL
      (Lean.And_intro _ _ HfoundL HleL)).
  - intro HL. destruct HL as [vL [HfoundL HleL]].
    set (vR := sub_nat_to_rocq vL).
    have Hv := sub_nat_rel_surjective vL.
    have HfoundR := sprop_to_prop _ _
      (fixpoint_some_eq_reverse_correspondence
        (fR sR) (fL sL) hR vR hL vL Hfs Hh Hv) HfoundL.
    have HleR := sprop_to_prop _ _
      (fixpoint_le_correspondence vR vL rR rL Hv Hr) HleL.
    apply strictly_inhabits. exists vR; assumption.
Qed.

Print Assumptions fixpoint_maximum_witness_correspondence.

Definition fixpoint_fmfs_maximum_target_type : SProp :=
  forall (f : Lean.Nat -> Lean.Nat -> Lean.Nat)
         (sp : ImportedFixpoint.List_inst1 Lean.Nat)
         (h s r : Lean.Nat),
    Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat r)
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint_of_seq
        f sp h) ->
    ImportedFixpoint.Membership_mem_inst3 Lean.Nat
      (ImportedFixpoint.List_inst1 Lean.Nat)
      (ImportedFixpoint.List_instMembership_inst1 Lean.Nat) sp s ->
    ImportedFixpoint.Exists Lean.Nat (fun v =>
      Lean.And
        (Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat v)
          (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint
            (f s) h))
        (ImportedFixpoint.LE_le_inst1 Lean.Nat
          ImportedFixpoint.instLENat v r)).

Definition fixpoint_fmfs_maximum_exact_type_guard :
    fixpoint_fmfs_maximum_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_fmfs_is_maximum.

Lemma fixpoint_fmfs_maximum_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_fmfs_is_maximum
    fixpoint_fmfs_maximum_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR fL spL hL sL rL HfoundL HmemberL.
    set (fR := fixpoint_binary_fun_to_rocq fL).
    set (spR := fixpoint_nat_list_to_rocq spL).
    set (hR := sub_nat_to_rocq hL).
    set (sR := sub_nat_to_rocq sL).
    set (rR := sub_nat_to_rocq rL).
    have Hf : FixpointBinaryFunRel fR fL :=
      fixpoint_binary_fun_to_rocq_rel fL.
    have Hsp : FixpointNatListRel spR spL :=
      fixpoint_nat_list_target_roundtrip spL.
    have Hh := sub_nat_rel_surjective hL.
    have Hs := sub_nat_rel_surjective sL.
    have Hr := sub_nat_rel_surjective rL.
    have HfoundR := sprop_to_prop _ _
      (fixpoint_max_of_seq_some_eq_reverse_correspondence
        fR fL spR spL hR rR hL rL Hf Hsp Hh Hr) HfoundL.
    have HmemberR := sprop_to_prop _ _
      (fixpoint_membership_correspondence sR sL spR spL Hs Hsp)
      HmemberL.
    exact (prop_to_sprop _ _
      (fixpoint_maximum_witness_correspondence
        fR fL sR hR rR sL hL rL Hf Hs Hh Hr)
      (HR fR spR hR sR rR HfoundR HmemberR)).
  - intro HL. apply strictly_inhabits.
    intros fR spR hR sR rR HfoundR HmemberR.
    set (fL := fixpoint_binary_fun_to_imported fR).
    set (spL := fixpoint_nat_list_to_imported spR).
    set (hL := sub_nat_to_imported hR).
    set (sL := sub_nat_to_imported sR).
    set (rL := sub_nat_to_imported rR).
    have Hf : FixpointBinaryFunRel fR fL :=
      fixpoint_binary_fun_to_imported_rel fR.
    have Hsp : FixpointNatListRel spR spL := @Lean.eq_refl _ _.
    have Hh := sub_nat_rel_canonical hR.
    have Hs := sub_nat_rel_canonical sR.
    have Hr := sub_nat_rel_canonical rR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_max_of_seq_some_eq_reverse_correspondence
        fR fL spR spL hR rR hL rL Hf Hsp Hh Hr) HfoundR.
    have HmemberL := prop_to_sprop _ _
      (fixpoint_membership_correspondence sR sL spR spL Hs Hsp)
      HmemberR.
    exact (sprop_to_prop _ _
      (fixpoint_maximum_witness_correspondence
        fR fL sR hR rR sL hL rL Hf Hs Hh Hr)
      (HL fL spL hL sL rL HfoundL HmemberL)).
Qed.

Print Assumptions fixpoint_fmfs_maximum_statement_certificate.

Lemma fixpoint_source_and_split (a b : bool) :
  is_true (a && b) -> is_true a /\ is_true b.
Proof. by move/andP. Qed.

Lemma fixpoint_source_and_join (a b : bool) :
  is_true a -> is_true b -> is_true (a && b).
Proof. intros Ha Hb. apply/andP. split; assumption. Qed.

Lemma fixpoint_search_space_correspondence
    (LR aR : nat) (LL aL : Lean.Nat)
    (pR : nat -> bool) (pL : Lean.Nat -> ImportedFixpoint.Bool) :
  SubNatRel LR LL -> SubNatRel aR aL ->
  FixpointNatPredRel pR pL ->
  PropSPropRel (is_true (ltn aR LR && pR aR))
    (Lean.And (ImportedFixpoint.LT_lt_inst1 Lean.Nat
      ImportedFixpoint.instLTNat aL LL)
      (Lean.eq (pL aL) ImportedFixpoint.Bool_true)).
Proof.
  intros HL Ha Hp. apply prop_sprop_rel_intro.
  - intro HR.
    destruct (fixpoint_source_and_split _ _ HR) as [HltR HpredR].
    have HltL := prop_to_sprop _ _
      (fixpoint_lt_correspondence aR aL LR LL Ha HL) HltR.
    have HpredL := prop_to_sprop _ _
      (fixpoint_bool_truth_correspondence
        (pR aR) (pL aL) (Hp aR aL Ha)) HpredR.
    exact (Lean.And_intro _ _ HltL HpredL).
  - intros [HltL HpredL].
    have HltR := sprop_to_prop _ _
      (fixpoint_lt_correspondence aR aL LR LL Ha HL) HltL.
    have HpredR := sprop_to_prop _ _
      (fixpoint_bool_truth_correspondence
        (pR aR) (pL aL) (Hp aR aL Ha)) HpredL.
    have Hboth : is_true (ltn aR LR && pR aR) :=
      fixpoint_source_and_join _ _ HltR HpredR.
    exact (strictly_inhabits Hboth).
Qed.

Print Assumptions fixpoint_search_space_correspondence.

Definition fixpoint_fmf_finds_target_type : SProp :=
  forall (L : Lean.Nat) (P : Lean.Nat -> ImportedFixpoint.Bool)
         (f : Lean.Nat -> Lean.Nat -> Lean.Nat) (h x : Lean.Nat),
    Lean.eq (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint
      L P f h) (ImportedFixpoint.Option_some_inst1 Lean.Nat x) ->
    ImportedFixpoint.Exists Lean.Nat (fun a =>
      Lean.And
        (Lean.And
          (ImportedFixpoint.LT_lt_inst1 Lean.Nat
            ImportedFixpoint.instLTNat a L)
          (Lean.eq (P a) ImportedFixpoint.Bool_true))
        (Lean.eq x (f a x))).

Definition fixpoint_fmf_finds_exact_type_guard :
    fixpoint_fmf_finds_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_fmf_finds_fixpoint.

Lemma fixpoint_fmf_finds_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_fmf_finds_fixpoint
    fixpoint_fmf_finds_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR LL pL fL hL xL HfoundL.
    set (LR := sub_nat_to_rocq LL).
    set (pR := fixpoint_pred_to_rocq pL).
    set (fR := fixpoint_binary_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (xR := sub_nat_to_rocq xL).
    have HL := sub_nat_rel_surjective LL.
    have Hp : FixpointNatPredRel pR pL :=
      fixpoint_pred_to_rocq_rel pL.
    have Hf : FixpointBinaryFunRel fR fL :=
      fixpoint_binary_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hx := sub_nat_rel_surjective xL.
    have HfoundR := sprop_to_prop _ _
      (fixpoint_max_wrapper_some_eq_correspondence
        LR LL pR pL fR fL hR xR hL xL HL Hp Hf Hh Hx)
      HfoundL.
    destruct (HR LR pR fR hR xR HfoundR)
      as [aR HspaceR HeqR].
    set (aL := sub_nat_to_imported aR).
    have Ha := sub_nat_rel_canonical aR.
    have HspaceL := prop_to_sprop _ _
      (fixpoint_search_space_correspondence
        LR aR LL aL pR pL HL Ha Hp) HspaceR.
    have Hfa := Hf aR aL Ha xR xL Hx.
    have HeqL := prop_to_sprop _ _
      (sub_nat_eq_correspondence xR xL
        (fR aR xR) (fL aL xL) Hx Hfa) HeqR.
    exact (ImportedFixpoint.Exists_intro Lean.Nat _ aL
      (Lean.And_intro _ _ HspaceL HeqL)).
  - intro HL. apply strictly_inhabits.
    intros LR pR fR hR xR HfoundR.
    set (LL := sub_nat_to_imported LR).
    set (pL := fixpoint_pred_to_imported pR).
    set (fL := fixpoint_binary_fun_to_imported fR).
    set (hL := sub_nat_to_imported hR).
    set (xL := sub_nat_to_imported xR).
    have HLL := sub_nat_rel_canonical LR.
    have Hp : FixpointNatPredRel pR pL :=
      fixpoint_pred_to_imported_rel pR.
    have Hf : FixpointBinaryFunRel fR fL :=
      fixpoint_binary_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hx := sub_nat_rel_canonical xR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_max_wrapper_some_eq_correspondence
        LR LL pR pL fR fL hR xR hL xL HLL Hp Hf Hh Hx)
      HfoundR.
    apply (interpret_strict _).
    destruct (HL LL pL fL hL xL HfoundL)
      as [aL [HspaceL HeqL]].
    set (aR := sub_nat_to_rocq aL).
    have Ha := sub_nat_rel_surjective aL.
    have HspaceR := sprop_to_prop _ _
      (fixpoint_search_space_correspondence
        LR aR LL aL pR pL HLL Ha Hp) HspaceL.
    have Hfa := Hf aR aL Ha xR xL Hx.
    have HeqR := sprop_to_prop _ _
      (sub_nat_eq_correspondence xR xL
        (fR aR xR) (fL aL xL) Hx Hfa) HeqL.
    apply strictly_inhabits. exists aR; assumption.
Qed.

Print Assumptions fixpoint_fmf_finds_statement_certificate.

Definition fixpoint_fmf_maximum_target_type : SProp :=
  forall (L : Lean.Nat) (P : Lean.Nat -> ImportedFixpoint.Bool)
         (f : Lean.Nat -> Lean.Nat -> Lean.Nat)
         (h s r : Lean.Nat),
    Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat r)
      (ImportedFixpoint.Prosa_Util_Fixpoint_find_max_fixpoint
        L P f h) ->
    Lean.And
      (ImportedFixpoint.LT_lt_inst1 Lean.Nat
        ImportedFixpoint.instLTNat s L)
      (Lean.eq (P s) ImportedFixpoint.Bool_true) ->
    ImportedFixpoint.Exists Lean.Nat (fun v =>
      Lean.And
        (Lean.eq (ImportedFixpoint.Option_some_inst1 Lean.Nat v)
          (ImportedFixpoint.Prosa_Util_Fixpoint_find_fixpoint
            (f s) h))
        (ImportedFixpoint.LE_le_inst1 Lean.Nat
          ImportedFixpoint.instLENat v r)).

Definition fixpoint_fmf_maximum_exact_type_guard :
    fixpoint_fmf_maximum_target_type :=
  ImportedFixpoint.Prosa_Util_Fixpoint_fmf_is_maximum.

Lemma fixpoint_fmf_maximum_statement_certificate :
  PropSPropRel
    GeneratedFixpointSourceAll.GeneratedFixpointSourceAll.statement_fmf_is_maximum
    fixpoint_fmf_maximum_target_type.
Proof.
  apply prop_sprop_rel_intro.
  - intros HR LL pL fL hL sL rL HfoundL HspaceL.
    set (LR := sub_nat_to_rocq LL).
    set (pR := fixpoint_pred_to_rocq pL).
    set (fR := fixpoint_binary_fun_to_rocq fL).
    set (hR := sub_nat_to_rocq hL).
    set (sR := sub_nat_to_rocq sL).
    set (rR := sub_nat_to_rocq rL).
    have HLL := sub_nat_rel_surjective LL.
    have Hp : FixpointNatPredRel pR pL :=
      fixpoint_pred_to_rocq_rel pL.
    have Hf : FixpointBinaryFunRel fR fL :=
      fixpoint_binary_fun_to_rocq_rel fL.
    have Hh := sub_nat_rel_surjective hL.
    have Hs := sub_nat_rel_surjective sL.
    have Hr := sub_nat_rel_surjective rL.
    have HfoundR := sprop_to_prop _ _
      (fixpoint_max_wrapper_some_eq_reverse_correspondence
        LR LL pR pL fR fL hR rR hL rL HLL Hp Hf Hh Hr)
      HfoundL.
    have HspaceR := sprop_to_prop _ _
      (fixpoint_search_space_correspondence
        LR sR LL sL pR pL HLL Hs Hp) HspaceL.
    exact (prop_to_sprop _ _
      (fixpoint_maximum_witness_correspondence
        fR fL sR hR rR sL hL rL Hf Hs Hh Hr)
      (HR LR pR fR hR sR rR HfoundR HspaceR)).
  - intro HL. apply strictly_inhabits.
    intros LR pR fR hR sR rR HfoundR HspaceR.
    set (LL := sub_nat_to_imported LR).
    set (pL := fixpoint_pred_to_imported pR).
    set (fL := fixpoint_binary_fun_to_imported fR).
    set (hL := sub_nat_to_imported hR).
    set (sL := sub_nat_to_imported sR).
    set (rL := sub_nat_to_imported rR).
    have HLL := sub_nat_rel_canonical LR.
    have Hp : FixpointNatPredRel pR pL :=
      fixpoint_pred_to_imported_rel pR.
    have Hf : FixpointBinaryFunRel fR fL :=
      fixpoint_binary_fun_to_imported_rel fR.
    have Hh := sub_nat_rel_canonical hR.
    have Hs := sub_nat_rel_canonical sR.
    have Hr := sub_nat_rel_canonical rR.
    have HfoundL := prop_to_sprop _ _
      (fixpoint_max_wrapper_some_eq_reverse_correspondence
        LR LL pR pL fR fL hR rR hL rL HLL Hp Hf Hh Hr)
      HfoundR.
    have HspaceL := prop_to_sprop _ _
      (fixpoint_search_space_correspondence
        LR sR LL sL pR pL HLL Hs Hp) HspaceR.
    exact (sprop_to_prop _ _
      (fixpoint_maximum_witness_correspondence
        fR fL sR hR rR sL hL rL Hf Hs Hh Hr)
      (HL LL pL fL hL sL rL HfoundL HspaceL)).
Qed.

Print Assumptions fixpoint_fmf_maximum_statement_certificate.
