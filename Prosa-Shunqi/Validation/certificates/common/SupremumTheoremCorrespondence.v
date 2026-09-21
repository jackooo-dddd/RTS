From mathcomp Require Import ssreflect ssrbool eqtype seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSupremum.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SupremumCertificate.

Inductive SupTheoremTrue : SProp := sup_theorem_I.
Inductive SupTheoremFalse : SProp := .

Definition sup_theorem_false_elim (P : SProp)
    (H : SupTheoremFalse) : P := match H return P with end.

Definition sup_relation_false_elim (P : SProp)
    (H : SupValidationFalse) : P := match H return P with end.

Definition SupBoolTruth (b : bool) : SProp :=
  match b with true => SupTheoremTrue | false => SupTheoremFalse end.

Definition sup_bool_prop_to_truth (b : bool) :
    is_true b -> SupBoolTruth b :=
  match b return is_true b -> SupBoolTruth b with
  | true => fun _ => sup_theorem_I
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => SupTheoremFalse | false => SupTheoremTrue end
      with Logic.eq_refl => sup_theorem_I end
  end.

Definition sup_truth_to_strict_bool_prop (b : bool) :
    SupBoolTruth b -> StrictlyInhabited (is_true b) :=
  match b return SupBoolTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => fun H => sup_theorem_false_elim _ H
  end.

Definition sup_imported_false_ne_true
    (H : Lean.eq ImportedSupremum.Bool_false ImportedSupremum.Bool_true) :
    SupTheoremFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedSupremum.Bool_false => SupTheoremTrue
    | ImportedSupremum.Bool_true => SupTheoremFalse
    end
  with Lean.eq_refl => sup_theorem_I end.

Lemma sup_bool_true_correspondence (bR : bool)
    (bL : ImportedSupremum.Bool) :
  SupBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedSupremum.Bool_true).
Proof.
  intro Hrel. apply prop_sprop_rel_intro.
  - destruct bR, bL; cbn in Hrel |- *.
    + exact (sup_relation_false_elim _ Hrel).
    + intros _. exact (@Lean.eq_refl ImportedSupremum.Bool
        ImportedSupremum.Bool_true).
    + intro H. exact (sup_theorem_false_elim _
        (sup_bool_prop_to_truth false H)).
    + exact (sup_relation_false_elim _ Hrel).
  - destruct bR, bL; cbn in Hrel |- *; intro Heq.
    + exact (sup_relation_false_elim _ Hrel).
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + exact (sup_theorem_false_elim _ (sup_imported_false_ne_true Heq)).
    + exact (sup_relation_false_elim _ Hrel).
Qed.

Lemma sup_bool_or_correspondence aR aL bR bL :
  SupBoolRel aR aL -> SupBoolRel bR bL ->
  SupBoolRel (aR || bR) (ImportedSupremum.Bool_or aL bL).
Proof.
  intros Ha Hb.
  destruct aR; destruct aL; destruct bR; destruct bL;
    cbn in Ha, Hb |- *; try exact Ha; try exact Hb;
    exact sup_validation_I.
Qed.

Definition coq_false_to_supremum_false
    (H : Logic.False) : ImportedSupremum.False :=
  match H return ImportedSupremum.False with end.

Definition supremum_false_elim (P : SProp)
    (H : ImportedSupremum.False) : P := match H return P with end.

Definition sup_eqtype_decidable_eq (T : eqType) :
    ImportedSupremum.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedSupremum.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedSupremum.Decidable_isFalse (Lean.eq x y)
        (fun HL => coq_false_to_supremum_false
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint sup_seq_to_imported {T : Type} (xs : seq T) :
    ImportedSupremum.List T :=
  match xs with
  | [::] => ImportedSupremum.List_nil T
  | x :: xs' => ImportedSupremum.List_cons T x (sup_seq_to_imported xs')
  end.

Fixpoint sup_imported_to_seq {T : Type} (xs : ImportedSupremum.List T) :
    seq T :=
  match xs with
  | ImportedSupremum.List_nil => [::]
  | ImportedSupremum.List_cons x xs' => x :: sup_imported_to_seq xs'
  end.

Lemma sup_seq_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (sup_imported_to_seq (sup_seq_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Fixpoint sup_list_rel_canonical {T : Type} (xs : seq T) :
    SupListRel T xs (sup_seq_to_imported xs) :=
  match xs with
  | [::] => sup_list_nil T
  | x :: xs' => sup_list_cons T x xs' (sup_seq_to_imported xs')
      (sup_list_rel_canonical xs')
  end.

Fixpoint sup_list_rel_surjective {T : Type}
    (xs : ImportedSupremum.List T) :
    SupListRel T (sup_imported_to_seq xs) xs :=
  match xs with
  | ImportedSupremum.List_nil => sup_list_nil T
  | ImportedSupremum.List_cons x xs' =>
      sup_list_cons T x (sup_imported_to_seq xs') xs'
        (sup_list_rel_surjective xs')
  end.

Fixpoint sup_list_rel_as_eq {T : Type} (xsR : seq T)
    (xsL : ImportedSupremum.List T) (H : SupListRel T xsR xsL) {struct H} :
    Lean.eq (sup_seq_to_imported xsR) xsL :=
    match H in SupListRel _ rs ls return Lean.eq (sup_seq_to_imported rs) ls with
    | sup_list_nil => @Lean.eq_refl (ImportedSupremum.List T)
        (ImportedSupremum.List_nil T)
    | sup_list_cons x rs ls Htail =>
        match sup_list_rel_as_eq rs ls Htail in Lean.eq _ zs return
          Lean.eq (ImportedSupremum.List_cons T x (sup_seq_to_imported rs))
            (ImportedSupremum.List_cons T x zs)
        with Lean.eq_refl => @Lean.eq_refl (ImportedSupremum.List T)
          (ImportedSupremum.List_cons T x (sup_seq_to_imported rs)) end
    end.

Definition sup_option_to_imported {T : Type} (o : option T) :
    ImportedSupremum.Option T :=
  match o with
  | None => ImportedSupremum.Option_none T
  | Some x => ImportedSupremum.Option_some T x
  end.

Definition sup_imported_to_option {T : Type} (o : ImportedSupremum.Option T) :
    option T :=
  match o with
  | ImportedSupremum.Option_none => None
  | ImportedSupremum.Option_some x => Some x
  end.

Lemma sup_option_roundtrip {T : Type} (o : option T) :
  Logic.eq (sup_imported_to_option (sup_option_to_imported o)) o.
Proof. destruct o; reflexivity. Qed.

Definition sup_option_rel_as_eq {T : Type} (oR : option T)
    (oL : ImportedSupremum.Option T) :
    SupOptionRel T oR oL -> Lean.eq (sup_option_to_imported oR) oL :=
  fun H =>
    match H in SupOptionRel _ rs ls return Lean.eq (sup_option_to_imported rs) ls with
    | sup_option_none => @Lean.eq_refl (ImportedSupremum.Option T)
        (ImportedSupremum.Option_none T)
    | sup_option_some x => @Lean.eq_refl (ImportedSupremum.Option T)
        (ImportedSupremum.Option_some T x)
    end.

Definition sup_imported_eq_sym {A : Type} (x y : A) :
    Lean.eq x y -> Lean.eq y x :=
  fun H => match H in Lean.eq _ z return Lean.eq z x with
           | Lean.eq_refl => @Lean.eq_refl A x end.

Definition sup_imported_eq_trans {A : Type} (x y z : A) :
    Lean.eq x y -> Lean.eq y z -> Lean.eq x z :=
  fun Hxy Hyz =>
    match Hxy in Lean.eq _ y' return Lean.eq y' z -> Lean.eq x z with
    | Lean.eq_refl => fun H => H
    end Hyz.

Lemma sup_option_eq_correspondence (T : Type)
    (aR bR : option T) (aL bL : ImportedSupremum.Option T) :
  SupOptionRel T aR aL -> SupOptionRel T bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sup_imported_eq_trans _ _ _
      (sup_imported_eq_sym _ _ (sup_option_rel_as_eq _ _ Ha))
      (sup_option_rel_as_eq _ _ Hb)).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (sup_option_to_imported aR)
        (sup_option_to_imported bR) :=
      sup_imported_eq_trans _ _ _ (sup_option_rel_as_eq _ _ Ha)
        (sup_imported_eq_trans _ _ _ Heq
          (sup_imported_eq_sym _ _ (sup_option_rel_as_eq _ _ Hb))).
    have Hdecoded := f_equal sup_imported_to_option
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (sup_option_roundtrip aR) in Hdecoded.
    rewrite (sup_option_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma sup_list_eq_correspondence (T : Type)
    (aR bR : seq T) (aL bL : ImportedSupremum.List T) :
  SupListRel T aR aL -> SupListRel T bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sup_imported_eq_trans _ _ _
      (sup_imported_eq_sym _ _ (sup_list_rel_as_eq _ _ Ha))
      (sup_list_rel_as_eq _ _ Hb)).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (sup_seq_to_imported aR)
        (sup_seq_to_imported bR) :=
      sup_imported_eq_trans _ _ _ (sup_list_rel_as_eq _ _ Ha)
        (sup_imported_eq_trans _ _ _ Heq
          (sup_imported_eq_sym _ _ (sup_list_rel_as_eq _ _ Hb))).
    have Hdecoded := f_equal sup_imported_to_seq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (sup_seq_roundtrip aR) in Hdecoded.
    rewrite (sup_seq_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Definition sup_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedSupremum.List T) :
    Lean.eq xs ys -> ImportedSupremum.List_Mem T x xs ->
    ImportedSupremum.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedSupremum.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition sup_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedSupremum.List T) :
    Logic.eq x y ->
    ImportedSupremum.List_Mem T x (ImportedSupremum.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedSupremum.List_Mem T x (ImportedSupremum.List_cons T z xs) with
    | Logic.eq_refl => ImportedSupremum.List_Mem_head T x xs
    end.

Fixpoint sup_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SupBoolTruth (x \in xs) ->
    ImportedSupremum.List_Mem T x (sup_seq_to_imported xs) :=
  match xs as xs0 return SupBoolTruth (x \in xs0) ->
      ImportedSupremum.List_Mem T x (sup_seq_to_imported xs0)
  with
  | [::] => sup_theorem_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SupBoolTruth (b || (x \in ys)) ->
        ImportedSupremum.List_Mem T x
          (ImportedSupremum.List_cons T y (sup_seq_to_imported ys))
      with
      | ReflectT Hxy => fun _ => sup_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedSupremum.List_Mem_tail T x y _
          (sup_seq_mem_forward x ys H)
      end
  end.

Definition sup_mem_tail_truth (a b : bool) :
    SupBoolTruth b -> SupBoolTruth (a || b) :=
  match a, b return SupBoolTruth b -> SupBoolTruth (a || b) with
  | true, true => fun _ => sup_theorem_I
  | true, false => fun _ => sup_theorem_I
  | false, true => fun _ => sup_theorem_I
  | false, false => fun H => H
  end.

Definition sup_mem_head_truth (a b : bool) :
    SupBoolTruth a -> SupBoolTruth (a || b) :=
  match a, b return SupBoolTruth a -> SupBoolTruth (a || b) with
  | true, true => fun _ => sup_theorem_I
  | true, false => fun _ => sup_theorem_I
  | false, true => fun _ => sup_theorem_I
  | false, false => fun H => H
  end.

Definition sup_eq_refl_truth (T : eqType) (x : T) :
    SupBoolTruth (x == x).
Proof. rewrite eqxx. exact sup_theorem_I. Defined.

Fixpoint sup_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedSupremum.List T)
    (H : ImportedSupremum.List_Mem T x xs) :
    SupBoolTruth (x \in sup_imported_to_seq xs) :=
  match H with
  | ImportedSupremum.List_Mem_head ys =>
      sup_mem_head_truth _ _ (sup_eq_refl_truth T x)
  | ImportedSupremum.List_Mem_tail y ys Htail =>
      sup_mem_tail_truth _ _ (sup_imported_mem_decoded x ys Htail)
  end.

Definition sup_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) :
    Logic.eq xs ys -> SupBoolTruth (x \in xs) -> SupBoolTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return SupBoolTruth (x \in zs) with
    | Logic.eq_refl => Htruth
    end.

Definition sup_imported_mem_backward {T : eqType} (x : T) (xs : seq T)
    (H : ImportedSupremum.List_Mem T x (sup_seq_to_imported xs)) :
    SupBoolTruth (x \in xs) :=
  sup_mem_truth_transport x _ _ (sup_seq_roundtrip xs)
    (sup_imported_mem_decoded x (sup_seq_to_imported xs) H).

Definition sup_imported_mem (T : Type) (x : T)
    (xs : ImportedSupremum.List T) : SProp :=
  ImportedSupremum.Membership_mem T (ImportedSupremum.List T)
    (ImportedSupremum.List_instMembership T) xs x.

Lemma sup_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedSupremum.List T) :
  SupListRel T xsR xsL ->
  PropSPropRel (x \in xsR) (sup_imported_mem T x xsL).
Proof.
  intro Hlist. apply prop_sprop_rel_intro.
  - intro Hmem. unfold sup_imported_mem.
    apply (sup_list_mem_transport x _ _ (sup_list_rel_as_eq _ _ Hlist)).
    apply sup_seq_mem_forward. exact (sup_bool_prop_to_truth _ Hmem).
  - intro Hmem. apply sup_truth_to_strict_bool_prop.
    apply sup_imported_mem_backward.
    unfold sup_imported_mem in Hmem.
    exact (sup_list_mem_transport x _ _
      (sup_imported_eq_sym _ _ (sup_list_rel_as_eq _ _ Hlist)) Hmem).
Qed.

Lemma sup_option_ne_correspondence (T : eqType)
    (aR bR : option T) (aL bL : ImportedSupremum.Option T) :
  SupOptionRel T aR aL -> SupOptionRel T bR bL ->
  PropSPropRel (is_true (aR != bR))
    (ImportedSupremum.Ne (ImportedSupremum.Option T) aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intros Hneq HeqL.
    have HeqR := sprop_to_prop _ _
      (sup_option_eq_correspondence T aR bR aL bL Ha Hb) HeqL.
    subst bR. rewrite eqxx in Hneq. discriminate Hneq.
  - intro HneqL.
    destruct (@eqP _ aR bR) as [HeqR | HneqR].
    + exact (supremum_false_elim _
        (HneqL (prop_to_sprop _ _
          (sup_option_eq_correspondence T aR bR aL bL Ha Hb) HeqR))).
    + apply strictly_inhabits. exact (Logic.eq_refl true).
Qed.

Print Assumptions sup_bool_true_correspondence.
Print Assumptions sup_bool_or_correspondence.
Print Assumptions sup_membership_correspondence.
Print Assumptions sup_option_eq_correspondence.
Print Assumptions sup_list_eq_correspondence.
Print Assumptions sup_option_ne_correspondence.
