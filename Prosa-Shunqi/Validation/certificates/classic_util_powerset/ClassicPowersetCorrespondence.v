From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype tuple.
From prosa Require Import classic.util.powerset.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicPowerset.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicPowersetBase ClassicPowersetList.

Module I := ImportedClassicPowerset.
Local Open Scope nat_scope.

(** Certificates for [classic/util/powerset.v] (ProsaBuddy classic, commit f692cb7).

    [powerset l] maps [mask m l] over [enum {: (size l).-tuple bool}].  MathComp
    seals that enumeration ([Module FinTuple : FinTupleSig], [enum] opaque in
    the signature), so its order is not observable in Rocq; only [enumP] (each
    tuple exactly once) is.  The Lean translation enumerates the Boolean lists
    of length [n] by [boolTupleEnum n].  The definition certificate is
    therefore [perm_eq]: the source list and the converted Lean list have the
    same elements with the same multiplicities.  It is proved from [enumP]
    (through [mem_enum]/[enum_uniq]) and the structure of [boolTupleEnum]
    (computed by conversion, mirrored by [bte]); [mask] is related
    structurally.  [mem_powerset] only observes membership.

    Inputs: elements of an [eqType] identified, its Lean [DecidableEq] the
    eqType's decision procedure; sequences elementwise (two-way totals). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Boolean lists (Set-level Lean lists) *)

Fixpoint cpb (m : seq bool) : I.List_inst1 I.Bool :=
  match m with [::] => I.List_nil_inst1 _ | b :: m' => I.List_cons_inst1 _ (ct_b2l b) (cpb m') end.
Fixpoint cpbb (s : seq (seq bool)) : I.List_inst1 (I.List_inst1 I.Bool) :=
  match s with [::] => I.List_nil_inst1 _ | m :: s' => I.List_cons_inst1 _ (cpb m) (cpbb s') end.

Lemma cp_append (s1 s2 : seq (seq bool)) :
  Logic.eq (I.List_append_inst1 _ (cpbb s1) (cpbb s2)) (cpbb (s1 ++ s2)).
Proof.
  elim: s1 => [|m s1 IH] //=.
  change (Logic.eq (I.List_cons_inst1 _ (cpb m) (I.List_append_inst1 _ (cpbb s1) (cpbb s2))) (cpbb (m :: s1 ++ s2))).
  by rewrite IH.
Qed.

Lemma cp_mapcons (b : bool) (s : seq (seq bool)) :
  Logic.eq (I.List_map_inst3 (I.List_inst1 I.Bool) (I.List_inst1 I.Bool) (fun t => I.List_cons_inst1 I.Bool (ct_b2l b) t) (cpbb s))
           (cpbb (map (cons b) s)).
Proof.
  elim: s => [|m s IH] //=.
  change (Logic.eq (I.List_cons_inst1 _ (I.List_cons_inst1 I.Bool (ct_b2l b) (cpb m))
     (I.List_map_inst3 (I.List_inst1 I.Bool) (I.List_inst1 I.Bool) (fun t => I.List_cons_inst1 I.Bool (ct_b2l b) t) (cpbb s)))
    (cpbb ((b :: m) :: map (cons b) s))).
  by rewrite IH.
Qed.

(** The Rocq mirror of [boolTupleEnum]. *)
Fixpoint bte (n : nat) : seq (seq bool) :=
  if n is n'.+1 then map (cons true) (bte n') ++ map (cons false) (bte n') else [:: [::]].

Lemma cp_bte (n : nat) : Logic.eq (I.Prosa_Classic_Util_Powerset_boolTupleEnum (sub_nat_to_imported n)) (cpbb (bte n)).
Proof.
  elim: n => [|n IH]; first reflexivity.
  change (Logic.eq
    (I.List_flatten_inst1 (I.List_inst1 I.Bool)
      (I.List_map_inst3 I.Bool (I.List_inst1 (I.List_inst1 I.Bool))
        (fun x => I.List_map_inst3 (I.List_inst1 I.Bool) (I.List_inst1 I.Bool) (fun t => I.List_cons_inst1 I.Bool x t)
                    (I.Prosa_Classic_Util_Powerset_boolTupleEnum (sub_nat_to_imported n)))
        (I.List_cons_inst1 I.Bool I.Bool_true (I.List_cons_inst1 I.Bool I.Bool_false (I.List_nil_inst1 I.Bool)))))
    (cpbb (bte n.+1))).
  rewrite IH.
  change (Logic.eq (I.List_append_inst1 _
      (I.List_map_inst3 (I.List_inst1 I.Bool) (I.List_inst1 I.Bool) (fun t => I.List_cons_inst1 I.Bool (ct_b2l true) t) (cpbb (bte n)))
      (I.List_append_inst1 _
        (I.List_map_inst3 (I.List_inst1 I.Bool) (I.List_inst1 I.Bool) (fun t => I.List_cons_inst1 I.Bool (ct_b2l false) t) (cpbb (bte n)))
        (I.List_nil_inst1 _)))
    (cpbb (bte n.+1))).
  rewrite !cp_mapcons.
  change (I.List_nil_inst1 (I.List_inst1 I.Bool)) with (cpbb [::]).
  by rewrite !cp_append cats0.
Qed.

(** [mask]. *)
Lemma cp_mask (T : Type) : forall (m : seq bool) (l : seq T),
  Logic.eq (I.Prosa_Classic_Util_Powerset_mask T (cpb m) (cl_map cid l)) (cl_map cid (mask m l)).
Proof.
  elim => [|b m IH] [|x l] //=.
  have -> : Logic.eq (I.Prosa_Classic_Util_Powerset_mask T (I.List_cons_inst1 I.Bool (ct_b2l b) (cpb m)) (I.List_cons T x (cl_map cid l)))
      (match ct_b2l b with
       | I.Bool_true => I.List_cons T x (I.Prosa_Classic_Util_Powerset_mask T (cpb m) (cl_map cid l))
       | I.Bool_false => I.Prosa_Classic_Util_Powerset_mask T (cpb m) (cl_map cid l) end).
  { cbn. destruct b; reflexivity. }
  rewrite IH. by case: b.
Qed.

Lemma cp_map_inst1 (T : Type) (f : I.List_inst1 I.Bool -> I.List T) : forall s : seq (seq bool),
  Logic.eq (I.List_map_inst1 (I.List_inst1 I.Bool) (I.List T) f (cpbb s)) (cl_map (fun m => f (cpb m)) s).
Proof.
  elim => [|m s IH] //=.
  change (Logic.eq (I.List_cons (I.List T) (f (cpb m)) (I.List_map_inst1 (I.List_inst1 I.Bool) (I.List T) f (cpbb s)))
                   (cl_map (fun m0 => f (cpb m0)) (m :: s))).
  by rewrite IH.
Qed.

Lemma cp_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cp_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

(* ------------------------------------------------------------------ *)
(** * Source side: the sealed enumeration against [bte] *)

Lemma cp_bte_mem n (x : seq bool) : Logic.eq (x \in bte n) (size x == n).
Proof.
  elim: n x => [|n IH] x; first by case: x.
  rewrite /= mem_cat. case: x => [|b x].
  - apply/negbTE. rewrite negb_or. apply/andP; split; apply/mapP => [[y _ E]]; by [].
  - have Hinj : injective (cons b) := fun s t => @congr1 _ _ behead _ _.
    case: b Hinj => Hinj.
    + rewrite (mem_map Hinj) IH.
      have -> : (true :: x \in map (cons false) (bte n)) = false.
      { apply/negbTE/mapP => [[y _ E]]. by case: E. }
      by rewrite orbF eqSS.
    + rewrite (mem_map Hinj) IH.
      have -> : (false :: x \in map (cons true) (bte n)) = false.
      { apply/negbTE/mapP => [[y _ E]]. by case: E. }
      by rewrite eqSS.
Qed.

Lemma cp_cons_inj (b : bool) : injective (cons b).
Proof. by move=> s t []. Qed.

Lemma cp_bte_uniq n : uniq (bte n).
Proof.
  elim: n => [|n IH] //=. rewrite cat_uniq (map_inj_uniq (cp_cons_inj true)) (map_inj_uniq (cp_cons_inj false)) IH /= andbT.
  apply/hasPn => y /mapP [z _ ->]. apply/mapP => [[w _ E]]. by case: E.
Qed.

Lemma cp_enum_mem n (x : seq bool) : Logic.eq (x \in map (@tval n bool) (enum {: n.-tuple bool})) (size x == n).
Proof.
  apply/mapP/idP.
  - move=> [t _ ->]. by rewrite size_tuple.
  - move=> H. exists (Tuple H); last by []. by rewrite mem_enum.
Qed.

Lemma cp_enum_perm n : perm_eq (map (@tval n bool) (enum {: n.-tuple bool})) (bte n).
Proof.
  apply: uniq_perm.
  - rewrite (map_inj_uniq val_inj). exact: enum_uniq.
  - exact: cp_bte_uniq.
  - move=> x. by rewrite cp_enum_mem cp_bte_mem.
Qed.

(* ------------------------------------------------------------------ *)
(** * Definition *)

Theorem powerset_correspondence (T : eqType) (l : seq T) :
  perm_eq (powerset l) (cl_unmap (cl_unmap cid) (I.Prosa_Classic_Util_Powerset_powerset T (ct_decidable_eq T) (cl_map cid l))).
Proof.
  have Hsize := imported_eq_to_coq_eq _ _ (cl_size cid l).
  have -> : Logic.eq (I.Prosa_Classic_Util_Powerset_powerset T (ct_decidable_eq T) (cl_map cid l))
      (cl_map (cl_map cid) (map (mask^~ l) (bte (size l)))).
  { change (Logic.eq (I.List_map_inst1 (I.List_inst1 I.Bool) (I.List T) (fun m => I.Prosa_Classic_Util_Powerset_mask T m (cl_map cid l))
                         (I.Prosa_Classic_Util_Powerset_boolTupleEnum (I.List_length T (cl_map cid l))))
                     (cl_map (cl_map cid) (map (mask^~ l) (bte (size l))))).
    rewrite -Hsize cp_bte cp_map_inst1 -cp_cl_map_comp. apply: cp_cl_map_ext => m. exact: cp_mask. }
  have Hrt : forall s : seq T, Logic.eq (cl_unmap cid (cl_map cid s)) s := cl_unmap_map cid cid (fun _ => Logic.eq_refl _).
  rewrite (cl_unmap_map (cl_map cid) (cl_unmap cid) Hrt).
  rewrite /powerset. have -> : [seq mask m l | m : (size l).-tuple bool <- enum {: (size l).-tuple bool}]
      = map (mask^~ l) (map (@tval (size l) bool) (enum {: (size l).-tuple bool})) by rewrite -map_comp.
  exact: (perm_map _ (cp_enum_perm (size l))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statement *)

Lemma cp_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cid cid (fun _ => Logic.eq_refl _) PR PL). Qed.

Definition src_mem_powerset (T : eqType) : Prop := ltac:(type_of_term (@mem_powerset T)).
Definition tgt_mem_powerset (T : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Util_Powerset_mem_powerset T (ct_decidable_eq T))).
Theorem mem_powerset_correspondence (T : eqType) : PropSPropRel (src_mem_powerset T) (tgt_mem_powerset T).
Proof.
  unfold src_mem_powerset, tgt_mem_powerset.
  apply: cp_forall_list => x X Hx. apply: cp_forall_list => y Y Hy.
  have Hrt : forall s : seq T, Logic.eq (cl_unmap cid (cl_map cid s)) s := cl_unmap_map cid cid (fun _ => Logic.eq_refl _).
  have Hrt' : forall s : I.List T, Logic.eq (cl_map cid (cl_unmap cid s)) s := cl_map_unmap cid cid (fun _ => Logic.eq_refl _).
  destruct Hx, Hy. apply: ct_imp.
  - rewrite (perm_mem (powerset_correspondence T x)).
    set P := I.Prosa_Classic_Util_Powerset_powerset T (ct_decidable_eq T) (cl_map cid x).
    have HP : ClListRel (cl_map cid) (cl_unmap (cl_unmap cid) P) P := coq_eq_to_imported_eq _ _ (cl_map_unmap _ _ Hrt' P).
    exact (cl_mem_rel_list _ (I.List T) (cl_map cid) (cl_unmap cid) Hrt y _ _ HP).
  - rewrite /sub_mem.
    apply: ct_forall_identity => z.
    exact (ct_imp _ _ _ _ (cl_mem_rel T T cid cid (fun _ => Logic.eq_refl _) z y)
                          (cl_mem_rel T T cid cid (fun _ => Logic.eq_refl _) z x)).
Qed.
