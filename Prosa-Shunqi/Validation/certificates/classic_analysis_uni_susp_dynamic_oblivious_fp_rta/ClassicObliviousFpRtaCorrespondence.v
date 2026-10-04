From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.minmax classic.model.suspension classic.model.priority classic.model.arrival.basic.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.susp.last_execution classic.model.schedule.uni.susp.suspension_intervals classic.model.schedule.uni.transformation.construction classic.model.schedule.uni.basic.platform classic.model.arrival.basic.job classic.model.arrival.basic.task classic.model.schedule.uni.schedulability classic.model.schedule.uni.response_time classic.model.schedule.uni.susp.platform classic.model.schedule.uni.susp.schedule classic.analysis.uni.susp.dynamic.oblivious.reduction classic.util.notation util.seqset util.sum classic.util.div_mod classic.model.arrival.basic.task_arrival classic.analysis.uni.basic.workload_bound_fp classic.util.fixedpoint classic.analysis.uni.basic.fp_rta_theory classic.analysis.uni.basic.fp_rta_comp classic.analysis.uni.susp.dynamic.oblivious.fp_rta.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicObliviousFpRta.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicObliviousFpRtaBase ClassicObliviousFpRtaList ClassicObliviousFpRtaOrd.



Module I := ImportedClassicObliviousFpRta.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/susp/dynamic/oblivious/fp_rta.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by its decision procedure
    ([ct_decidable_eq]); times by [SubNatRel]; job parameters pointwise through [SubNatRel]; suspension functions
    pointwise on related times; JLDP policies pointwise on related times; arrival sequences pointwise on related times;
    uniprocessor schedules pointwise through the option map; all with two-way totals.  Every definition is related for
    arbitrary related inputs.  [seq_min] as in the accepted classic minmax certificate; [suspended_at] as in the accepted
    classic suspension-intervals certificate; the construction from prefixes as in the accepted classic uniprocessor
    construction certificate (re-bound below: the construction step maps related schedules and instants to related
    choices); [schedule_prefix] through its kernel-checked Lean recursion equations. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cso_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cso_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cso_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) cso_false_rel). Qed.

Lemma cso_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cso_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma cso_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cso_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cso_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cso_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cso_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cso_unmap_rel T l) PR PL).
Qed.

Definition CsoParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cso_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsoParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cso_forall_cover _ _ (CsoParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cso_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cso_natl s') end.

Definition cso_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cso_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cso_one) (cso_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cso_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cso_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cso_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (cso_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (cso_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma cso_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cso_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cso_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma cso_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH cso_cl_append. reflexivity.
Qed.

Lemma cso_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsoFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma cso_bigcat_rel (A : Type) fR fL (Hf : CsoFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicObliviousFpRtaInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (cso_iota_range (nR - mR) 0) cso_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (cso_cl_map_ext _ _ Hpt) (cso_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) cso_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite cso_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CsoArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cso_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cso_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cso_arr_canonical aR : CsoArrRel aR (cso_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cso_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cso_arr_surjective aL : CsoArrRel (cso_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cso_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CsoArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cso_forall_cover _ _ CsoArrRel cso_arr_to_target cso_arr_to_source cso_arr_canonical cso_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cso_arrives_in aR aL (Ha : CsoArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cso_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma cso_consistent pR pL (Hp : CsoParRel Job pR pL) aR aL (Ha : CsoArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (cso_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

Lemma cso_is_a_set aR aL (Ha : CsoArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_sequence_is_a_set aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence_is_a_set Job dJ aL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (cso_uniq Job _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cso_arrives_at aR aL (Ha : CsoArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (cso_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma cso_has_arrived pR pL (Hp : CsoParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cso_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cso_snatl s') end.

Lemma cso_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cso_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cso_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cso_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cso_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cso_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cso_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsoFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cso_fun_canonical FR FL (HF : CsoFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cso_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cso_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsoFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cso_nat_sub_canonical nR mR.
  rewrite cso_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cso_foldr_add FL FR (cso_fun_canonical FR FL HF)).
  by rewrite cso_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cso_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cso_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cso_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cso_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cso_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CsoSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cso_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cso_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cso_sched_canonical sR : CsoSchedRel sR (cso_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cso_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cso_sched_surjective sL : CsoSchedRel (cso_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cso_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cso_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsoSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cso_forall_cover _ _ CsoSchedRel cso_sched_to_target cso_sched_to_source cso_sched_canonical cso_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cso_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CsoSchedRel Job sR (cso_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CsoSchedRel Job (cso_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cso_sched_canonical Job) (cso_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsoSchedRel Job sR sL.

Lemma cso_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cso_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cso_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cso_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cso_US_scheduled_at j tR tL Ht)). Qed.

Lemma cso_service_at_fun j : CsoFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cso_US_service_at j kR kL Hk). Qed.

Lemma cso_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cso_ico _ _ _ _ _ _ H1 H2 (cso_service_at_fun j)). Qed.

Lemma cso_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cso_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cso_US_completed_by cR cL (Hc : CsoParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cso_US_service j tR tL Ht)). Qed.

Lemma cso_US_pending aR aL (Ha : CsoParRel Job aR aL) cR cL (Hc : CsoParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cso_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (cso_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma cso_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CsoArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cso_US_scheduled_at j tR tL Ht)).
  exact (cso_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cso_US_jobs_must_arrive_to_execute aR aL (Ha : CsoParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cso_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cso_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cso_US_completed_jobs_dont_execute cR cL (Hc : CsoParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cso_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** * [\max] over ordinals against [maxFiltered] over [List.finRange] *)

Lemma cso_foldr_max (f : Lean.Nat -> Lean.Nat) (g : nat -> nat)
    (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat I.Nat_max (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
                        (I.List_map_inst3 Lean.Nat Lean.Nat f (co_natl s)))
                     (sub_nat_to_imported (foldr maxn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.Nat_max (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat I.Nat_max (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))
              (I.List_map_inst3 Lean.Nat Lean.Nat f (co_natl s))))
         (sub_nat_to_imported (maxn (g k) (foldr maxn 0 (map g s))))).
  rewrite IH Hf. exact (ct_max_canonical _ _).
Qed.

Lemma cso_max_rel nR nL (Hn : SubNatRel nR nL) (QR : 'I_nR -> bool) (QL : Fin nL -> I.Bool) (HQ : CoOrdPredRel nR nL QR QL) :
  SubNatRel (\max_(i < nR | QR i) nat_of_ord i)
    (I.Prosa_Util_Sum_maxFiltered_inst1 (Fin nL) (I.List_finRange nL) QL (fun o => I.Fin_val nL o)).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicObliviousFpRtaInterface_maxFiltered_finRange
             (sub_nat_to_imported nR) QL (fun o => I.Fin_val _ o))).
  rewrite big_mkcond (co_big_ord maxn 0 nR (fun i => if QR i then nat_of_ord i else 0) 0).
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (co_iota_range nR 0).
  have HF : forall o oL, CoOrdRel nR (sub_nat_to_imported nR) o oL ->
      Logic.eq (I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0))
               (sub_nat_to_imported (if QR o then nat_of_ord o else 0)).
  { intros o oL Ho. rewrite (ct_bool_rel_logic _ _ (HQ o oL Ho)). destruct (QR o).
    - exact (Logic.eq_sym (imported_eq_to_coq_eq _ _ Ho)).
    - reflexivity. }
  exact (cso_foldr_max _ _ (co_fam_related nR sub_nat_to_imported (fun i => if QR i then nat_of_ord i else 0)
           (fun oL => I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0)) 0 HF) (iota 0 nR)).
Qed.

Lemma cso_ite_rel bR bL (Hb : CtBoolRel bR bL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR)
    (I.ite Lean.Nat (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) xL yL).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). destruct bR; [exact Hx | exact Hy]. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cso_LE_time_after_last_execution (Job : eqType) aR aL (Ha : CsoParRel Job aR aL)
    sR sL (Hs : CsoSchedRel Job sR sL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (LastExecution.time_after_last_execution aR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_LastExecution_LastExecution_time_after_last_execution Job (ct_decidable_eq Job) aL sL j tL).
Proof.
  assert (HQ : CoOrdPredRel tR tL (fun o => UniprocessorSchedule.scheduled_at sR j o)
      (fun oL => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job (ct_decidable_eq Job) sL j (I.Fin_val tL oL))).
  { intros o oL Ho. exact (cso_US_scheduled_at Job sR sL Hs j _ _ Ho). }
  exact (cso_ite_rel _ _ (co_exists_rel tR tL Ht _ _ HQ) _ _
           (sub_add_correspondence _ _ _ _ (cso_max_rel tR tL Ht _ _ HQ) (sub_nat_rel_canonical 1)) _ _ (Ha j)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Section SuspSusp.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSusp := (I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).

Definition CsoSuspRel (sR : Suspension.job_suspension Job) (sL : LSusp) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (sR j tR) (sL j tL).

Definition cso_susp_to_target (sR : Suspension.job_suspension Job) : LSusp :=
  fun j tL => sub_nat_to_imported (sR j (sub_nat_to_rocq tL)).

Definition cso_susp_to_source (sL : LSusp) : Suspension.job_suspension Job :=
  fun j tR => sub_nat_to_rocq (sL j (sub_nat_to_imported tR)).

Lemma cso_susp_canonical sR : CsoSuspRel sR (cso_susp_to_target sR).
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  unfold cso_susp_to_target. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma cso_susp_surjective sL : CsoSuspRel (cso_susp_to_source sL) sL.
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma cso_forall_susp (PR : Suspension.job_suspension Job -> Prop) (PL : LSusp -> SProp) :
  (forall sR sL, CsoSuspRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cso_forall_cover _ _ CsoSuspRel cso_susp_to_target cso_susp_to_source cso_susp_canonical cso_susp_surjective PR PL). Qed.

End SuspSusp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cso_SU_job_suspension (Job : eqType) :
  And (forall sR : Suspension.job_suspension Job, CsoSuspRel Job sR (cso_susp_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job (ct_decidable_eq Job), CsoSuspRel Job (cso_susp_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cso_susp_canonical Job) (cso_susp_surjective Job)). Qed.

Lemma cso_SU_total_suspension (Job : eqType) cR cL (Hc : CsoParRel Job cR cL) sR sL (Hs : CsoSuspRel Job sR sL) j :
  SubNatRel (Suspension.total_suspension cR sR j) (I.Prosa_Classic_Model_Suspension_Suspension_total_suspension Job (ct_decidable_eq Job) cL sL j).
Proof. exact (cso_ico 0 _ (cR j) (cL j) (sR j) (sL j) (sub_nat_rel_canonical 0) (Hc j) (Hs j)). Qed.

Lemma cso_SU_dynamic_suspension_model (Task Job : eqType) cR cL (Hc : CsoParRel Job cR cL)
    (job_task : Job -> Task) sR sL (Hs : CsoSuspRel Job sR sL) bR bL (Hb : CsoParRel Task bR bL) :
  PropSPropRel (Suspension.dynamic_suspension_model cR job_task sR bR)
    (I.Prosa_Classic_Model_Suspension_Suspension_dynamic_suspension_model Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) cL job_task sL bL).
Proof.
  apply: ct_forall_identity => j.
  exact (sub_nat_le_correspondence _ _ _ _ (cso_SU_total_suspension Job cR cL Hc sR sL Hs j) (Hb (job_task j))).
Qed.

Section SuspintDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsoSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CsoParRel Job aR aL) (Hc : CsoParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CsoSuspRel Job nR nL.

Notation TALE := (cso_LE_time_after_last_execution Job aR aL Ha sR sL Hs).

Lemma cso_SI_suspension_duration j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (SuspensionIntervals.suspension_duration aR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspension_duration Job dJ aL nL sL j tL).
Proof. exact (Hn j _ _ (cso_US_service Job sR sL Hs j _ _ (TALE j tR tL Ht))). Qed.

Lemma cso_SI_suspended_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (SuspensionIntervals.suspended_at aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_at Job dJ aL cL nL sL j tL).
Proof.
  have HT := TALE j tR tL Ht.
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (cso_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht))
           (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Ht)
              (ct_decide_lt _ _ _ _ Ht (sub_add_correspondence _ _ _ _ HT (cso_SI_suspension_duration j tR tL Ht))))).
Qed.

Lemma cso_SI_respects_self_suspensions :
  PropSPropRel (SuspensionIntervals.respects_self_suspensions aR cR nR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_respects_self_suspensions Job dJ aL cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cso_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (cso_SI_suspended_at j tR tL Ht)) cso_false_rel).
Qed.

End SuspintDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CsoRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cso_rel_canonical (T : Type) (rR : T -> T -> bool) : CsoRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cso_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CsoRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cso_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CsoRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cso_forall_cover _ _ (CsoRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cso_rel_canonical T) (cso_rel_surjective T) PR PL).
Qed.

Definition CsoJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CsoRelRel T (rR tR) (rL tL).

Lemma cso_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CsoJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cso_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CsoJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cso_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CsoJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cso_forall_cover _ _ (CsoJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cso_jldp_canonical T) (cso_jldp_surjective T) PR PL).
Qed.

(* ------------------------------------------------------------------ *)
(** * [seq_min] (as in the accepted classic minmax certificate) *)

Lemma cso_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := f_equal cl_unopt (imported_eq_to_coq_eq _ _ E).
    by rewrite !cl_unopt_opt in E'.
Qed.

Section MinmaxArg.
Variables (T1 : eqType) (T2R : eqType) (T2L : Type) (d2 : I.DecidableEq T2L).
Variables (relR : T2R -> T2R -> bool) (relL : T2L -> T2L -> I.Bool) (FR : T1 -> T2R) (FL : T1 -> T2L).
Hypothesis Hcomp : forall x y, CtBoolRel (relR (FR x) (FR y)) (relL (FL x) (FL y)).
Notation d1 := (ct_decidable_eq T1).

End MinmaxArg.

(* ------------------------------------------------------------------ *)
(** * Options *)

Lemma cso_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (cso_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition cso_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma cso_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma cso_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

(* ------------------------------------------------------------------ *)
(** * Construction from prefixes, specialised at related inputs

    As in the accepted v0.6 [implementation/facts/generic_schedule.v] certificate: the construction function
    [build_schedule : schedule Job -> time -> option Job] is a higher-order input; the certificates below are stated for
    any source function and any Lean function that agree (through the option map) on related schedules and related
    instants ([Hbuild]), and for related base schedules ([Hbase]); the predicate [P] of the last statement is related
    pointwise through the option map ([HP]).  Inside the statements every quantified schedule, instant and job is covered
    in both directions. *)

Section UconsConstruction.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Variable buildR : UniprocessorSchedule.schedule Job -> nat -> option Job.
Variable buildL : LSched -> Lean.Nat -> I.Option Job.
Hypothesis Hbuild : forall sR sL, CsoSchedRel Job sR sL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (buildR sR tR)) (buildL sL tL).
Variables (baseR : UniprocessorSchedule.schedule Job) (baseL : LSched).
Hypothesis Hbase : CsoSchedRel Job baseR baseL.

Lemma cso_nat_eqb tR tL t'R t'L : SubNatRel tR tL -> SubNatRel t'R t'L ->
  CtBoolRel (tR == t'R) (I.Decidable_decide (Lean.eq tL t'L) (I.instDecidableEqNat tL t'L)).
Proof. intros Ht Ht'. exact (ct_decide_eq_nat _ _ _ _ Ht Ht'). Qed.

Lemma cso_UC_update_schedule prevR prevL (Hprev : CsoSchedRel Job prevR prevL) nR nL (Hn : SubNatRel nR nL) :
  CsoSchedRel Job (@ScheduleConstruction.update_schedule Job buildR prevR nR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ buildL prevL nL).
Proof.
  intros tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (cso_nat_eqb tR tL nR nL Ht Hn)).
  case: (tR == nR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev tR tL Ht)).
Qed.

Lemma cso_prefix_canonical (mR : nat) :
  CsoSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL (sub_nat_to_imported mR)).
Proof.
  induction mR as [|m IH].
  - refine (cso_trs (cso_lsym (I.Prosa_Validation_ClassicObliviousFpRtaInterface_production_schedule_prefix_zero Job dJ buildL baseL))
              (fun z => CsoSchedRel Job _ z) _).
    exact (cso_UC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hm1 : SubNatRel m.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported m) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (cso_src_transport (fun x => SubNatRel x _) _ _ (addn1 m)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical 1))). }
    refine (cso_trs Hm1 (fun z => CsoSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR m.+1) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) _).
    refine (cso_trs (cso_lsym (I.Prosa_Validation_ClassicObliviousFpRtaInterface_production_schedule_prefix_succ Job dJ buildL baseL (sub_nat_to_imported m)))
              (fun z => CsoSchedRel Job _ z) _).
    exact (cso_UC_update_schedule _ _ IH _ _ Hm1).
Qed.

Lemma cso_UC_schedule_prefix mR mL (Hm : SubNatRel mR mL) :
  CsoSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL mL).
Proof. exact (cso_trs Hm (fun z => CsoSchedRel Job _ (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) (cso_prefix_canonical mR)). Qed.

End UconsConstruction.

Section SuspschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsoSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CsoParRel Job aR aL) (Hc : CsoParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CsoSuspRel Job nR nL.

Lemma cso_SS_backlogged j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithSuspensions.backlogged aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Schedule_ScheduleWithSuspensions_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _
           (ct_bool_and _ _ _ _ (cso_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)
              (ct_bool_not _ _ (cso_US_scheduled_at Job sR sL Hs j _ _ Ht)))
           (ct_bool_not _ _ (cso_SI_suspended_at Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht))).
Qed.

End SuspschedDefs.

Section SuspplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsoSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CsoParRel Job aR aL) (Hc : CsoParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CsoSuspRel Job nR nL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CsoArrRel Job arrR arrL.

Notation BL := (cso_SS_backlogged Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
Notation SA := (cso_US_scheduled_at Job sR sL Hs).

Lemma cso_SP_work_conserving :
  PropSPropRel (PlatformWithSuspensions.work_conserving aR cR nR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_work_conserving Job dJ aL cL nL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cso_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma cso_SP_respects_FP_policy (job_task : Job -> Task) hR hL (Hh : CsoRelRel Task hR hL) :
  PropSPropRel (PlatformWithSuspensions.respects_FP_policy aR cR job_task nR arrR sR hR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_respects_FP_policy Task dT Job dJ aL cL job_task nL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cso_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh (job_task j_hp) (job_task j))).
Qed.

End SuspplatDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsoSchedRel Job sR sL.

End UrtDefs.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cso_PR_FP_policy :
  And (forall rR : Priority.FP_policy Task, CsoRelRel Task rR (fun a b => ct_b2l (rR a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_FP_policy Task dT, CsoRelRel Task (fun a b => ct_l2b (rL a b)) rL).
Proof. exact (And_intro _ _ (cso_rel_canonical Task) (cso_rel_surjective Task)). Qed.

Lemma cso_reflexive (T : Type) rR rL (Hr : CsoRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma cso_transitive (T : Type) rR rL (Hr : CsoRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma cso_PR_FP_is_reflexive rR rL (Hr : CsoRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_reflexive Task dT rL).
Proof. exact (cso_reflexive Task rR rL Hr). Qed.

Lemma cso_PR_FP_is_transitive rR rL (Hr : CsoRelRel Task rR rL) :
  PropSPropRel (Priority.FP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_FP_is_transitive Task dT rL).
Proof. exact (cso_transitive Task rR rL Hr). Qed.

Lemma cso_PR_FP_is_total_over_task_set rR rL (Hr : CsoRelRel Task rR rL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (Priority.FP_is_total_over_task_set rR ts)
    (I.Prosa_Classic_Model_Priority_Priority_FP_is_total_over_task_set Task dT rL tsL).
Proof.
  apply: ct_forall_identity => x1. apply: ct_forall_identity => x2.
  apply: ct_imp; first exact (cso_mem Task x1 ts tsL Hts).
  apply: ct_imp; first exact (cso_mem Task x2 ts tsL Hts).
  exact (ct_or _ _ _ _ (ct_bool_truth _ _ (Hr x1 x2)) (ct_bool_truth _ _ (Hr x2 x1))).
Qed.

End PriodefsDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cso_J_job_cost_positive cR cL (Hc : CsoParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cso_J_job_deadline_positive dR dL (Hd : CsoParRel Job dR dL) j :
  CtBoolRel (Job.job_deadline_positive dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_positive Job dJ dL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd j)). Qed.

Lemma cso_J_job_cost_le_deadline cR cL dR dL (Hc : CsoParRel Job cR cL) (Hd : CsoParRel Job dR dL) j :
  CtBoolRel (Job.job_cost_le_deadline cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_deadline Job dJ cL dL j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Hd j)). Qed.

Lemma cso_J_valid_realtime_job cR cL dR dL (Hc : CsoParRel Job cR cL) (Hd : CsoParRel Job dR dL) j :
  PropSPropRel (Job.valid_realtime_job cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_realtime_job Job dJ cL dL j).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (cso_J_job_cost_positive cR cL Hc j)).
  apply: ct_and; first exact (ct_bool_truth _ _ (cso_J_job_cost_le_deadline cR cL dR dL Hc Hd j)).
  exact (ct_bool_truth _ _ (cso_J_job_deadline_positive dR dL Hd j)).
Qed.

Lemma cso_J_job_cost_le_task_cost tcR tcL (Htc : CsoParRel Task tcR tcL) cR cL (Hc : CsoParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cso_J_job_deadline_eq_task_deadline tdR tdL (Htd : CsoParRel Task tdR tdL) dR dL (Hd : CsoParRel Job dR dL)
    (job_task : Job -> Task) j :
  PropSPropRel (Job.job_deadline_eq_task_deadline tdR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_eq_task_deadline Task dT tdL Job dJ dL job_task j).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))). Qed.

Lemma cso_J_valid_sporadic_job tcR tcL tdR tdL (Htc : CsoParRel Task tcR tcL) (Htd : CsoParRel Task tdR tdL)
    cR cL dR dL (Hc : CsoParRel Job cR cL) (Hd : CsoParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task dT tcL tdL Job dJ cL dL job_task j).
Proof.
  apply: ct_and; first exact (cso_J_valid_realtime_job cR cL dR dL Hc Hd j).
  apply: ct_and; first exact (ct_bool_truth _ _ (cso_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
  exact (cso_J_job_deadline_eq_task_deadline tdR tdL Htd dR dL Hd job_task j).
Qed.

End JobDefs.

Lemma cso_iff (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [f g]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (f (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (g (sprop_to_prop _ _ HQ q))).
  - intros [f g]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (f (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (g (prop_to_sprop _ _ HQ q))).
Qed.

Section TaskDefsP.
Variables (Task : eqType).
Notation dT := (ct_decidable_eq Task).
Notation c0 := (sub_nat_rel_canonical 0).

Lemma cso_TK_task_cost_positive cR cL (Hc : CsoParRel Task cR cL) tsk :
  CtBoolRel (SporadicTask.task_cost_positive cR tsk) (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_cost_positive Task dT cL tsk).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc tsk)). Qed.

Lemma cso_TK_task_period_positive pR pL (Hp : CsoParRel Task pR pL) tsk :
  CtBoolRel (SporadicTask.task_period_positive pR tsk) (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_period_positive Task dT pL tsk).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hp tsk)). Qed.

Lemma cso_TK_task_deadline_positive dR dL (Hd : CsoParRel Task dR dL) tsk :
  CtBoolRel (SporadicTask.task_deadline_positive dR tsk) (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_deadline_positive Task dT dL tsk).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd tsk)). Qed.

Lemma cso_TK_task_cost_le_deadline cR cL dR dL (Hc : CsoParRel Task cR cL) (Hd : CsoParRel Task dR dL) tsk :
  CtBoolRel (SporadicTask.task_cost_le_deadline cR dR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_cost_le_deadline Task dT cL dL tsk).
Proof. exact (ct_decide_le _ _ _ _ (Hc tsk) (Hd tsk)). Qed.

Lemma cso_TK_task_cost_le_period cR cL pR pL (Hc : CsoParRel Task cR cL) (Hp : CsoParRel Task pR pL) tsk :
  CtBoolRel (SporadicTask.task_cost_le_period cR pR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_task_cost_le_period Task dT cL pL tsk).
Proof. exact (ct_decide_le _ _ _ _ (Hc tsk) (Hp tsk)). Qed.

Lemma cso_TK_is_valid_sporadic_task cR cL pR pL dR dL
    (Hc : CsoParRel Task cR cL) (Hp : CsoParRel Task pR pL) (Hd : CsoParRel Task dR dL) tsk :
  PropSPropRel (SporadicTask.is_valid_sporadic_task cR pR dR tsk)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTask_is_valid_sporadic_task Task dT cL pL dL tsk).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (cso_TK_task_cost_positive cR cL Hc tsk)).
  apply: ct_and; first exact (ct_bool_truth _ _ (cso_TK_task_period_positive pR pL Hp tsk)).
  apply: ct_and; first exact (ct_bool_truth _ _ (cso_TK_task_deadline_positive dR dL Hd tsk)).
  apply: ct_and; first exact (ct_bool_truth _ _ (cso_TK_task_cost_le_deadline cR cL dR dL Hc Hd tsk)).
  exact (ct_bool_truth _ _ (cso_TK_task_cost_le_period cR cL pR pL Hc Hp tsk)).
Qed.

Lemma cso_TK_valid_sporadic_taskset cR cL pR pL dR dL
    (Hc : CsoParRel Task cR cL) (Hp : CsoParRel Task pR pL) (Hd : CsoParRel Task dR dL) ts tsL (Hts : ClListRel cid ts tsL) :
  PropSPropRel (SporadicTaskset.valid_sporadic_taskset cR pR dR ts)
    (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_valid_sporadic_taskset Task dT cL pL dL tsL).
Proof.
  apply: ct_forall_identity => tsk.
  exact (ct_imp _ _ _ _ (cso_mem Task tsk ts tsL Hts) (cso_TK_is_valid_sporadic_task cR cL pR pL dR dL Hc Hp Hd tsk)).
Qed.

End TaskDefsP.

Section UplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsoSchedRel Job sR sL.

End UplatDefs.

(* ------------------------------------------------------------------ *)
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section SeqSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma cso_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicObliviousFpRtaInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicObliviousFpRtaInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma cso_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cso_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma cso_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicObliviousFpRtaInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicObliviousFpRtaInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicObliviousFpRtaInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma cso_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (cso_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End SeqSums.

Definition CsoPredRel (T : Type) (pR : T -> bool) (pL : T -> I.Bool) : SProp := forall x, CtBoolRel (pR x) (pL x).

Lemma cso_forall_pred (T : Type) (PR : (T -> bool) -> Prop) (PL : (T -> I.Bool) -> SProp) :
  (forall pR pL, CsoPredRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cso_forall_cover _ _ (CsoPredRel T) (fun pR x => ct_b2l (pR x)) (fun pL x => ct_l2b (pL x))
           (fun pR x => ct_bool_canonical _) (fun pL x => ct_bool_surjective _) PR PL).
Qed.

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cso_TA_sporadic_task_model tpR tpL (Htp : CsoParRel Task tpR tpL)
    jaR jaL (Hja : CsoParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CsoArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task dT tpL Job dJ jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (cso_ne Job j j').
  apply: ct_imp; first exact (cso_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (cso_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

End TaskArrivalDefs.

(* ------------------------------------------------------------------ *)
(** * Nat subtraction / Euclidean division bridge (re-bound copy of the accepted NatSubCorrespondence and
    DivModCorrespondence, through the exported [DivModInterface] equations) *)

(** Adapter for the operations that occur in the actual freshly imported
    [Prosa.Util.Nat] theorem types. *)
Definition nat_target_add (a b : Lean.Nat) : Lean.Nat :=
  I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHAdd_inst1 Lean.Nat I.instAddNat) a b.

Definition nat_target_sub (a b : Lean.Nat) : Lean.Nat :=
  I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHSub_inst1 Lean.Nat I.instSubNat) a b.

Definition nat_target_le (a b : Lean.Nat) : SProp :=
  I.LE_le_inst1 Lean.Nat I.instLENat a b.

Lemma nat_target_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (nat_target_add aL bL).
Proof.
  intros Ha Hb. exact (sub_add_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma nat_target_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (nat_target_le aL bL).
Proof.
  intros Ha Hb. exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

(** The actual compiled Lean subtraction is a course-of-values recursion on
    the amount being subtracted.  Its two computation equations are
    definitionally true in the imported artifact. *)
Lemma nat_target_sub_zero (a : Lean.Nat) :
  Lean.eq (nat_target_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma nat_target_sub_succ (a b : Lean.Nat) :
  Lean.eq (nat_target_sub a (Lean.Nat_succ b))
    (I.Nat_pred (nat_target_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (I.Nat_pred (nat_target_sub a b))).
Qed.

Fixpoint rocq_iterated_pred (a b : nat) : nat :=
  match b with
  | O => a
  | S b' => Nat.pred (rocq_iterated_pred a b')
  end.

Lemma rocq_iterated_pred_is_subn (a b : nat) :
  Logic.eq (rocq_iterated_pred a b) (a - b).
Proof.
  revert a. induction b as [|b IH]; intro a; cbn [rocq_iterated_pred].
  - rewrite subn0. reflexivity.
  - rewrite (IH a). exact (Logic.eq_sym (subnS a b)).
Qed.

Definition nat_target_pred_canonical (n : nat) :
  Lean.eq (I.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (I.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma nat_target_sub_iterated_pred (a b : nat) :
  Lean.eq
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (nat_target_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (nat_target_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr I.Nat_pred _ _ IH)
        (nat_target_pred_canonical (rocq_iterated_pred a b)))).
Qed.

(** Direct computation proof for truncated subtraction.  This covers both
    branches: a positive residual and truncation to zero. *)
Lemma nat_target_sub_canonical (a b : nat) :
  Lean.eq
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (nat_target_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma nat_target_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (nat_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (nat_target_sub_canonical aR bR))
    (sub_imported_eq_congr2 nat_target_sub _ _ _ _ Ha Hb)).
Qed.

(** Explicit branch witnesses requested by the translation policy. *)
Lemma nat_target_sub_nontruncated a b :
  is_true (leq b a) ->
  SubNatRel (a - b)
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof. intros _. apply nat_target_sub_correspondence; apply sub_nat_rel_canonical. Qed.

Lemma rocq_sub_truncates a b :
  is_true (ltn a b) -> Logic.eq (a - b) O.
Proof.
  move: a. elim: b => [|b IH] [|a] //= H. exact: IH.
Qed.

Lemma nat_target_sub_truncated a b :
  is_true (ltn a b) ->
  SubNatRel O
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  intro Hlt. have Hz : Logic.eq (a - b) O := rocq_sub_truncates a b Hlt.
  rewrite <- Hz. apply nat_target_sub_correspondence; apply sub_nat_rel_canonical.
Qed.

(** Operation-level bridge for the exact [Nat.div]/[Nat.mod] interface
    exported from the compiled [Prosa.Util.Div_mod] artifact.  The proof uses
    the two Euclidean characterizations on each side; it does not unfold the
    implementation-specific Lean [Nat.brecOn]/[Nat.below] recursion. *)

Definition dm_imported_add (a b : Lean.Nat) : Lean.Nat :=
  I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHAdd_inst1 Lean.Nat I.instAddNat) a b.

Definition dm_imported_mul (a b : Lean.Nat) : Lean.Nat :=
  I.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHMul_inst1 Lean.Nat I.instMulNat) a b.

Definition dm_imported_div (a b : Lean.Nat) : Lean.Nat :=
  I.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHDiv_inst1 Lean.Nat I.Nat_instDiv) a b.

Definition dm_imported_sub (a b : Lean.Nat) : Lean.Nat :=
  I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHSub_inst1 Lean.Nat I.instSubNat) a b.

Definition dm_imported_mod (a b : Lean.Nat) : Lean.Nat :=
  I.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (I.instHMod_inst1 Lean.Nat I.Nat_instMod) a b.

Definition dm_imported_lt (a b : Lean.Nat) : SProp :=
  I.LT_lt_inst1 Lean.Nat I.instLTNat a b.

Definition dm_imported_le (a b : Lean.Nat) : SProp :=
  I.LE_le_inst1 Lean.Nat I.instLENat a b.

Definition dm_imported_dvd (a b : Lean.Nat) : SProp :=
  I.Dvd_dvd_inst1 Lean.Nat I.Nat_instDvd a b.

Definition dm_imported_zero : Lean.Nat :=
  I.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (I.instOfNatNat Lean.Nat_zero).

Definition dm_imported_one : Lean.Nat :=
  I.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (I.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition dm_imported_div_floor (a b : Lean.Nat) : Lean.Nat :=
  I.Prosa_Classic_Util_DivMod_div_floor a b.

Definition dm_imported_div_ceil (a b : Lean.Nat) : Lean.Nat :=
  I.Prosa_Classic_Util_DivMod_div_ceil a b.

Definition dm_coq_false_to_target (H : Logic.False) :
    I.False :=
  match H return I.False with end.

Lemma dm_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (dm_imported_add aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR + bR) (sub_imported_add aL bL)).
  exact (sub_add_correspondence aR aL bR bL).
Qed.

Lemma dm_mul_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR * bR) (dm_imported_mul aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR * bR) (sub_imported_mul aL bL)).
  exact (sub_mul_correspondence aR aL bR bL).
Qed.

Lemma dm_sub_zero (a : Lean.Nat) :
  Lean.eq (dm_imported_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma dm_sub_succ (a b : Lean.Nat) :
  Lean.eq (dm_imported_sub a (Lean.Nat_succ b))
    (I.Nat_pred (dm_imported_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (I.Nat_pred (dm_imported_sub a b))).
Qed.

Definition dm_pred_canonical (n : nat) :
  Lean.eq (I.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (I.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma dm_sub_iterated_pred (a b : nat) :
  Lean.eq
    (dm_imported_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  revert a. induction b as [|b IH]; intro a.
  - exact (dm_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (dm_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr I.Nat_pred _ _ (IH a))
        (dm_pred_canonical (rocq_iterated_pred a b)))).
Qed.

Lemma dm_sub_canonical (a b : nat) :
  Lean.eq
    (dm_imported_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (dm_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma dm_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (dm_imported_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_sub_canonical aR bR))
    (sub_imported_eq_congr2 dm_imported_sub _ _ _ _ Ha Hb)).
Qed.

Lemma dm_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (dm_imported_le aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (leq aR bR)) (sub_imported_le aL bL)).
  exact (sub_nat_le_correspondence aR aL bR bL).
Qed.

Lemma dm_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (dm_imported_lt aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (ltn aR bR)) (sub_imported_lt aL bL)).
  exact (sub_nat_lt_correspondence aR aL bR bL).
Qed.

Lemma dm_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Lemma dm_succ_correspondence nR nL :
  SubNatRel nR nL ->
  SubNatRel nR.+1 (dm_imported_add nL dm_imported_one).
Proof.
  intro Hn. have H := dm_add_correspondence nR nL 1 dm_imported_one
    Hn (sub_nat_rel_canonical 1).
  rewrite addn1 in H. exact H.
Qed.

Lemma dm_div_mod_decoded_canonical (x y : nat) :
  Logic.eq
    (sub_nat_to_rocq
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %/ y) /\
  Logic.eq
    (sub_nat_to_rocq
      (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %% y).
Proof.
  case Hy: y => [|y'].
  - subst y. split.
    + rewrite divn0.
      have H :=
        I.Prosa_Validation_DivModInterface_production_div_zero
          (sub_nat_to_imported x).
      exact (f_equal sub_nat_to_rocq
        (imported_eq_to_coq_eq _ _ H)).
    + rewrite modn0.
      have H :=
        I.Prosa_Validation_DivModInterface_production_mod_zero
          (sub_nat_to_imported x).
      transitivity
        (sub_nat_to_rocq (sub_nat_to_imported x)).
      * exact (f_equal sub_nat_to_rocq
          (imported_eq_to_coq_eq _ _ H)).
      * exact (sub_nat_rocq_roundtrip x).
  - have Hypos : is_true (ltn O y'.+1) by done.
    set xL := sub_nat_to_imported x.
    set yL := sub_nat_to_imported y'.+1.
    set qL := dm_imported_div xL yL.
    set rL := dm_imported_mod xL yL.
    have HrLtR : is_true (ltn (sub_nat_to_rocq rL) y'.+1).
    { exact (sprop_to_prop _ _
        (dm_lt_correspondence (sub_nat_to_rocq rL) rL y'.+1 yL
          (sub_nat_rel_surjective rL) (sub_nat_rel_canonical y'.+1))
        (I.Prosa_Validation_DivModInterface_production_mod_lt
          xL yL
          (prop_to_sprop _ _
            (dm_lt_correspondence O dm_imported_zero y'.+1 yL
              (sub_nat_rel_canonical O) (sub_nat_rel_canonical y'.+1))
            Hypos))). }
    have HdecompR : Logic.eq
        (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL) x.
    { exact (sprop_to_prop _ _
        (dm_eq_correspondence
          (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL)
          (dm_imported_add (dm_imported_mul yL qL) rL)
          x xL
          (dm_add_correspondence _ _ _ _
            (dm_mul_correspondence y'.+1 yL
              (sub_nat_to_rocq qL) qL
              (sub_nat_rel_canonical y'.+1)
              (sub_nat_rel_surjective qL))
            (sub_nat_rel_surjective rL))
          (sub_nat_rel_canonical x))
        (I.Prosa_Validation_DivModInterface_production_div_add_mod
          xL yL)). }
    have Hx : Logic.eq x
        (sub_nat_to_rocq qL * y'.+1 + sub_nat_to_rocq rL).
    { rewrite mulnC. exact (Logic.eq_sym HdecompR). }
    have Hedge : Logic.eq (edivn x y'.+1)
        (sub_nat_to_rocq qL, sub_nat_to_rocq rL).
    { rewrite Hx. exact (@edivn_eq y'.+1 (sub_nat_to_rocq qL)
        (sub_nat_to_rocq rL) HrLtR). }
    have Hq := f_equal (@Datatypes.fst nat nat) Hedge.
    change (Logic.eq (divn x (S y')) (sub_nat_to_rocq qL)) in Hq.
    have Hr := f_equal (@Datatypes.snd nat nat) Hedge.
    change (Logic.eq (Datatypes.snd (edivn x (S y')))
      (sub_nat_to_rocq rL)) in Hr.
    rewrite <- (modn_def x y'.+1) in Hr.
    split; exact (Logic.eq_sym Hq) || exact (Logic.eq_sym Hr).
Qed.

Lemma dm_div_canonical (x y : nat) :
  Lean.eq
    (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %/ y)).
Proof.
  have Hdecoded := proj1 (dm_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma dm_mod_canonical (x y : nat) :
  Lean.eq
    (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %% y)).
Proof.
  have Hdecoded := proj2 (dm_div_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (dm_imported_mod (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma dm_div_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %/ yR) (dm_imported_div xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_div_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_div _ _ _ _ Hx Hy)).
Qed.

Lemma dm_mod_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %% yR) (dm_imported_mod xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_mod_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_mod _ _ _ _ Hx Hy)).
Qed.

Lemma dm_dvd_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  PropSPropRel (is_true (yR %| xR)) (dm_imported_dvd yL xL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro HdvdR.
    apply (I.Iff_mpr _ _
      (I.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
        xL yL)).
    apply (prop_to_sprop _ _
      (dm_eq_correspondence (xR %% yR) (dm_imported_mod xL yL)
        O dm_imported_zero
        (dm_mod_correspondence xR xL yR yL Hx Hy)
        (sub_nat_rel_canonical O))).
    move: HdvdR. rewrite /dvdn. by move/eqP.
  - intro HdvdL. apply strictly_inhabits.
    rewrite /dvdn. apply/eqP.
    apply (sprop_to_prop _ _
      (dm_eq_correspondence (xR %% yR) (dm_imported_mod xL yL)
        O dm_imported_zero
        (dm_mod_correspondence xR xL yR yL Hx Hy)
        (sub_nat_rel_canonical O))).
    exact (I.Iff_mp _ _
      (I.Prosa_Validation_DivModInterface_production_dvd_iff_mod_eq_zero
        xL yL) HdvdL).
Qed.

Lemma dm_div_floor_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %/ yR) (dm_imported_div_floor xL yL).
Proof.
  intros Hx Hy.
  change (SubNatRel (xR %/ yR) (dm_imported_div xL yL)).
  exact (dm_div_correspondence xR xL yR yL Hx Hy).
Qed.

Lemma dm_bool_false_no_truth (b : bool) :
  Logic.eq b false -> is_true b -> Logic.False.
Proof. destruct b; cbn; intros Hfalse Htruth; discriminate. Qed.

Definition dm_not_dvd_canonical (x y : nat)
    (Hfalse : Logic.eq (y %| x) false) :
    I.Not
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x)) :=
  fun HdvdL =>
    dm_coq_false_to_target
      (dm_bool_false_no_truth (y %| x) Hfalse
        (sprop_to_prop _ _
        (dm_dvd_correspondence x (sub_nat_to_imported x)
          y (sub_nat_to_imported y)
          (sub_nat_rel_canonical x) (sub_nat_rel_canonical y)) HdvdL)).

Lemma dm_div_succ_canonical (x y : nat) :
  Lean.eq
    (dm_imported_add
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      dm_imported_one)
    (sub_nat_to_imported ((x %/ y).+1)).
Proof.
  have Hrel := dm_add_correspondence
    (x %/ y) (dm_imported_div (sub_nat_to_imported x)
      (sub_nat_to_imported y))
    1 dm_imported_one
    (dm_div_correspondence x (sub_nat_to_imported x)
      y (sub_nat_to_imported y)
      (sub_nat_rel_canonical x) (sub_nat_rel_canonical y))
    (sub_nat_rel_canonical 1).
  unfold SubNatRel in Hrel.
  rewrite addn1 in Hrel.
  exact (sub_imported_eq_sym _ _ Hrel).
Qed.

Lemma dm_div_ceil_canonical (x y : nat) :
  Lean.eq
    (dm_imported_div_ceil (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported
      (if y %| x then x %/ y else (x %/ y).+1)).
Proof.
  have Hbody :=
    I.Prosa_Validation_DivModInterface_production_div_ceil_eq
      (sub_nat_to_imported x) (sub_nat_to_imported y).
  destruct (y %| x) eqn:HdvdR.
  - have HdvdR' : is_true (y %| x) by rewrite HdvdR.
    have HdvdL := prop_to_sprop _ _
      (dm_dvd_correspondence x (sub_nat_to_imported x)
        y (sub_nat_to_imported y)
        (sub_nat_rel_canonical x) (sub_nat_rel_canonical y)) HdvdR'.
    have Hif := I.if_pos
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x))
      (I.Nat_decidable_dvd
        (sub_nat_to_imported y) (sub_nat_to_imported x)) HdvdL
      Lean.Nat
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      (dm_imported_add
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
        dm_imported_one).
    exact (sub_imported_eq_trans _ _ _ Hbody
      (sub_imported_eq_trans _ _ _ Hif (dm_div_canonical x y))).
  - have Hif := I.if_neg
      (dm_imported_dvd (sub_nat_to_imported y) (sub_nat_to_imported x))
      (I.Nat_decidable_dvd
        (sub_nat_to_imported y) (sub_nat_to_imported x))
      (dm_not_dvd_canonical x y HdvdR)
      Lean.Nat
      (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
      (dm_imported_add
        (dm_imported_div (sub_nat_to_imported x) (sub_nat_to_imported y))
        dm_imported_one).
    exact (sub_imported_eq_trans _ _ _ Hbody
      (sub_imported_eq_trans _ _ _ Hif (dm_div_succ_canonical x y))).
Qed.

Lemma dm_div_ceil_correspondence xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel
    (if yR %| xR then xR %/ yR else (xR %/ yR).+1)
    (dm_imported_div_ceil xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (dm_div_ceil_canonical xR yR))
    (sub_imported_eq_congr2 dm_imported_div_ceil _ _ _ _ Hx Hy)).
Qed.

(** The imported target uses propositional [ite] for [Nat] order, whereas
    MathComp computes the corresponding branch with a Boolean test.  Keep
    the negative transport at top level: eliminating an imported [SProp]
    directly inside a local proof would violate Rocq's SProp restriction. *)
Definition dm_not_le_related (aR : nat) (aL : Lean.Nat)
    (bR : nat) (bL : Lean.Nat)
    (Ha : SubNatRel aR aL) (Hb : SubNatRel bR bL)
    (Hfalse : Logic.eq (leq aR bR) false) :
    I.Not (dm_imported_le aL bL) :=
  fun HleL =>
    dm_coq_false_to_target
      (dm_bool_false_no_truth (leq aR bR) Hfalse
        (sprop_to_prop _ _
          (dm_le_correspondence aR aL bR bL Ha Hb) HleL)).

Lemma dm_mod_elim_rhs_canonical (a b c : nat) :
  Lean.eq
    (I.ite Lean.Nat
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)))
    (sub_nat_to_imported
      (if leq b (a %% c) then a %% c - b else a %% c + c - b)).
Proof.
  destruct (leq b (a %% c)) eqn:HleR.
  - have HleR' : is_true (leq b (a %% c)) by rewrite HleR.
    have HleL := prop_to_sprop _ _
      (dm_le_correspondence b (sub_nat_to_imported b)
        (a %% c)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_rel_canonical b)
        (dm_mod_correspondence a (sub_nat_to_imported a)
          c (sub_nat_to_imported c)
          (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))) HleR'.
    have Hif := I.if_pos
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      HleL Lean.Nat
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)).
    exact (sub_imported_eq_trans _ _ _ Hif
      (sub_imported_eq_sym _ _
        (dm_sub_correspondence (a %% c)
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          b (sub_nat_to_imported b)
          (dm_mod_correspondence a (sub_nat_to_imported a)
            c (sub_nat_to_imported c)
            (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))
          (sub_nat_rel_canonical b)))).
  - have Hif := I.if_neg
      (dm_imported_le (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (I.Nat_decLe (sub_nat_to_imported b)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c)))
      (dm_not_le_related b (sub_nat_to_imported b)
        (a %% c)
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_rel_canonical b)
        (dm_mod_correspondence a (sub_nat_to_imported a)
          c (sub_nat_to_imported c)
          (sub_nat_rel_canonical a) (sub_nat_rel_canonical c)) HleR)
      Lean.Nat
      (dm_imported_sub
        (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
        (sub_nat_to_imported b))
      (dm_imported_sub
        (dm_imported_add
          (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
          (sub_nat_to_imported c))
        (sub_nat_to_imported b)).
    exact (sub_imported_eq_trans _ _ _ Hif
      (sub_imported_eq_sym _ _
        (dm_sub_correspondence (a %% c + c)
          (dm_imported_add
            (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
            (sub_nat_to_imported c))
          b (sub_nat_to_imported b)
          (dm_add_correspondence (a %% c)
            (dm_imported_mod (sub_nat_to_imported a) (sub_nat_to_imported c))
            c (sub_nat_to_imported c)
            (dm_mod_correspondence a (sub_nat_to_imported a)
              c (sub_nat_to_imported c)
              (sub_nat_rel_canonical a) (sub_nat_rel_canonical c))
            (sub_nat_rel_canonical c))
          (sub_nat_rel_canonical b)))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Options, pairs and the response-time iteration *)

Lemma cso_ite_bool (A : Type) bR bL (Hb : CtBoolRel bR bL) (a b : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) a b) (if bR then a else b).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: bR. Qed.

Lemma cso_ite_dec (A : Type) (P : SProp) (dec : I.Decidable P) bR (Hb : CtBoolRel bR (I.Decidable_decide P dec)) (a b : A) :
  Logic.eq (I.ite A P dec a b) (if bR then a else b).
Proof.
  have E := ct_bool_rel_logic _ _ Hb. clear Hb. move: E.
  case: dec => [h|h] E; destruct bR; try reflexivity; discriminate E.
Qed.

Definition cso_onat (o : option nat) : I.Option_inst1 Lean.Nat :=
  match o with Some n => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported n) | None => I.Option_none_inst1 Lean.Nat end.

Lemma cso_iter_canonical fR fL (Hf : forall a aL, SubNatRel a aL -> SubNatRel (fR a) (fL aL)) : forall n x,
  Logic.eq (cso_onat (iter_fixpoint fR n x))
    (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_inst1 Lean.Nat I.instDecidableEqNat fL (sub_nat_to_imported n) (sub_nat_to_imported x)).
Proof.
  elim => [|n IH] x; first reflexivity.
  have E := cl_nat_logic _ _ (Hf x _ (sub_nat_rel_canonical x)).
  have -> : Logic.eq (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_inst1 Lean.Nat I.instDecidableEqNat fL (sub_nat_to_imported n.+1) (sub_nat_to_imported x))
      (match I.Decidable_decide (Lean.eq (sub_nat_to_imported x) (fL (sub_nat_to_imported x)))
               (I.instDecidableEqNat (sub_nat_to_imported x) (fL (sub_nat_to_imported x))) with
       | I.Bool_true => I.Option_some_inst1 Lean.Nat (sub_nat_to_imported x)
       | I.Bool_false => I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_inst1 Lean.Nat I.instDecidableEqNat fL (sub_nat_to_imported n) (fL (sub_nat_to_imported x)) end).
  { cbn. destruct (I.instDecidableEqNat (sub_nat_to_imported x) (fL (sub_nat_to_imported x))); reflexivity. }
  rewrite E (ct_bool_rel_logic _ _ (ct_decide_eq_nat _ _ _ _ (sub_nat_rel_canonical x) (sub_nat_rel_canonical (fR x)))) -IH /=.
  by case: (x == fR x).
Qed.

Lemma cso_iter fR fL (Hf : forall a aL, SubNatRel a aL -> SubNatRel (fR a) (fL aL)) nR nL (Hn : SubNatRel nR nL) xR xL (Hx : SubNatRel xR xL) :
  Logic.eq (cso_onat (iter_fixpoint fR nR xR)) (I.Prosa_Classic_Util_Fixedpoint_iter_fixpoint_inst1 Lean.Nat I.instDecidableEqNat fL nL xL).
Proof. rewrite (cl_nat_logic _ _ Hn) (cl_nat_logic _ _ Hx). exact (cso_iter_canonical fR fL Hf nR xR). Qed.

Section Pairs.
Variable Task : eqType.
Notation PT := (I.Prod_inst2 Task Lean.Nat).
Notation PO := (I.Prod_inst2 Task (I.Option_inst1 Lean.Nat)).

Definition cso_pair (p : Task * nat) : PT := I.Prod_mk_inst2 Task Lean.Nat p.1 (sub_nat_to_imported p.2).
Definition cso_unpair (q : PT) : Task * nat := match q with I.Prod_mk_inst2 a b => (a, sub_nat_to_rocq b) end.
Lemma cso_unpair_pair p : Logic.eq (cso_unpair (cso_pair p)) p.
Proof. case: p => a b. rewrite /cso_unpair /cso_pair /=. by rewrite sub_nat_rocq_roundtrip. Qed.
Lemma cso_pair_unpair q : Logic.eq (cso_pair (cso_unpair q)) q.
Proof. case: q => a b. rewrite /cso_unpair /cso_pair /=. by rewrite (imported_eq_to_coq_eq _ _ (sub_nat_imported_roundtrip b)). Qed.
Definition cso_pairo (p : Task * option nat) : PO := I.Prod_mk_inst2 Task (I.Option_inst1 Lean.Nat) p.1 (cso_onat p.2).
Definition cso_opair (o : option (Task * nat)) : I.Option PT := match o with Some p => I.Option_some PT (cso_pair p) | None => I.Option_none PT end.
Definition cso_olist (o : option (seq (Task * nat))) : I.Option (I.List PT) :=
  match o with Some l => I.Option_some (I.List PT) (cl_map cso_pair l) | None => I.Option_none (I.List PT) end.

Lemma cso_all_step (P : PO -> I.Bool) a l : Logic.eq (I.List_all PO (I.List_cons PO a l) P) (I.Bool_and (P a) (I.List_all PO l P)).
Proof. reflexivity. Qed.

Lemma cso_filterMap_step (f : PO -> I.Option PT) a l :
  Logic.eq (I.List_filterMap PO PT f (I.List_cons PO a l))
    (match f a with I.Option_none => I.List_filterMap PO PT f l | I.Option_some b => I.List_cons PT b (I.List_filterMap PO PT f l) end).
Proof. reflexivity. Qed.

Lemma cso_all_pmap (vR : Task * option nat -> option (Task * nat)) (vL : PO -> I.Option PT)
    (Hv : forall p, Logic.eq (cso_opair (vR p)) (vL (cso_pairo p))) s :
  Logic.eq (cso_olist (if all (fun p => isSome (vR p)) s then Some (pmap vR s) else None))
    (I.ite (I.Option (I.List PT))
       (Lean.eq (I.List_all PO (cl_map cso_pairo s) (fun p => I.Option_isSome PT (vL p))) I.Bool_true)
       (I.instDecidableEqBool (I.List_all PO (cl_map cso_pairo s) (fun p => I.Option_isSome PT (vL p))) I.Bool_true)
       (I.Option_some (I.List PT) (I.List_filterMap PO PT vL (cl_map cso_pairo s)))
       (I.Option_none (I.List PT))).
Proof.
  have Eall : Logic.eq (I.List_all PO (cl_map cso_pairo s) (fun p => I.Option_isSome PT (vL p))) (ct_b2l (all (fun p => isSome (vR p)) s)).
  { elim: s => [|x s IH]; first reflexivity.
    rewrite [cl_map _ _]/= [all _ (_ :: _)]/= cso_all_step IH -(Hv x). case: (vR x) => [p|]; reflexivity. }
  have Epm : Logic.eq (I.List_filterMap PO PT vL (cl_map cso_pairo s)) (cl_map cso_pair (pmap vR s)).
  { clear Eall. elim: s => [|x s IH]; first reflexivity.
    rewrite [cl_map cso_pairo _]/= [pmap _ (_ :: _)]/= cso_filterMap_step IH -(Hv x). case: (vR x) => [p|]; reflexivity. }
  rewrite Eall Epm. by case: (all _ s).
Qed.

Lemma cso_cl_map_pair_inj (s1 s2 : seq (Task * nat)) : Logic.eq (cl_map cso_pair s1) (cl_map cso_pair s2) -> Logic.eq s1 s2.
Proof.
  intro E. have E' := f_equal (cl_unmap cso_unpair) E.
  by rewrite !(cl_unmap_map cso_pair cso_unpair cso_unpair_pair) in E'.
Qed.

Lemma cso_fcb_eq oR oL (Ho : Logic.eq (cso_olist oR) oL) rbR rbL (Hrb : ClListRel cso_pair rbR rbL) :
  PropSPropRel (Logic.eq oR (Some rbR)) (Lean.eq oL (I.Option_some (I.List PT) rbL)).
Proof.
  subst oL. rewrite (cl_list_logic _ _ _ Hrb). apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E. clear E.
    case: oR E' => [l|] /= E'; last discriminate E'.
    injection E' => E''. by rewrite (cso_cl_map_pair_inj _ _ E'').
Qed.

Lemma cso_mem_pair tsk RR RL (HR : SubNatRel RR RL) rbR rbL (Hrb : ClListRel cso_pair rbR rbL) :
  PropSPropRel ((tsk, RR) \in rbR) (I.List_Mem PT (I.Prod_mk_inst2 Task Lean.Nat tsk RL) rbL).
Proof. destruct HR. exact (cl_mem_rel_list _ _ cso_pair cso_unpair cso_unpair_pair (tsk, RR) _ _ Hrb). Qed.

Lemma cso_forall_bounds (PR : seq (Task * nat) -> Prop) (PL : I.List PT -> SProp) :
  (forall sR sL, ClListRel cso_pair sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cl_forall_list cso_pair cso_unpair cso_pair_unpair PR PL). Qed.

End Pairs.

Lemma cso_onat_eq oR oL (Ho : Logic.eq (cso_onat oR) oL) RR RL (HR : SubNatRel RR RL) :
  PropSPropRel (Logic.eq oR (Some RR)) (Lean.eq oL (I.Option_some_inst1 Lean.Nat RL)).
Proof.
  subst oL. rewrite (cl_nat_logic _ _ HR). apply prop_sprop_rel_intro.
  - intros ->. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. have E' := imported_eq_to_coq_eq _ _ E. clear E.
    case: oR E' => [x|] /= E'; last discriminate E'.
    injection E' => E''. have := f_equal sub_nat_to_rocq E''. by rewrite !sub_nat_rocq_roundtrip => ->.
Qed.

(* ------------------------------------------------------------------ *)
(** * Inflated costs *)

Lemma cso_OR_inflated_task_cost (Task : eqType) cR cL (Hc : CsoParRel Task cR cL) bR bL (Hb : CsoParRel Task bR bL) :
  CsoParRel Task (@ReductionToBasicSchedule.inflated_task_cost Task cR bR) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Oblivious_Reduction_ReductionToBasicSchedule_inflated_task_cost Task (ct_decidable_eq Task) cL bL).
Proof. intro x. exact (sub_add_correspondence _ _ _ _ (Hc x) (Hb x)). Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section ORDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat).
Hypothesis Hja : CsoParRel Job jaR jaL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CsoArrRel Job aR aL.
Variables (hR : nat -> Job -> Job -> bool) (hL : Lean.Nat -> Job -> Job -> I.Bool).
Hypothesis Hh : CsoJldpRel Job hR hL.
Variables (ssR : UniprocessorSchedule.schedule Job) (ssL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hss : CsoSchedRel Job ssR ssL.
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CsoSuspRel Job nR nL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CsoParRel Job cR cL.

Lemma cso_empty : CsoSchedRel Job (fun _ => None) (fun _ => I.Option_none Job).
Proof. intros tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

End ORDefs.

Lemma cso_itc_pt (Task : eqType) cR cL (Hc : CsoParRel Task cR cL) bR bL (Hb : CsoParRel Task bR bL) x :
  SubNatRel (@ReductionToBasicSchedule.inflated_task_cost Task cR bR x) (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Oblivious_Reduction_ReductionToBasicSchedule_inflated_task_cost Task (ct_decidable_eq Task) cL bL x).
Proof. exact (cso_OR_inflated_task_cost Task cR cL Hc bR bL Hb x). Qed.

(* ------------------------------------------------------------------ *)
(** * The FP workload bound (as in the accepted classic uni workload_bound_fp certificate) *)

Section FPCWDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

Lemma cso_W_max_jobs pR pL (Hp : CsoParRel Task pR pL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundFP.max_jobs pR tsk dR) (I.Prosa_Classic_Analysis_Uni_Basic_WorkloadBoundFp_WorkloadBoundFP_max_jobs Task dT pL tsk dL).
Proof. exact (dm_div_ceil_correspondence _ _ _ _ Hd (Hp tsk)). Qed.

Lemma cso_W_task_workload_bound_FP cR cL (Hc : CsoParRel Task cR cL) pR pL (Hp : CsoParRel Task pR pL)
    tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundFP.task_workload_bound_FP cR pR tsk dR) (I.Prosa_Classic_Analysis_Uni_Basic_WorkloadBoundFp_WorkloadBoundFP_task_workload_bound_FP Task dT cL pL tsk dL).
Proof. exact (sub_mul_correspondence _ _ _ _ (cso_W_max_jobs pR pL Hp tsk dR dL Hd) (Hc tsk)). Qed.

Lemma cso_W_total_workload_bound_fp cR cL (Hc : CsoParRel Task cR cL) pR pL (Hp : CsoParRel Task pR pL)
    hR hL (Hh : CsoRelRel Task hR hL) tsR tsL (Hts : ClListRel cid tsR tsL) tsk dR dL (Hd : SubNatRel dR dL) :
  SubNatRel (WorkloadBoundFP.total_workload_bound_fp cR pR hR tsR tsk dR) (I.Prosa_Classic_Analysis_Uni_Basic_WorkloadBoundFp_WorkloadBoundFP_total_workload_bound_fp Task dT cL pL hL tsL tsk dL).
Proof.
  exact (cso_sum_filtered_rel Task _ _ (fun x => cso_W_task_workload_bound_FP cR cL Hc pR pL Hp x dR dL Hd)
           _ _ (fun x => Hh x tsk) _ _ Hts).
Qed.

End FPCWDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section FPCDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tcR tpR tdR : Task -> nat) (tcL tpL tdL : Task -> Lean.Nat).
Hypotheses (Htc : CsoParRel Task tcR tcL) (Htp : CsoParRel Task tpR tpL) (Htd : CsoParRel Task tdR tdL).
Variables (hR : Task -> Task -> bool) (hL : Task -> Task -> I.Bool).
Hypothesis Hh : CsoRelRel Task hR hL.

Lemma cso_FPC_max_steps tsk :
  SubNatRel (@ResponseTimeIterationFP.max_steps Task tcR tdR tsk) (I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_max_steps Task dT tcL tdL tsk).
Proof. exact (sub_add_correspondence _ _ _ _ (ct_sub_rel _ _ _ _ (Htd tsk) (Htc tsk)) (sub_nat_rel_canonical 1)). Qed.

Lemma cso_FPC_per_task_rta tsR tsL (Hts : ClListRel cid tsR tsL) tsk :
  Logic.eq (cso_onat (@ResponseTimeIterationFP.per_task_rta Task tcR tpR tdR hR tsR tsk)) (I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_per_task_rta Task dT tcL tpL tdL hL tsL tsk).
Proof.
  rewrite /ResponseTimeIterationFP.per_task_rta. unfold I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_per_task_rta.
  exact (cso_iter _ _ (fun a aL Ha => cso_W_total_workload_bound_fp Task tcR tcL Htc tpR tpL Htp hR hL Hh tsR tsL Hts tsk a aL Ha)
           _ _ (cso_FPC_max_steps tsk) _ _ (Htc tsk)).
Qed.

Lemma cso_FPC_fp_claimed_bounds tsR tsL (Hts : ClListRel cid tsR tsL) :
  Logic.eq (cso_olist Task (@ResponseTimeIterationFP.fp_claimed_bounds Task tcR tpR tdR hR tsR)) (I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds Task dT tcL tpL tdL hL tsL).
Proof.
  rewrite /ResponseTimeIterationFP.fp_claimed_bounds. unfold I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_fp_claimed_bounds. cbv zeta.
  rewrite (cl_list_logic _ _ _ Hts).
  rewrite -(cl_map_op cid (cso_pairo Task) (fun tsk => (tsk, @ResponseTimeIterationFP.per_task_rta Task tcR tpR tdR hR tsR tsk))
              (fun tsk => I.Prod_mk_inst2 Task (I.Option_inst1 Lean.Nat) tsk (I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_per_task_rta Task dT tcL tpL tdL hL (cl_map cid tsR) tsk))
              (fun tsk => _) tsR).
  - intro tsk. rewrite /cso_pairo /= -(cso_FPC_per_task_rta _ _ (@Lean.eq_refl _ _) tsk). reflexivity.
  - apply: cso_all_pmap => - [tsk [R|]]; last reflexivity.
    cbv beta iota zeta. rewrite [cso_pairo _ _]/cso_pairo [cso_onat _]/cso_onat. unfold I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_is_valid_bound.
    rewrite [I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_is_valid_bound_match_1 _ _ _ _ _]/=.
    rewrite (cso_ite_dec _ _ _ _ (ct_decide_le _ _ _ _ (sub_nat_rel_canonical R) (Htd tsk))).
    by case: (_ <= _).
Qed.

Notation FCB := cso_FPC_fp_claimed_bounds.

Lemma cso_FPC_fp_schedulable tsR tsL (Hts : ClListRel cid tsR tsL) :
  CtBoolRel (@ResponseTimeIterationFP.fp_schedulable Task tcR tpR tdR hR tsR) (I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_fp_schedulable Task dT tcL tpL tdL hL tsL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /ResponseTimeIterationFP.fp_schedulable. unfold I.Prosa_Classic_Analysis_Uni_Basic_FpRtaComp_ResponseTimeIterationFP_fp_schedulable.
  rewrite -(FCB tsR tsL Hts). by case: (@ResponseTimeIterationFP.fp_claimed_bounds Task tcR tpR tdR hR tsR).
Qed.

End FPCDefs.

Notation FCB := cso_FPC_fp_claimed_bounds.
Notation PTR := cso_FPC_per_task_rta.
Notation FS := cso_FPC_fp_schedulable.
Notation TWc := cso_W_total_workload_bound_fp.

(** Schedulability (as in the accepted classic uniprocessor schedulability certificate). *)
Section FPCSched.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsoSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (dR : Job -> nat) (dL : Job -> Lean.Nat).
Hypotheses (Ha : CsoParRel Job aR aL) (Hc : CsoParRel Job cR cL) (Hd : CsoParRel Job dR dL).
Lemma cso_job_misses_no_deadline j :
  PropSPropRel (Schedulability.job_misses_no_deadline aR cR dR sR j)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedulability_Schedulability_job_misses_no_deadline Job dJ aL cL dL sL j).
Proof. exact (ct_bool_truth _ _ (cso_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) (Hd j)))). Qed.
Lemma cso_task_misses_no_deadline (job_task : Job -> Task) arrR arrL (Harr : CsoArrRel Job arrR arrL) tsk :
  PropSPropRel (Schedulability.task_misses_no_deadline aR cR dR job_task arrR sR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedulability_Schedulability_task_misses_no_deadline Job dJ aL cL dL Task dT job_task arrL sL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (cso_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (cso_job_misses_no_deadline j).
Qed.

End FPCSched.

(** Task sets ([taskset_of Task], the accepted sequence-set type), related through their underlying sequences
    elementwise by identity, with two-way totals (as in the accepted classic constrained-deadlines certificates). *)
Section FPCTs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation LTs := (I.Prosa_Classic_Model_Arrival_Basic_Task_SporadicTaskset_taskset_of Task dT).
Notation LVal := (I.Prosa_Util_Seqset_set_val Task dT).

Definition CsoTsRel (tsR : SporadicTaskset.taskset_of Task) (tsL : LTs) : SProp :=
  ClListRel cid (@prosa.util.seqset._set_seq _ tsR) (LVal tsL).

Lemma cso_ts_id (x : Task) : Logic.eq x x.
Proof. reflexivity. Qed.

Definition cso_ts_to_target (tsR : SporadicTaskset.taskset_of Task) : LTs :=
  I.Prosa_Util_Seqset_set_mk Task dT (cl_map cid (@prosa.util.seqset._set_seq _ tsR))
    (prop_to_sprop _ _ (cl_uniq_rel _ _ cid cid cso_ts_id cso_ts_id _) (@prosa.util.seqset.set_uniq _ tsR)).

Definition cso_ts_to_source (tsL : LTs) : SporadicTaskset.taskset_of Task :=
  @prosa.util.seqset.Build_set _ (cl_unmap cid (LVal tsL))
    (interpret_strict _ (cl_uniq_backward _ _ cid cid cso_ts_id _ (@I.nodup Task dT tsL))).

Lemma cso_ts_canonical tsR : CsoTsRel tsR (cso_ts_to_target tsR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma cso_ts_surjective tsL : CsoTsRel (cso_ts_to_source tsL) tsL.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid cso_ts_id _). Qed.

Lemma cso_forall_ts (PR : SporadicTaskset.taskset_of Task -> Prop) (PL : LTs -> SProp) :
  (forall tsR tsL, CsoTsRel tsR tsL -> PropSPropRel (PR tsR) (PL tsL)) -> PropSPropRel (forall ts, PR ts) (forall ts, PL ts).
Proof. exact (cso_forall_cover _ _ CsoTsRel cso_ts_to_target cso_ts_to_source cso_ts_canonical cso_ts_surjective PR PL). Qed.

Lemma cso_ts_mem tsR tsL (Hts : CsoTsRel tsR tsL) x :
  PropSPropRel (x \in tsR) (I.Membership_mem Task LTs (I.Prosa_Util_Seqset_instMembershipSet Task dT) tsL x).
Proof. exact (cl_mem_rel_list _ _ cid cid cso_ts_id x _ _ Hts). Qed.

End FPCTs.

(* ------------------------------------------------------------------ *)
(** * Statement relation search

    [crel] proves a [PropSPropRel P PL] (and the [SubNatRel], [CtBoolRel], [ClListRel] and relation goals it
    generates) by the structure of the source side [P], as in the accepted classic case-study certificates: each
    binder by the cover lemma of its type's relation, each connective by its [LogicalRelation]/base lemma, and
    each atom by the correspondence lemma of its head (above), whose remaining relation premises are hypotheses
    introduced by the binders.  It only chains lemmas proved in this file or its imports; a goal it cannot close
    makes the proof fail. *)

Ltac crel_hyp :=
  match goal with
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CsoParRel _ f g |- _ => exact (H x) end
  | |- CtBoolRel (?f ?x ?y) (?g ?x ?y) => match goal with H : CsoRelRel _ f g |- _ => exact (H x y) end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (cso_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (cso_forall_sched _); intros ? ? ?
  | Priority.FP_policy _ => apply: (cso_forall_rel _); intros ? ? ?
  | SporadicTaskset.taskset_of _ => apply: (cso_forall_ts _); intros ? ? ?
  | seq _ => apply: (cso_forall_list _); intros ? ? ?
  | Suspension.job_suspension _ => apply: (cso_forall_susp _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: cso_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CsoParRel _ (ReductionToBasicSchedule.inflated_task_cost _ _) _ => eapply cso_OR_inflated_task_cost; crel
    | |- CsoParRel _ (ReductionToBasicSchedule.inflated_job_cost _ _) _ => fail; crel
    | |- ClListRel _ (prosa.util.seqset._set_seq ?t) _ => match goal with H : CsoTsRel _ t _ |- _ => exact H end
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => eapply ct_sub_rel; crel
  | S _ => eapply cso_succ_rel; crel
  | _ => first [ exact (sub_nat_rel_canonical _) | crel_n_defs ]
  end
with crel_b b :=
  lazymatch b with
  | andb _ _ => eapply ct_bool_and; crel
  | negb _ => eapply ct_bool_not; crel
  | leq _ _ => first [ eapply ct_decide_lt; crel | eapply ct_decide_le; crel ]
  | @eq_op ?T _ _ => first [ eapply ct_decide_eq_nat; crel | eapply ct_decide_eq; crel ]
  | _ => crel_b_defs
  end
with crel_l l := crel_l_defs
with crel_p P :=
  lazymatch P with
  | forall x : ?T, _ => lazymatch type of T with Prop => eapply ct_imp; crel | _ => crel_intro T; crel end
  | exists x : ?T, _ =>
      tryif crel_isnat T then (apply: ct_exists_nat; intros ? ? ?; crel)
      else (apply: ct_exists_identity; intro; crel)
  | _ /\ _ => eapply ct_and; crel
  | _ <-> _ => eapply cso_iff; crel
  | _ <> _ => eapply cso_ne
  | ~ _ => eapply ct_imp; [crel | exact cso_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | eapply cso_opt_rel_eq; crel ]
with crel_n_defs := first [ eapply ct_bool_to_nat; crel
    | eapply cso_itc_pt; crel
    | eapply cso_US_service; crel
    | eapply cso_US_service_during; crel
    | eapply cso_US_service_at; crel ]
with crel_b_defs := first [ eapply cso_FPC_fp_schedulable; crel
    | eapply cso_US_scheduled_at; crel
    | eapply cso_US_completed_by; crel
    | eapply cso_US_pending; crel
    | eapply cso_has_arrived; crel
    | eapply cso_arrives_at; crel
    | eapply cso_J_job_cost_positive; crel
    | eapply cso_J_job_deadline_positive; crel
    | eapply cso_J_job_cost_le_deadline; crel
    | eapply cso_J_job_cost_le_task_cost; crel ]
with crel_l_defs := first [ fail ]
with crel_p_defs := first [ eapply cso_false_rel; crel
    | eapply cso_SI_respects_self_suspensions; crel
    | eapply cso_TK_valid_sporadic_taskset; crel
    | eapply cso_TK_is_valid_sporadic_task; crel
    | eapply cso_arrives_in; crel
    | eapply cso_consistent; crel
    | eapply cso_is_a_set; crel
    | eapply cso_mem; crel
    | eapply cso_ts_mem; crel
    | eapply cso_US_jobs_come_from_arrival_sequence; crel
    | eapply cso_US_jobs_must_arrive_to_execute; crel
    | eapply cso_US_completed_jobs_dont_execute; crel
    | eapply cso_SP_work_conserving; crel
    | eapply cso_SP_respects_FP_policy; crel
    | eapply cso_PR_FP_is_reflexive; crel
    | eapply cso_PR_FP_is_transitive; crel
    | eapply cso_PR_FP_is_total_over_task_set; crel
    | eapply cso_SU_dynamic_suspension_model; crel
    | eapply cso_J_valid_sporadic_job; crel
    | eapply cso_TA_sporadic_task_model; crel
    | eapply cso_task_misses_no_deadline; crel
    | eapply cso_uniq; crel
    | eapply cso_J_valid_realtime_job; crel
    | eapply cso_J_job_deadline_eq_task_deadline; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_suspension_oblivious_fp_rta_implies_schedulability (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@SuspensionObliviousFP.suspension_oblivious_fp_rta_implies_schedulability Task p0 p1 p2 Job)).
Definition tgt_suspension_oblivious_fp_rta_implies_schedulability (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Dynamic_Oblivious_FpRta_SuspensionObliviousFP_suspension_oblivious_fp_rta_implies_schedulability Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem SuspensionObliviousFP_suspension_oblivious_fp_rta_implies_schedulability_correspondence (Task Job : eqType) :
  PropSPropRel (src_suspension_oblivious_fp_rta_implies_schedulability Task Job) (tgt_suspension_oblivious_fp_rta_implies_schedulability Task Job).
Proof. unfold src_suspension_oblivious_fp_rta_implies_schedulability, tgt_suspension_oblivious_fp_rta_implies_schedulability. crel_spine. crel. Unshelve. all: crel. Qed.
