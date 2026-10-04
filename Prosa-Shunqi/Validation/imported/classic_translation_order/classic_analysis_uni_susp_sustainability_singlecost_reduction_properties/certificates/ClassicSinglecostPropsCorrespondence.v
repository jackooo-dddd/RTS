From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.util.minmax classic.model.suspension classic.model.priority classic.model.arrival.basic.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.susp.last_execution classic.model.schedule.uni.susp.suspension_intervals classic.model.schedule.uni.transformation.construction classic.analysis.uni.susp.sustainability.singlecost.reduction classic.model.schedule.uni.response_time classic.model.schedule.uni.susp.schedule classic.model.schedule.uni.susp.platform classic.analysis.uni.susp.sustainability.singlecost.reduction_properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicSinglecostProps.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicSinglecostPropsBase ClassicSinglecostPropsList ClassicSinglecostPropsOrd.



Module I := ImportedClassicSinglecostProps.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/susp/sustainability/singlecost/reduction_properties.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma csp_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma csp_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma csp_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) csp_false_rel). Qed.

Lemma csp_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma csp_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma csp_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma csp_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma csp_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (csp_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => csp_unmap_rel T l) PR PL).
Qed.

Definition CspParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma csp_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CspParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (csp_forall_cover _ _ (CspParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint csp_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (csp_natl s') end.

Definition csp_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma csp_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) csp_one) (csp_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) csp_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (csp_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma csp_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (csp_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (csp_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma csp_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma csp_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma csp_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma csp_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH csp_cl_append. reflexivity.
Qed.

Lemma csp_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CspFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

Lemma csp_bigcat_rel (A : Type) fR fL (Hf : CspFamRel A fR fL) mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ClListRel cid (\big[cat/[::]]_(mR <= t < nR) fR t) (I.Prosa_Util_Notation_bigCat A mL nL fL).
Proof.
  intros Hm Hn. have E1 := cl_nat_logic _ _ Hm. have E2 := cl_nat_logic _ _ Hn. subst mL nL.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicSinglecostPropsInterface_bigCat_range'
             A (sub_nat_to_imported mR) (sub_nat_to_imported nR) fL)).
  have Hd : Logic.eq (I.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHSub_inst1 Lean.Nat I.instSubNat)
                       (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR)) :=
    ct_sub_canonical nR mR.
  rewrite Hd.
  change (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0)) with (sub_nat_to_imported 0).
  rewrite (csp_iota_range (nR - mR) 0) csp_map_natl. cbv beta.
  have Hpt : forall k, Logic.eq
      (fL (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
             (sub_nat_to_imported mR) (sub_nat_to_imported k)))
      (cl_map cid (fR (mR + k))).
  { intro k. exact (cl_list_logic _ _ _ (Hf _ _ (sub_add_correspondence mR _ k _
       (sub_nat_rel_canonical mR) (sub_nat_rel_canonical k)))). }
  rewrite (csp_cl_map_ext _ _ Hpt) (csp_cl_map_comp (fun k => fR (mR + k)) (cl_map cid)) csp_flatten.
  have Hi : Logic.eq (iota mR (nR - mR)) (map (addn mR) (iota 0 (nR - mR))) by rewrite -iotaDl addn0.
  rewrite csp_big_seq /index_iota Hi -map_comp.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CspArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition csp_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition csp_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma csp_arr_canonical aR : CspArrRel aR (csp_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /csp_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma csp_arr_surjective aL : CspArrRel (csp_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma csp_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CspArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (csp_forall_cover _ _ CspArrRel csp_arr_to_target csp_arr_to_source csp_arr_canonical csp_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma csp_jobs_arrived_between aR aL (Ha : CspArrRel Job aR aL) t1R t1L t2R t2L
    (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :
  ClListRel cid (ArrivalSequence.jobs_arrived_between aR t1R t2R)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_between Job dJ aL t1L t2L).
Proof. exact (csp_bigcat_rel Job (fun t => aR t) (fun t => aL t) Ha t1R t1L t2R t2L H1 H2). Qed.

Lemma csp_arrives_in aR aL (Ha : CspArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (csp_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma csp_consistent pR pL (Hp : CspParRel Job pR pL) aR aL (Ha : CspArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (csp_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma csp_jobs_arrived_up_to aR aL (Ha : CspArrRel Job aR aL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (ArrivalSequence.jobs_arrived_up_to aR tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_jobs_arrived_up_to Job dJ aL tL).
Proof. exact (csp_jobs_arrived_between Job aR aL Ha 0 _ tR.+1 _ (sub_nat_rel_canonical 0) (csp_succ_rel tR tL Ht)). Qed.

Lemma csp_arrives_at aR aL (Ha : CspArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (csp_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma csp_has_arrived pR pL (Hp : CspParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint csp_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (csp_snatl s') end.

Lemma csp_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (csp_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (csp_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma csp_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (csp_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (csp_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma csp_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CspFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma csp_fun_canonical FR FL (HF : CspFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma csp_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma csp_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CspFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := csp_nat_sub_canonical nR mR.
  rewrite csp_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (csp_foldr_add FL FR (csp_fun_canonical FR FL HF)).
  by rewrite csp_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition csp_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition csp_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma csp_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma csp_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (csp_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CspSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition csp_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition csp_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma csp_sched_canonical sR : CspSchedRel sR (csp_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /csp_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma csp_sched_surjective sL : CspSchedRel (csp_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /csp_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma csp_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CspSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (csp_forall_cover _ _ CspSchedRel csp_sched_to_target csp_sched_to_source csp_sched_canonical csp_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma csp_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CspSchedRel Job sR (csp_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CspSchedRel Job (csp_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (csp_sched_canonical Job) (csp_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CspSchedRel Job sR sL.

Lemma csp_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (csp_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (csp_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma csp_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (csp_US_scheduled_at j tR tL Ht)). Qed.

Lemma csp_service_at_fun j : CspFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (csp_US_service_at j kR kL Hk). Qed.

Lemma csp_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (csp_ico _ _ _ _ _ _ H1 H2 (csp_service_at_fun j)). Qed.

Lemma csp_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (csp_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma csp_US_completed_by cR cL (Hc : CspParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (csp_US_service j tR tL Ht)). Qed.

Lemma csp_US_pending aR aL (Ha : CspParRel Job aR aL) cR cL (Hc : CspParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (csp_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (csp_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma csp_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CspArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csp_US_scheduled_at j tR tL Ht)).
  exact (csp_arrives_in Job arrR arrL Harr j).
Qed.

Lemma csp_US_jobs_must_arrive_to_execute aR aL (Ha : CspParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csp_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (csp_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma csp_US_completed_jobs_dont_execute cR cL (Hc : CspParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (csp_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** * [\max] over ordinals against [maxFiltered] over [List.finRange] *)

Lemma csp_foldr_max (f : Lean.Nat -> Lean.Nat) (g : nat -> nat)
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

Lemma csp_max_rel nR nL (Hn : SubNatRel nR nL) (QR : 'I_nR -> bool) (QL : Fin nL -> I.Bool) (HQ : CoOrdPredRel nR nL QR QL) :
  SubNatRel (\max_(i < nR | QR i) nat_of_ord i)
    (I.Prosa_Util_Sum_maxFiltered_inst1 (Fin nL) (I.List_finRange nL) QL (fun o => I.Fin_val nL o)).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicSinglecostPropsInterface_maxFiltered_finRange
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
  exact (csp_foldr_max _ _ (co_fam_related nR sub_nat_to_imported (fun i => if QR i then nat_of_ord i else 0)
           (fun oL => I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0)) 0 HF) (iota 0 nR)).
Qed.

Lemma csp_ite_rel bR bL (Hb : CtBoolRel bR bL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR)
    (I.ite Lean.Nat (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) xL yL).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). destruct bR; [exact Hx | exact Hy]. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma csp_LE_time_after_last_execution (Job : eqType) aR aL (Ha : CspParRel Job aR aL)
    sR sL (Hs : CspSchedRel Job sR sL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (LastExecution.time_after_last_execution aR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_LastExecution_LastExecution_time_after_last_execution Job (ct_decidable_eq Job) aL sL j tL).
Proof.
  assert (HQ : CoOrdPredRel tR tL (fun o => UniprocessorSchedule.scheduled_at sR j o)
      (fun oL => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job (ct_decidable_eq Job) sL j (I.Fin_val tL oL))).
  { intros o oL Ho. exact (csp_US_scheduled_at Job sR sL Hs j _ _ Ho). }
  exact (csp_ite_rel _ _ (co_exists_rel tR tL Ht _ _ HQ) _ _
           (sub_add_correspondence _ _ _ _ (csp_max_rel tR tL Ht _ _ HQ) (sub_nat_rel_canonical 1)) _ _ (Ha j)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Section SuspSusp.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSusp := (I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).

Definition CspSuspRel (sR : Suspension.job_suspension Job) (sL : LSusp) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (sR j tR) (sL j tL).

Definition csp_susp_to_target (sR : Suspension.job_suspension Job) : LSusp :=
  fun j tL => sub_nat_to_imported (sR j (sub_nat_to_rocq tL)).

Definition csp_susp_to_source (sL : LSusp) : Suspension.job_suspension Job :=
  fun j tR => sub_nat_to_rocq (sL j (sub_nat_to_imported tR)).

Lemma csp_susp_canonical sR : CspSuspRel sR (csp_susp_to_target sR).
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  unfold csp_susp_to_target. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma csp_susp_surjective sL : CspSuspRel (csp_susp_to_source sL) sL.
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma csp_forall_susp (PR : Suspension.job_suspension Job -> Prop) (PL : LSusp -> SProp) :
  (forall sR sL, CspSuspRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (csp_forall_cover _ _ CspSuspRel csp_susp_to_target csp_susp_to_source csp_susp_canonical csp_susp_surjective PR PL). Qed.

End SuspSusp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma csp_SU_job_suspension (Job : eqType) :
  And (forall sR : Suspension.job_suspension Job, CspSuspRel Job sR (csp_susp_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job (ct_decidable_eq Job), CspSuspRel Job (csp_susp_to_source Job sL) sL).
Proof. exact (And_intro _ _ (csp_susp_canonical Job) (csp_susp_surjective Job)). Qed.

Section SuspintDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CspSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CspParRel Job aR aL) (Hc : CspParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CspSuspRel Job nR nL.

Notation TALE := (csp_LE_time_after_last_execution Job aR aL Ha sR sL Hs).

Lemma csp_SI_suspension_duration j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (SuspensionIntervals.suspension_duration aR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspension_duration Job dJ aL nL sL j tL).
Proof. exact (Hn j _ _ (csp_US_service Job sR sL Hs j _ _ (TALE j tR tL Ht))). Qed.

Lemma csp_SI_suspended_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (SuspensionIntervals.suspended_at aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_at Job dJ aL cL nL sL j tL).
Proof.
  have HT := TALE j tR tL Ht.
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (csp_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht))
           (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Ht)
              (ct_decide_lt _ _ _ _ Ht (sub_add_correspondence _ _ _ _ HT (csp_SI_suspension_duration j tR tL Ht))))).
Qed.

Lemma csp_SI_respects_self_suspensions :
  PropSPropRel (SuspensionIntervals.respects_self_suspensions aR cR nR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_respects_self_suspensions Job dJ aL cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csp_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (csp_SI_suspended_at j tR tL Ht)) csp_false_rel).
Qed.

End SuspintDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CspRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma csp_rel_canonical (T : Type) (rR : T -> T -> bool) : CspRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma csp_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CspRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma csp_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CspRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (csp_forall_cover _ _ (CspRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (csp_rel_canonical T) (csp_rel_surjective T) PR PL).
Qed.

Definition CspJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CspRelRel T (rR tR) (rL tL).

Lemma csp_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CspJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma csp_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CspJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma csp_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CspJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (csp_forall_cover _ _ (CspJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (csp_jldp_canonical T) (csp_jldp_surjective T) PR PL).
Qed.

(* ------------------------------------------------------------------ *)
(** * [seq_min] (as in the accepted classic minmax certificate) *)

Lemma csp_opt_eq {A} (o1 o2 : option A) : PropSPropRel (Logic.eq o1 o2) (Lean.eq (cl_opt o1) (cl_opt o2)).
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

Lemma csp_argmin_step x l :
  Logic.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (I.List_cons T1 x l))
    (I.Prosa_Classic_Util_Minmax_seq_argmin_match_1 T1 (fun _ => I.Option T1)
       (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL l)
       (fun y => I.ite (I.Option T1) (Lean.eq (relL (FL x) (FL y)) I.Bool_true) (I.instDecidableEqBool (relL (FL x) (FL y)) I.Bool_true)
                   (I.Option_some T1 x) (I.Option_some T1 y))
       (fun _ => I.Option_some T1 x)).
Proof. reflexivity. Qed.

Lemma csp_argmin_rel : forall l,
  Logic.eq (cl_opt (seq_argmin relR FR l)) (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL (cl_map cid l)).
Proof.
  elim => [|x l IH] //=. rewrite csp_argmin_step -IH.
  case: (seq_argmin relR FR l) => [y|] //=.
  rewrite (ct_bool_rel_logic _ _ (Hcomp x y)). by case: (relR (FR x) (FR y)).
Qed.

Lemma csp_argmin_eq l L (H : ClListRel cid l L) o :
  PropSPropRel (Logic.eq (seq_argmin relR FR l) o)
    (Lean.eq (I.Prosa_Classic_Util_Minmax_seq_argmin T1 T2L d1 d2 relL FL L) (cl_opt o)).
Proof. destruct H. rewrite -csp_argmin_rel. exact (csp_opt_eq _ _). Qed.

End MinmaxArg.

Lemma csp_seq_min (T : eqType) relR relL (Hrel : forall a b, CtBoolRel (relR a b) (relL a b)) l :
  Logic.eq (cl_opt (seq_min relR l)) (I.Prosa_Classic_Util_Minmax_seq_min T (ct_decidable_eq T) relL (cl_map cid l)).
Proof. exact (csp_argmin_rel T T T (ct_decidable_eq T) relR relL (@Datatypes.id T) (I.id T) (fun x y => Hrel _ _) l). Qed.

(* ------------------------------------------------------------------ *)
(** * Options *)

Lemma csp_opt_rel_eq (A : Type) (o1 o2 : option A) l1 l2 :
  Lean.eq (cl_opt o1) l1 -> Lean.eq (cl_opt o2) l2 -> PropSPropRel (Logic.eq o1 o2) (Lean.eq l1 l2).
Proof.
  intros H1 H2. destruct H1. destruct H2. apply prop_sprop_rel_intro.
  - intro E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. exact (csp_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Definition csp_lsym {A : Type} {x y : A} (E : Lean.eq x y) : Lean.eq y x :=
  match E in Lean.eq _ z return Lean.eq z x with Lean.eq_refl => @Lean.eq_refl _ _ end.

Lemma csp_src_transport {A : Type} (P : A -> SProp) (x y : A) : Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma csp_nat_input (nR : nat) (nL : Lean.Nat) : SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
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
Hypothesis Hbuild : forall sR sL, CspSchedRel Job sR sL -> forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (buildR sR tR)) (buildL sL tL).
Variables (baseR : UniprocessorSchedule.schedule Job) (baseL : LSched).
Hypothesis Hbase : CspSchedRel Job baseR baseL.

Lemma csp_nat_eqb tR tL t'R t'L : SubNatRel tR tL -> SubNatRel t'R t'L ->
  CtBoolRel (tR == t'R) (I.Decidable_decide (Lean.eq tL t'L) (I.instDecidableEqNat tL t'L)).
Proof. intros Ht Ht'. exact (ct_decide_eq_nat _ _ _ _ Ht Ht'). Qed.

Lemma csp_UC_update_schedule prevR prevL (Hprev : CspSchedRel Job prevR prevL) nR nL (Hn : SubNatRel nR nL) :
  CspSchedRel Job (@ScheduleConstruction.update_schedule Job buildR prevR nR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule Job dJ buildL prevL nL).
Proof.
  intros tR tL Ht. unfold ScheduleConstruction.update_schedule, I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_update_schedule. cbv beta.
  apply: coq_eq_to_imported_eq.
  rewrite (ct_bool_rel_logic _ _ (csp_nat_eqb tR tL nR nL Ht Hn)).
  case: (tR == nR).
  - exact (imported_eq_to_coq_eq _ _ (Hbuild prevR prevL Hprev tR tL Ht)).
  - exact (imported_eq_to_coq_eq _ _ (Hprev tR tL Ht)).
Qed.

Lemma csp_prefix_canonical (mR : nat) :
  CspSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL (sub_nat_to_imported mR)).
Proof.
  induction mR as [|m IH].
  - refine (csp_trs (csp_lsym (I.Prosa_Validation_ClassicSinglecostPropsInterface_production_schedule_prefix_zero Job dJ buildL baseL))
              (fun z => CspSchedRel Job _ z) _).
    exact (csp_UC_update_schedule baseR baseL Hbase 0 _ (sub_nat_rel_canonical 0)).
  - assert (Hm1 : SubNatRel m.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat)
                                 (sub_nat_to_imported m) (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)))).
    { exact (csp_src_transport (fun x => SubNatRel x _) _ _ (addn1 m)
               (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical m) (sub_nat_rel_canonical 1))). }
    refine (csp_trs Hm1 (fun z => CspSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR m.+1) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) _).
    refine (csp_trs (csp_lsym (I.Prosa_Validation_ClassicSinglecostPropsInterface_production_schedule_prefix_succ Job dJ buildL baseL (sub_nat_to_imported m)))
              (fun z => CspSchedRel Job _ z) _).
    exact (csp_UC_update_schedule _ _ IH _ _ Hm1).
Qed.

Lemma csp_UC_schedule_prefix mR mL (Hm : SubNatRel mR mL) :
  CspSchedRel Job (@ScheduleConstruction.schedule_prefix Job buildR baseR mR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL mL).
Proof. exact (csp_trs Hm (fun z => CspSchedRel Job _ (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_schedule_prefix Job dJ buildL baseL z)) (csp_prefix_canonical mR)). Qed.

Lemma csp_UC_build_schedule_from_prefixes :
  CspSchedRel Job (@ScheduleConstruction.build_schedule_from_prefixes Job buildR baseR) (I.Prosa_Classic_Model_Schedule_Uni_Transformation_Construction_ScheduleConstruction_build_schedule_from_prefixes Job dJ buildL baseL).
Proof. intros tR tL Ht. exact (csp_UC_schedule_prefix tR tL Ht tR tL Ht). Qed.

End UconsConstruction.

Section SuspschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CspSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CspParRel Job aR aL) (Hc : CspParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CspSuspRel Job nR nL.

Lemma csp_SS_backlogged j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ScheduleWithSuspensions.backlogged aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Schedule_ScheduleWithSuspensions_backlogged Job dJ aL cL nL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _
           (ct_bool_and _ _ _ _ (csp_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)
              (ct_bool_not _ _ (csp_US_scheduled_at Job sR sL Hs j _ _ Ht)))
           (ct_bool_not _ _ (csp_SI_suspended_at Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht))).
Qed.

End SuspschedDefs.

Section SuspplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CspSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CspParRel Job aR aL) (Hc : CspParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CspSuspRel Job nR nL.
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CspArrRel Job arrR arrL.

Notation BL := (csp_SS_backlogged Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
Notation SA := (csp_US_scheduled_at Job sR sL Hs).

Lemma csp_SP_work_conserving :
  PropSPropRel (PlatformWithSuspensions.work_conserving aR cR nR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_work_conserving Job dJ aL cL nL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (csp_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma csp_SP_respects_JLDP_policy hR hL (Hh : CspJldpRel Job hR hL) :
  PropSPropRel (PlatformWithSuspensions.respects_JLDP_policy aR cR nR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_Platform_PlatformWithSuspensions_respects_JLDP_policy Job dJ aL cL nL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (csp_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh tR tL Ht j_hp j)).
Qed.

End SuspplatDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CspSchedRel Job sR sL.

Lemma csp_RT_is_response_time_bound_of_job aR aL (Ha : CspParRel Job aR aL) cR cL (Hc : CspParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (csp_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

End UrtDefs.

Section PriodefsDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma csp_PR_JLDP_policy :
  And (forall rR : Priority.JLDP_policy Job, CspJldpRel Job rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)))
      (forall rL : I.Prosa_Classic_Model_Priority_Priority_JLDP_policy Job dJ,
         CspJldpRel Job (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL).
Proof. exact (And_intro _ _ (csp_jldp_canonical Job) (csp_jldp_surjective Job)). Qed.

Lemma csp_reflexive (T : Type) rR rL (Hr : CspRelRel T rR rL) :
  PropSPropRel (reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_reflexiveB T rL).
Proof. apply: ct_forall_identity => x. exact (ct_bool_truth _ _ (Hr x x)). Qed.

Lemma csp_transitive (T : Type) rR rL (Hr : CspRelRel T rR rL) :
  PropSPropRel (transitive rR) (I.Prosa_Classic_Model_Priority_Priority_transitiveB T rL).
Proof.
  apply: ct_forall_identity => y. apply: ct_forall_identity => x. apply: ct_forall_identity => z.
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr x y)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (Hr y z)).
  exact (ct_bool_truth _ _ (Hr x z)).
Qed.

Lemma csp_PR_JLDP_is_reflexive rR rL (Hr : CspJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_reflexive rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_reflexive Job dJ rL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (csp_reflexive Job _ _ (Hr tR tL Ht)). Qed.

Lemma csp_PR_JLDP_is_transitive rR rL (Hr : CspJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_transitive rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_transitive Job dJ rL).
Proof. apply: ct_forall_nat => tR tL Ht. exact (csp_transitive Job _ _ (Hr tR tL Ht)). Qed.

Lemma csp_PR_JLDP_is_total aR aL (Ha : CspArrRel Job aR aL) rR rL (Hr : CspJldpRel Job rR rL) :
  PropSPropRel (Priority.JLDP_is_total aR rR) (I.Prosa_Classic_Model_Priority_Priority_JLDP_is_total Job dJ aL rL).
Proof.
  apply: ct_forall_identity => j1. apply: ct_forall_identity => j2. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (csp_arrives_in Job aR aL Ha j1).
  apply: ct_imp; first exact (csp_arrives_in Job aR aL Ha j2).
  exact (ct_bool_truth _ _ (ct_bool_or _ _ _ _ (Hr tR tL Ht j1 j2) (Hr tR tL Ht j2 j1))).
Qed.

End PriodefsDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section SSCDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (jaR : Job -> nat) (jaL : Job -> Lean.Nat).
Hypothesis Hja : CspParRel Job jaR jaL.
Variables (aR : ArrivalSequence.arrival_sequence Job)
  (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Ha : CspArrRel Job aR aL.
Variables (hR : nat -> Job -> Job -> bool) (hL : Lean.Nat -> Job -> Job -> I.Bool).
Hypothesis Hh : CspJldpRel Job hR hL.
Variables (ssR : UniprocessorSchedule.schedule Job) (ssL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hss : CspSchedRel Job ssR ssL.
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CspSuspRel Job nR nL.
Variables (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypothesis Hc : CspParRel Job cR cL.

Notation READY sR sL Hs tR tL Ht j :=
  (ct_bool_and _ _ _ _ (csp_US_pending Job sR sL Hs jaR jaL Hja cR cL Hc j tR tL Ht)
     (ct_bool_not _ _ (csp_SI_suspended_at Job sR sL Hs jaR jaL cR cL Hja Hc nR nL Hn j tR tL Ht))).

Lemma csp_SSC_ready_jobs sR sL (Hs : CspSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  ClListRel cid (@SustainabilitySingleCost.ready_jobs Job jaR aR nR cR sR tR) (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_Reduction_SustainabilitySingleCost_ready_jobs Job dJ jaL aL nL cL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  have E := cl_list_logic _ _ _ (csp_jobs_arrived_up_to Job aR aL Ha tR tL Ht).
  have F := cl_filter cid _ (fun j => I.Bool_and (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ jaL cL sL j tL)
                          (I.Bool_not (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_at Job dJ jaL cL nL sL j tL)))
              (fun j => READY sR sL Hs tR tL Ht j) (ArrivalSequence.jobs_arrived_up_to aR tR).
  rewrite -E in F. exact F.
Qed.

Lemma csp_SSC_highest_priority_job sR sL (Hs : CspSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@SustainabilitySingleCost.highest_priority_job Job jaR aR hR nR cR sR tR)) (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_Reduction_SustainabilitySingleCost_highest_priority_job Job dJ jaL aL hL nL cL sL tL).
Proof.
  apply: coq_eq_to_imported_eq.
  rewrite /SustainabilitySingleCost.highest_priority_job (csp_seq_min Job (hR tR) (hL tL) (Hh tR tL Ht)).
  rewrite -(cl_list_logic _ _ _ (csp_SSC_ready_jobs sR sL Hs tR tL Ht)).
  reflexivity.
Qed.

Lemma csp_ite_bool (A : Type) bR bL (Hb : CtBoolRel bR bL) (a b : A) :
  Logic.eq (I.ite A (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) a b) (if bR then a else b).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). clear Hb. by case: bR. Qed.

Lemma csp_SSC_build_schedule sR sL (Hs : CspSchedRel Job sR sL) tR tL (Ht : SubNatRel tR tL) :
  Lean.eq (cl_opt (@SustainabilitySingleCost.build_schedule Job jaR aR hR ssR nR cR sR tR)) (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_Reduction_SustainabilitySingleCost_build_schedule Job dJ jaL aL hL ssL nL cL sL tL).
Proof.
  apply: coq_eq_to_imported_eq. rewrite /SustainabilitySingleCost.build_schedule. unfold I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_Reduction_SustainabilitySingleCost_build_schedule.
  rewrite -(imported_eq_to_coq_eq _ _ (csp_SSC_highest_priority_job sR sL Hs tR tL Ht)).
  case: (@SustainabilitySingleCost.highest_priority_job Job jaR aR hR nR cR sR tR) => [jhp|] /=; last reflexivity.
  rewrite -(imported_eq_to_coq_eq _ _ (Hss tR tL Ht)).
  case: (ssR tR) => [js|] /=; last reflexivity.
  rewrite (csp_ite_bool _ _ _ (ct_bool_and _ _ _ _ (READY sR sL Hs tR tL Ht js) (Hh tR tL Ht js jhp))).
  by case: (_ && _).
Qed.

Lemma csp_empty : CspSchedRel Job (fun _ => None) (fun _ => I.Option_none Job).
Proof. intros tR tL Ht. exact (@Lean.eq_refl _ _). Qed.

Lemma csp_SSC_sched_susp_highercost :
  CspSchedRel Job (@SustainabilitySingleCost.sched_susp_highercost Job jaR aR hR ssR nR cR) (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_Reduction_SustainabilitySingleCost_sched_susp_highercost Job dJ jaL aL hL ssL nL cL).
Proof. exact (csp_UC_build_schedule_from_prefixes Job _ _ csp_SSC_build_schedule _ _ csp_empty). Qed.

End SSCDefs.

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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CspParRel _ f g |- _ => exact (H x) end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (csp_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (csp_forall_sched _); intros ? ? ?
  | nat -> option _ => apply: (csp_forall_sched _); intros ? ? ?
  | Priority.JLDP_policy _ => apply: (csp_forall_jldp _); intros ? ? ?
  | Suspension.job_suspension _ => apply: (csp_forall_susp _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: csp_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- CspSchedRel _ (SustainabilitySingleCost.sched_susp_highercost _ _ _ _ _ _) _ => eapply csp_SSC_sched_susp_highercost; crel
    | |- Lean.eq (cl_opt (SustainabilitySingleCost.build_schedule _ _ _ _ _ _ _ _)) _ => eapply csp_SSC_build_schedule; crel
    | |- Lean.eq (cl_opt (?s _)) _ => first [ match goal with H : CspSchedRel _ s _ |- _ => eapply H; crel end | eapply csp_SSC_sched_susp_highercost; crel ]
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => eapply ct_sub_rel; crel
  | S _ => eapply csp_succ_rel; crel
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
  | _ <-> _ => fail; crel
  | _ <> _ => eapply csp_ne
  | ~ _ => eapply ct_imp; [crel | exact csp_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | eapply csp_opt_rel_eq; crel ]
with crel_n_defs := first [ eapply csp_US_service; crel
    | eapply csp_LE_time_after_last_execution; crel
    | eapply csp_SI_suspension_duration; crel
    | eapply csp_US_service_during; crel ]
with crel_b_defs := first [ eapply csp_US_scheduled_at; crel
    | eapply csp_US_completed_by; crel
    | eapply csp_has_arrived; crel
    | eapply csp_SI_suspended_at; crel
    | eapply csp_US_pending; crel ]
with crel_l_defs := first [ fail ]
with crel_p_defs := first [ eapply csp_arrives_in; crel
    | eapply csp_consistent; crel
    | eapply csp_US_jobs_come_from_arrival_sequence; crel
    | eapply csp_US_jobs_must_arrive_to_execute; crel
    | eapply csp_US_completed_jobs_dont_execute; crel
    | eapply csp_SP_work_conserving; crel
    | eapply csp_SP_respects_JLDP_policy; crel
    | eapply csp_SI_respects_self_suspensions; crel
    | eapply csp_RT_is_response_time_bound_of_job; crel
    | eapply csp_PR_JLDP_is_reflexive; crel
    | eapply csp_PR_JLDP_is_transitive; crel
    | eapply csp_PR_JLDP_is_total; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_sched_susp_highercost_depends_only_on_prefix (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_depends_only_on_prefix Job)).
Definition tgt_sched_susp_highercost_depends_only_on_prefix (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_depends_only_on_prefix Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_depends_only_on_prefix_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_depends_only_on_prefix Job) (tgt_sched_susp_highercost_depends_only_on_prefix Job).
Proof. unfold src_sched_susp_highercost_depends_only_on_prefix, tgt_sched_susp_highercost_depends_only_on_prefix. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_uses_construction_function (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_uses_construction_function Job)).
Definition tgt_sched_susp_highercost_uses_construction_function (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_uses_construction_function Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_uses_construction_function_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_uses_construction_function Job) (tgt_sched_susp_highercost_uses_construction_function Job).
Proof. unfold src_sched_susp_highercost_uses_construction_function, tgt_sched_susp_highercost_uses_construction_function. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_jobs_come_from_arrival_sequence (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_jobs_come_from_arrival_sequence Job)).
Definition tgt_sched_susp_highercost_jobs_come_from_arrival_sequence (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_jobs_come_from_arrival_sequence Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_jobs_come_from_arrival_sequence_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_jobs_come_from_arrival_sequence Job) (tgt_sched_susp_highercost_jobs_come_from_arrival_sequence Job).
Proof. unfold src_sched_susp_highercost_jobs_come_from_arrival_sequence, tgt_sched_susp_highercost_jobs_come_from_arrival_sequence. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_jobs_must_arrive_to_execute (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_jobs_must_arrive_to_execute Job)).
Definition tgt_sched_susp_highercost_jobs_must_arrive_to_execute (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_jobs_must_arrive_to_execute Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_jobs_must_arrive_to_execute_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_jobs_must_arrive_to_execute Job) (tgt_sched_susp_highercost_jobs_must_arrive_to_execute Job).
Proof. unfold src_sched_susp_highercost_jobs_must_arrive_to_execute, tgt_sched_susp_highercost_jobs_must_arrive_to_execute. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_completed_jobs_dont_execute (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_completed_jobs_dont_execute Job)).
Definition tgt_sched_susp_highercost_completed_jobs_dont_execute (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_completed_jobs_dont_execute Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_completed_jobs_dont_execute_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_completed_jobs_dont_execute Job) (tgt_sched_susp_highercost_completed_jobs_dont_execute Job).
Proof. unfold src_sched_susp_highercost_completed_jobs_dont_execute, tgt_sched_susp_highercost_completed_jobs_dont_execute. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_work_conserving (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_work_conserving Job)).
Definition tgt_sched_susp_highercost_work_conserving (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_work_conserving Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_work_conserving_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_work_conserving Job) (tgt_sched_susp_highercost_work_conserving Job).
Proof. unfold src_sched_susp_highercost_work_conserving, tgt_sched_susp_highercost_work_conserving. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_respects_policy (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_respects_policy Job)).
Definition tgt_sched_susp_highercost_respects_policy (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_respects_policy Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_respects_policy_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_respects_policy Job) (tgt_sched_susp_highercost_respects_policy Job).
Proof. unfold src_sched_susp_highercost_respects_policy, tgt_sched_susp_highercost_respects_policy. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_respects_self_suspensions (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_respects_self_suspensions Job)).
Definition tgt_sched_susp_highercost_respects_self_suspensions (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_respects_self_suspensions Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_respects_self_suspensions_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_respects_self_suspensions Job) (tgt_sched_susp_highercost_respects_self_suspensions Job).
Proof. unfold src_sched_susp_highercost_respects_self_suspensions, tgt_sched_susp_highercost_respects_self_suspensions. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_same_completion (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_same_completion Job)).
Definition tgt_sched_susp_highercost_same_completion (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_same_completion Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_same_completion_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_same_completion Job) (tgt_sched_susp_highercost_same_completion Job).
Proof. unfold src_sched_susp_highercost_same_completion, tgt_sched_susp_highercost_same_completion. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_same_time_after_last_exec (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_same_time_after_last_exec Job)).
Definition tgt_sched_susp_highercost_same_time_after_last_exec (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_same_time_after_last_exec Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_same_time_after_last_exec_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_same_time_after_last_exec Job) (tgt_sched_susp_highercost_same_time_after_last_exec Job).
Proof. unfold src_sched_susp_highercost_same_time_after_last_exec, tgt_sched_susp_highercost_same_time_after_last_exec. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_same_suspension_duration (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_same_suspension_duration Job)).
Definition tgt_sched_susp_highercost_same_suspension_duration (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_same_suspension_duration Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_same_suspension_duration_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_same_suspension_duration Job) (tgt_sched_susp_highercost_same_suspension_duration Job).
Proof. unfold src_sched_susp_highercost_same_suspension_duration, tgt_sched_susp_highercost_same_suspension_duration. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_same_suspension (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_same_suspension Job)).
Definition tgt_sched_susp_highercost_same_suspension (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_same_suspension Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_same_suspension_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_same_suspension Job) (tgt_sched_susp_highercost_same_suspension Job).
Proof. unfold src_sched_susp_highercost_same_suspension, tgt_sched_susp_highercost_same_suspension. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_same_schedule (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_same_schedule Job)).
Definition tgt_sched_susp_highercost_same_schedule (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_same_schedule Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_same_schedule_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_same_schedule Job) (tgt_sched_susp_highercost_same_schedule Job).
Proof. unfold src_sched_susp_highercost_same_schedule, tgt_sched_susp_highercost_same_schedule. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_scheduled_in_susp_iff_scheduled_in_wcet (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.scheduled_in_susp_iff_scheduled_in_wcet Job)).
Definition tgt_scheduled_in_susp_iff_scheduled_in_wcet (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_scheduled_in_susp_iff_scheduled_in_wcet Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_scheduled_in_susp_iff_scheduled_in_wcet_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_in_susp_iff_scheduled_in_wcet Job) (tgt_scheduled_in_susp_iff_scheduled_in_wcet Job).
Proof. unfold src_scheduled_in_susp_iff_scheduled_in_wcet, tgt_scheduled_in_susp_iff_scheduled_in_wcet. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_same_service_for_j (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_same_service_for_j Job)).
Definition tgt_sched_susp_highercost_same_service_for_j (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_same_service_for_j Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_same_service_for_j_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_same_service_for_j Job) (tgt_sched_susp_highercost_same_service_for_j Job).
Proof. unfold src_sched_susp_highercost_same_service_for_j, tgt_sched_susp_highercost_same_service_for_j. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_r_le_R (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_r_le_R Job)).
Definition tgt_sched_susp_highercost_r_le_R (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_r_le_R Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_r_le_R_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_r_le_R Job) (tgt_sched_susp_highercost_r_le_R Job).
Proof. unfold src_sched_susp_highercost_r_le_R, tgt_sched_susp_highercost_r_le_R. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_R_bounds_inflated_cost (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.R_bounds_inflated_cost Job)).
Definition tgt_R_bounds_inflated_cost (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_R_bounds_inflated_cost Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_R_bounds_inflated_cost_correspondence (Job : eqType) :
  PropSPropRel (src_R_bounds_inflated_cost Job) (tgt_R_bounds_inflated_cost Job).
Proof. unfold src_R_bounds_inflated_cost, tgt_R_bounds_inflated_cost. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_sched_susp_highercost_incurs_more_interference (Job : eqType) : Prop :=
  ltac:(type_of_term (@SustainabilitySingleCostProperties.sched_susp_highercost_incurs_more_interference Job)).
Definition tgt_sched_susp_highercost_incurs_more_interference (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Susp_Sustainability_Singlecost_ReductionProperties_SustainabilitySingleCostProperties_sched_susp_highercost_incurs_more_interference Job (ct_decidable_eq Job))).
Theorem SustainabilitySingleCostProperties_sched_susp_highercost_incurs_more_interference_correspondence (Job : eqType) :
  PropSPropRel (src_sched_susp_highercost_incurs_more_interference Job) (tgt_sched_susp_highercost_incurs_more_interference Job).
Proof. unfold src_sched_susp_highercost_incurs_more_interference, tgt_sched_susp_highercost_incurs_more_interference. crel_spine. crel. Unshelve. all: crel. Qed.
