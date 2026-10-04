From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div.
From prosa Require Import util.seqset classic.model.time classic.util.list classic.util.div_mod classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.policy_tdma classic.model.schedule.uni.schedule classic.model.schedule.uni.response_time classic.model.schedule.uni.basic.platform_tdma classic.model.schedule.uni.end_time classic.analysis.uni.basic.tdma_wcrt_analysis classic.model.arrival.basic.task classic.model.arrival.basic.task_arrival classic.model.schedule.uni.schedulability classic.analysis.uni.basic.tdma_rta_theory.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicTdmaRtaTheory.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicTdmaRtaTheoryBase ClassicTdmaRtaTheoryList.



Module I := ImportedClassicTdmaRtaTheory.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/basic/tdma_rta_theory.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; times by [SubNatRel]; job parameters
    pointwise through [SubNatRel]; uniprocessor schedules pointwise through the option map; arrival sequences pointwise
    on related times; task sets elementwise, TDMA slots pointwise through [SubNatRel], slot orders pointwise on
    Booleans; all with two-way totals.  The imported uniprocessor schedule and TDMA policy definitions are related as
    in the accepted classic certificates (re-bound below, through the kernel-guarded body projections, the [sumSeq] /
    [sumFiltered] constructor equations and the [DivModInterface] Euclidean equations of
    [ClassicUniPlatformTdmaInterface]). The TDMA platform and end-time notions are related as in the accepted classic certificates
    (re-bound below); the Rocq section-local arithmetic [Let]s are unfolded on the source side and correspond to
    the Lean [LEAN_HELPER] definitions of the same names (no certificate of their own); [div_ceil] through the
    accepted div/mod relation. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma ctr_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma ctr_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma ctr_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) ctr_false_rel). Qed.

Lemma ctr_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma ctr_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma ctr_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma ctr_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma ctr_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma ctr_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (ctr_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => ctr_unmap_rel T l) PR PL).
Qed.

Definition CtrParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma ctr_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CtrParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ctr_forall_cover _ _ (CtrParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint ctr_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ctr_natl s') end.

Definition ctr_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma ctr_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) ctr_one) (ctr_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) ctr_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ctr_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ctr_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma ctr_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma ctr_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma ctr_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH ctr_cl_append. reflexivity.
Qed.

Lemma ctr_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CtrFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CtrArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition ctr_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition ctr_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma ctr_arr_canonical aR : CtrArrRel aR (ctr_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /ctr_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma ctr_arr_surjective aL : CtrArrRel (ctr_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma ctr_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CtrArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (ctr_forall_cover _ _ CtrArrRel ctr_arr_to_target ctr_arr_to_source ctr_arr_canonical ctr_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma ctr_arrives_in aR aL (Ha : CtrArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (ctr_mem Job j _ _ (Ha tR tL Ht)). Qed.

Lemma ctr_consistent pR pL (Hp : CtrParRel Job pR pL) aR aL (Ha : CtrArrRel Job aR aL) :
  PropSPropRel (ArrivalSequence.arrival_times_are_consistent pR aR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_times_are_consistent Job dJ pL aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_decide_bool _ _ _ (ctr_mem Job j _ _ (Ha tR tL Ht)))).
  exact (sub_nat_eq_correspondence _ _ _ _ (Hp j) Ht).
Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma ctr_arrives_at aR aL (Ha : CtrArrRel Job aR aL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.arrives_at aR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_at Job dJ aL j tL).
Proof. exact (ct_decide_bool _ _ _ (ctr_mem Job j _ _ (Ha tR tL Ht))). Qed.

Lemma ctr_has_arrived pR pL (Hp : CtrParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint ctr_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ctr_snatl s') end.

Lemma ctr_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (ctr_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ctr_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ctr_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ctr_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ctr_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma ctr_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CtrFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma ctr_fun_canonical FR FL (HF : CtrFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma ctr_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma ctr_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CtrFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ctr_nat_sub_canonical nR mR.
  rewrite ctr_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (ctr_foldr_add FL FR (ctr_fun_canonical FR FL HF)).
  by rewrite ctr_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition ctr_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition ctr_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma ctr_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma ctr_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (ctr_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CtrSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition ctr_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition ctr_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma ctr_sched_canonical sR : CtrSchedRel sR (ctr_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /ctr_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma ctr_sched_surjective sL : CtrSchedRel (ctr_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /ctr_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma ctr_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CtrSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (ctr_forall_cover _ _ CtrSchedRel ctr_sched_to_target ctr_sched_to_source ctr_sched_canonical ctr_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ctr_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CtrSchedRel Job sR (ctr_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CtrSchedRel Job (ctr_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (ctr_sched_canonical Job) (ctr_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CtrSchedRel Job sR sL.

Lemma ctr_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (ctr_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (ctr_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma ctr_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (ctr_US_scheduled_at j tR tL Ht)). Qed.

Lemma ctr_service_at_fun j : CtrFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (ctr_US_service_at j kR kL Hk). Qed.

Lemma ctr_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (ctr_ico _ _ _ _ _ _ H1 H2 (ctr_service_at_fun j)). Qed.

Lemma ctr_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (ctr_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma ctr_US_completed_by cR cL (Hc : CtrParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (ctr_US_service j tR tL Ht)). Qed.

Lemma ctr_US_pending aR aL (Ha : CtrParRel Job aR aL) cR cL (Hc : CtrParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ctr_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (ctr_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma ctr_US_backlogged aR aL (Ha : CtrParRel Job aR aL) cR cL (Hc : CtrParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ctr_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (ctr_US_scheduled_at j tR tL Ht))).
Qed.

Lemma ctr_US_jobs_must_arrive_to_execute aR aL (Ha : CtrParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctr_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (ctr_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma ctr_US_completed_jobs_dont_execute cR cL (Hc : CtrParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (ctr_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma ctr_J_job_cost_positive cR cL (Hc : CtrParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma ctr_J_job_deadline_positive dR dL (Hd : CtrParRel Job dR dL) j :
  CtBoolRel (Job.job_deadline_positive dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_positive Job dJ dL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd j)). Qed.

Lemma ctr_J_job_cost_le_deadline cR cL dR dL (Hc : CtrParRel Job cR cL) (Hd : CtrParRel Job dR dL) j :
  CtBoolRel (Job.job_cost_le_deadline cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_deadline Job dJ cL dL j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Hd j)). Qed.

Lemma ctr_J_valid_realtime_job cR cL dR dL (Hc : CtrParRel Job cR cL) (Hd : CtrParRel Job dR dL) j :
  PropSPropRel (Job.valid_realtime_job cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_realtime_job Job dJ cL dL j).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ctr_J_job_cost_positive cR cL Hc j)).
  apply: ct_and; first exact (ct_bool_truth _ _ (ctr_J_job_cost_le_deadline cR cL dR dL Hc Hd j)).
  exact (ct_bool_truth _ _ (ctr_J_job_deadline_positive dR dL Hd j)).
Qed.

Lemma ctr_J_job_cost_le_task_cost tcR tcL (Htc : CtrParRel Task tcR tcL) cR cL (Hc : CtrParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma ctr_J_job_deadline_eq_task_deadline tdR tdL (Htd : CtrParRel Task tdR tdL) dR dL (Hd : CtrParRel Job dR dL)
    (job_task : Job -> Task) j :
  PropSPropRel (Job.job_deadline_eq_task_deadline tdR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_eq_task_deadline Task dT tdL Job dJ dL job_task j).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))). Qed.

Lemma ctr_J_valid_sporadic_job tcR tcL tdR tdL (Htc : CtrParRel Task tcR tcL) (Htd : CtrParRel Task tdR tdL)
    cR cL dR dL (Hc : CtrParRel Job cR cL) (Hd : CtrParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task dT tcL tdL Job dJ cL dL job_task j).
Proof.
  apply: ct_and; first exact (ctr_J_valid_realtime_job cR cL dR dL Hc Hd j).
  apply: ct_and; first exact (ct_bool_truth _ _ (ctr_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
  exact (ctr_J_job_deadline_eq_task_deadline tdR tdL Htd dR dL Hd job_task j).
Qed.

End JobDefs.

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
(** * Sequence sums against [sumSeq] / [sumFiltered] (as in the accepted v0.6 request-bound-function certificates) *)

Section TdmaSums.
Variable X : Type.
Variable FR : X -> nat.
Variable FL : X -> Lean.Nat.
Hypothesis HF : forall x, SubNatRel (FR x) (FL x).

Lemma ctr_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicTdmaRtaTheoryInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicTdmaRtaTheoryInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma ctr_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (ctr_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma ctr_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicTdmaRtaTheoryInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicTdmaRtaTheoryInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicTdmaRtaTheoryInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma ctr_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (ctr_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End TdmaSums.

(* ------------------------------------------------------------------ *)
(** * Task sets, slots and slot orders *)

Section TdmaRel.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation LSet := (I.Prosa_Util_Seqset_set Task dT).

Definition CtrSetRel (sR : {set Task}) (sL : LSet) : SProp :=
  ClListRel cid (@prosa.util.seqset._set_seq Task sR) (I.Prosa_Util_Seqset_set_val Task dT sL).

Lemma ctr_uniq_rel (xs : seq Task) : PropSPropRel (uniq xs) (I.List_Nodup Task (cl_map cid xs)).
Proof. exact (cl_uniq_rel Task Task cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) xs). Qed.

Definition ctr_set_to_target (sR : {set Task}) : LSet :=
  match sR with
  | @prosa.util.seqset.Build_set _ xs Hu =>
      I.Prosa_Util_Seqset_set_mk Task dT (cl_map cid xs) (prop_to_sprop _ _ (ctr_uniq_rel xs) Hu)
  end.

Lemma ctr_import_uniq (xs : I.List Task) (Hn : I.List_Nodup Task xs) : uniq (cl_unmap cid xs).
Proof.
  apply (sprop_to_prop _ _ (ctr_uniq_rel (cl_unmap cid xs))).
  rewrite (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) xs). exact Hn.
Qed.

Definition ctr_set_to_source (sL : LSet) : {set Task} :=
  match sL with
  | I.Prosa_Util_Seqset_set_mk xs Hn => @prosa.util.seqset.Build_set Task (cl_unmap cid xs) (ctr_import_uniq xs Hn)
  end.

Lemma ctr_set_canonical sR : CtrSetRel sR (ctr_set_to_target sR).
Proof. destruct sR. exact (@Lean.eq_refl _ _). Qed.

Lemma ctr_set_surjective sL : CtrSetRel (ctr_set_to_source sL) sL.
Proof.
  destruct sL as [xs Hn]. unfold CtrSetRel. cbn.
  exact (coq_eq_to_imported_eq _ _ (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) xs)).
Qed.

Lemma ctr_forall_set (PR : {set Task} -> Prop) (PL : LSet -> SProp) :
  (forall sR sL, CtrSetRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (ctr_forall_cover _ _ CtrSetRel ctr_set_to_target ctr_set_to_source ctr_set_canonical ctr_set_surjective PR PL). Qed.

Lemma ctr_set_mem x sR sL (Hs : CtrSetRel sR sL) :
  PropSPropRel (x \in sR) (I.Membership_mem Task LSet (I.Prosa_Util_Seqset_instMembershipSet Task dT) sL x).
Proof. exact (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) x _ _ Hs). Qed.

Definition CtrOrdRel (oR : rel Task) (oL : Task -> Task -> I.Bool) : SProp := forall a b, CtBoolRel (oR a b) (oL a b).

Definition ctr_ord_to_target (oR : rel Task) : Task -> Task -> I.Bool := fun a b => ct_b2l (oR a b).
Definition ctr_ord_to_source (oL : Task -> Task -> I.Bool) : rel Task := fun a b => ct_l2b (oL a b).

Lemma ctr_ord_canonical oR : CtrOrdRel oR (ctr_ord_to_target oR).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma ctr_ord_surjective oL : CtrOrdRel (ctr_ord_to_source oL) oL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma ctr_forall_ord (PR : rel Task -> Prop) (PL : (Task -> Task -> I.Bool) -> SProp) :
  (forall oR oL, CtrOrdRel oR oL -> PropSPropRel (PR oR) (PL oL)) -> PropSPropRel (forall o, PR o) (forall o, PL o).
Proof. exact (ctr_forall_cover _ _ CtrOrdRel ctr_ord_to_target ctr_ord_to_source ctr_ord_canonical ctr_ord_surjective PR PL). Qed.

Lemma ctr_neq x y : CtBoolRel (x != y) (I.Bool_not (I.Decidable_decide (Lean.eq x y) (dT x y))).
Proof. exact (ct_bool_not _ _ (ct_decide_eq Task x y)). Qed.

End TdmaRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section TdmaDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

Lemma ctr_TD_TDMA_slot :
  And (forall sR : PolicyTDMA.TDMA_slot Task, CtrParRel Task sR (fun x => sub_nat_to_imported (sR x)))
      (forall sL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT, CtrParRel Task (fun x => sub_nat_to_rocq (sL x)) sL).
Proof.
  exact (And_intro _ _ (fun sR x => sub_nat_rel_canonical (sR x)) (fun sL x => sub_nat_rel_surjective (sL x))).
Qed.

Lemma ctr_TD_TDMA_slot_order :
  And (forall oR : PolicyTDMA.TDMA_slot_order Task, CtrOrdRel Task oR (ctr_ord_to_target Task oR))
      (forall oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT, CtrOrdRel Task (ctr_ord_to_source Task oL) oL).
Proof. exact (And_intro _ _ (ctr_ord_canonical Task) (ctr_ord_surjective Task)). Qed.

Lemma ctr_TD_is_valid_time_slot task slR slL (Hsl : CtrParRel Task slR slL) :
  CtBoolRel (PolicyTDMA.is_valid_time_slot task slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_is_valid_time_slot Task dT task slL).
Proof. exact (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hsl task)). Qed.

Lemma ctr_TD_TDMA_cycle sR sL (Hs : CtrSetRel Task sR sL) slR slL (Hsl : CtrParRel Task slR slL) :
  SubNatRel (PolicyTDMA.TDMA_cycle sR slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_cycle Task dT sL slL).
Proof. exact (ctr_sum_rel Task slR slL Hsl _ _ Hs). Qed.

Lemma ctr_TD_Task_slot_offset sR sL (Hs : CtrSetRel Task sR sL) oR oL (Ho : CtrOrdRel Task oR oL)
    task slR slL (Hsl : CtrParRel Task slR slL) :
  SubNatRel (PolicyTDMA.Task_slot_offset sR oR task slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_slot_offset Task dT sL oL task slL).
Proof.
  exact (ctr_sum_filtered_rel Task slR slL Hsl _
    (fun p => I.Bool_and (oL p task) (I.Bool_not (I.Decidable_decide (Lean.eq p task) (dT p task))))
    (fun p => ct_bool_and _ _ _ _ (Ho p task) (ctr_neq Task p task)) _ _ Hs).
Qed.

Lemma ctr_TD_Task_in_time_slot sR sL (Hs : CtrSetRel Task sR sL) oR oL (Ho : CtrOrdRel Task oR oL)
    task slR slL (Hsl : CtrParRel Task slR slL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (PolicyTDMA.Task_in_time_slot sR oR task slR tR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_in_time_slot Task dT sL oL task slL tL).
Proof.
  have HC := ctr_TD_TDMA_cycle sR sL Hs slR slL Hsl.
  have HO := ctr_TD_Task_slot_offset sR sL Hs oR oL Ho task slR slL Hsl.
  apply: ct_decide_lt; last exact (Hsl task).
  apply: dm_mod_correspondence; last exact HC.
  apply: dm_sub_correspondence; last exact (dm_mod_correspondence _ _ _ _ HO HC).
  exact (sub_add_correspondence _ _ _ _ Ht HC).
Qed.

End TdmaDefs.

Lemma ctr_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

Lemma ctr_iff (P Q : Prop) (PL QL : SProp) :
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

(** The imported [TaskArrival] definitions (as in the accepted classic task_arrival certificate). *)
Section TaskArrivalDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma ctr_TA_sporadic_task_model tpR tpL (Htp : CtrParRel Task tpR tpL)
    jaR jaL (Hja : CtrParRel Job jaR jaL) (job_task : Job -> Task) aR aL (Ha : CtrArrRel Job aR aL) :
  PropSPropRel (TaskArrival.sporadic_task_model tpR jaR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_TaskArrival_TaskArrival_sporadic_task_model Task dT tpL Job dJ jaL job_task aL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j'.
  apply: ct_imp; first exact (ctr_ne Job j j').
  apply: ct_imp; first exact (ctr_arrives_in Job aR aL Ha j).
  apply: ct_imp; first exact (ctr_arrives_in Job aR aL Ha j').
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task j')).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ (Hja j) (Hja j')).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (Hja j) (Htp (job_task j))) (Hja j')).
Qed.

End TaskArrivalDefs.

Section UrtDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CtrSchedRel Job sR sL.

Lemma ctr_RT_is_response_time_bound_of_job aR aL (Ha : CtrParRel Job aR aL) cR cL (Hc : CtrParRel Job cR cL)
    j rR rL (Hr : SubNatRel rR rL) :
  CtBoolRel (ResponseTime.is_response_time_bound_of_job aR cR sR j rR) (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_job Job dJ aL cL sL j rL).
Proof. exact (ctr_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) Hr)). Qed.

Lemma ctr_RT_is_response_time_bound_of_task aR aL (Ha : CtrParRel Job aR aL) cR cL (Hc : CtrParRel Job cR cL)
    (job_task : Job -> Task) arrR arrL (Harr : CtrArrRel Job arrR arrL) tsk rR rL (Hr : SubNatRel rR rL) :
  PropSPropRel (ResponseTime.is_response_time_bound_of_task aR cR job_task arrR sR tsk rR)
    (I.Prosa_Classic_Model_Schedule_Uni_ResponseTime_ResponseTime_is_response_time_bound_of_task Task dT Job dJ aL cL job_task arrL sL tsk rL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ctr_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ct_bool_truth _ _ (ctr_RT_is_response_time_bound_of_job aR aL Ha cR cL Hc j rR rL Hr)).
Qed.

End UrtDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section TWTDPDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CtrSchedRel Job sR sL.
Variables (tsR : {set Task}) (tsL : I.Prosa_Util_Seqset_set Task dT).
Hypothesis Hts : CtrSetRel Task tsR tsL.
Variables (slR : PolicyTDMA.TDMA_slot Task) (slL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT).
Hypothesis Hsl : CtrParRel Task slR slL.
Variables (oR : PolicyTDMA.TDMA_slot_order Task) (oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT).
Hypothesis Ho : CtrOrdRel Task oR oL.
Variable job_task : Job -> Task.

Lemma ctr_in_slot j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (PolicyTDMA.Task_in_time_slot tsR oR (job_task j) slR tR)
    (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_in_time_slot Task dT tsL oL (job_task j) slL tL).
Proof. exact (ctr_TD_Task_in_time_slot Task tsR tsL Hts oR oL Ho (job_task j) slR slL Hsl tR tL Ht). Qed.

Lemma ctr_TDP_sched_implies_in_slot j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (Platform_TDMA.sched_implies_in_slot job_task sR tsR slR oR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_sched_implies_in_slot Task dT Job dJ job_task sL tsL slL oL j tL).
Proof.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctr_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (ctr_in_slot j tR tL Ht)).
Qed.

Lemma ctr_TDP_backlogged_implies_not_in_slot_or_other_job_sched aR aL (Ha : CtrParRel Job aR aL)
    cR cL (Hc : CtrParRel Job cR cL) arrR arrL (Harr : CtrArrRel Job arrR arrL) j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (Platform_TDMA.backlogged_implies_not_in_slot_or_other_job_sched aR cR job_task arrR sR tsR slR oR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_backlogged_implies_not_in_slot_or_other_job_sched Task dT Job dJ aL cL job_task arrL sL tsL slL oL j tL).
Proof.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctr_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_or.
  - apply: ct_imp; first exact (ct_bool_truth _ _ (ctr_in_slot j tR tL Ht)).
    exact ctr_false_rel.
  - apply: ct_exists_identity => j_other.
    apply: ct_and; first exact (ctr_arrives_in Job arrR arrL Harr j_other).
    apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j_other) (Ha j)).
    apply: ct_and; first exact (ct_eq_rel Task (job_task j) (job_task j_other)).
    exact (ct_bool_truth _ _ (ctr_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

Lemma ctr_TDP_Respects_TDMA_policy aR aL (Ha : CtrParRel Job aR aL)
    cR cL (Hc : CtrParRel Job cR cL) arrR arrL (Harr : CtrArrRel Job arrR arrL) :
  PropSPropRel (Platform_TDMA.Respects_TDMA_policy aR cR job_task arrR sR tsR slR oR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_Respects_TDMA_policy Task dT Job dJ aL cL job_task arrL sL tsL slL oL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ctr_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (ctr_TDP_sched_implies_in_slot j tR tL Ht).
  exact (ctr_TDP_backlogged_implies_not_in_slot_or_other_job_sched aR aL Ha cR cL Hc arrR arrL Harr j tR tL Ht).
Qed.

End TWTDPDefs.

(* ------------------------------------------------------------------ *)
(** * [diagnosis_option] (constructor-wise, related instants) *)

Notation nc := sub_nat_to_imported.
Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Definition ctr_dg_to_target (d : end_time.diagnosis_option) : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option :=
  match d with
  | end_time.OK t => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK (nc t)
  | end_time.Failure t => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_Failure (nc t)
  end.
Definition ctr_dg_to_source (d : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option) : end_time.diagnosis_option :=
  match d with
  | I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK t => end_time.OK (sub_nat_to_rocq t)
  | I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_Failure t => end_time.Failure (sub_nat_to_rocq t)
  end.
Definition CtrDgRel (dR : end_time.diagnosis_option) (dL : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option) : SProp :=
  Lean.eq (ctr_dg_to_target dR) dL.

Lemma ctr_dg_ts d : Logic.eq (ctr_dg_to_source (ctr_dg_to_target d)) d.
Proof. case: d => t /=; by rewrite sub_nat_rocq_roundtrip. Qed.

Lemma ctr_dg_eq dR1 dL1 dR2 dL2 (H1 : CtrDgRel dR1 dL1) (H2 : CtrDgRel dR2 dL2) :
  PropSPropRel (Logic.eq dR1 dR2) (Lean.eq dL1 dL2).
Proof.
  rewrite -(EQ H1) -(EQ H2). clear H1 H2. apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := f_equal ctr_dg_to_source (EQ E). by rewrite !ctr_dg_ts in E'.
Qed.

Lemma ctr_OK tR tL (Ht : SubNatRel tR tL) : CtrDgRel (end_time.OK tR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK tL).
Proof. exact (sub_imported_eq_congr (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK) _ _ Ht). Qed.

Lemma ctr_not_rel (P : Prop) (PL : SProp) : PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof. intro H. exact (ct_imp _ _ _ _ H ctr_false_rel). Qed.

(* ------------------------------------------------------------------ *)
(** * [end_time_option] and [end_time_predicate] *)

Section TWETEndTime.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CtrSchedRel Job sR sL.
Variable job : Job.
Notation SA := (ctr_US_scheduled_at Job sR sL Hs job).

Lemma ctr_back_rel tL : SubNatRel (sub_nat_to_rocq tL) tL.
Proof. exact (sub_nat_imported_roundtrip tL). Qed.

End TWETEndTime.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ctr_dg_st d : Logic.eq (ctr_dg_to_target (ctr_dg_to_source d)) d.
Proof.
  case: d => t /=; by rewrite (EQ (sub_nat_imported_roundtrip t)).
Qed.

(** The inductive [diagnosis_option]: the constructor-wise relation is total in both directions. *)
Lemma ctr_ET_diagnosis_option :
  And (forall dR : end_time.diagnosis_option, CtrDgRel dR (ctr_dg_to_target dR))
      (forall dL : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option, CtrDgRel (ctr_dg_to_source dL) dL).
Proof.
  exact (And_intro _ _ (fun dR => @Lean.eq_refl _ _) (fun dL => coq_eq_to_imported_eq _ _ (ctr_dg_st dL))).
Qed.

(* ------------------------------------------------------------------ *)
(** * Conditionals *)

(** A Lean [ite] on a decidable proposition against a Rocq Boolean [if], given the relation of the
    Boolean test to the proposition (any decision procedure). *)
Lemma ctr_ite_nat (bR : bool) (P : SProp) (d : I.Decidable P) (H : PropSPropRel (is_true bR) P)
    xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR) (I.ite Lean.Nat P d xL yL).
Proof.
  destruct d as [Hf | Ht]; destruct bR; cbn.
  - exact (ct_false_elim _ (Hf (prop_to_sprop _ _ H (Logic.eq_refl true)))).
  - exact Hy.
  - exact Hx.
  - exact (ct_false_elim _ (ct_coq_false_to_target (match sprop_to_prop _ _ H Ht with end))).
Qed.

Lemma ctr_eqn0 nR nL (Hn : SubNatRel nR nL) :
  PropSPropRel (is_true (nR == 0)) (Lean.eq nL (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))).
Proof.
  have E := sub_nat_eq_correspondence _ _ _ _ Hn (sub_nat_rel_canonical 0).
  apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

(* ------------------------------------------------------------------ *)
(** * The section-local arithmetic [Let]s (Lean [LEAN_HELPER] definitions) *)

Section TWArith.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tsR : {set Task}) (tsL : I.Prosa_Util_Seqset_set Task dT).
Hypothesis Hts : CtrSetRel Task tsR tsL.
Variables (slR : PolicyTDMA.TDMA_slot Task) (slL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT).
Hypothesis Hsl : CtrParRel Task slR slL.
Variables (oR : PolicyTDMA.TDMA_slot_order Task) (oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT).
Hypothesis Ho : CtrOrdRel Task oR oL.
Variable tsk : Task.
Notation HC := (ctr_TD_TDMA_cycle Task tsR tsL Hts slR slL Hsl).
Notation HO := (ctr_TD_Task_slot_offset Task tsR tsL Hts oR oL Ho tsk slR slL Hsl).
Notation cyc := (PolicyTDMA.TDMA_cycle tsR slR).
Notation FS t := ((t + cyc - PolicyTDMA.Task_slot_offset tsR oR tsk slR %% cyc) %% cyc).

End TWArith.

Lemma ctr_TW_WCRT_formula cyR cyL (Hcy : SubNatRel cyR cyL) sR sL (Hs : SubNatRel sR sL) wR wL (Hw : SubNatRel wR wL) :
  SubNatRel (WCRT_OneJobTDMA.WCRT_formula cyR sR wR) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_WCRT_formula cyL sL wL).
Proof.
  exact (dm_add_correspondence _ _ _ _
    (dm_mul_correspondence _ _ _ _ (dm_div_ceil_correspondence _ _ _ _ Hw Hs) (dm_sub_correspondence _ _ _ _ Hcy Hs)) Hw).
Qed.

(* ------------------------------------------------------------------ *)
(** * Section hypotheses shared by the lemmas *)

Lemma ctr_allprev (Task Job : eqType) aR aL (Ha : CtrParRel Job aR aL) cR cL (Hc : CtrParRel Job cR cL) (job_task : Job -> Task)
    arrR arrL (Harr : CtrArrRel Job arrR arrL) sR sL (Hs : CtrSchedRel Job sR sL) j :
  PropSPropRel
    (forall j_other, ArrivalSequence.arrives_in arrR j_other -> job_task j = job_task j_other ->
       aR j_other < aR j -> UniprocessorSchedule.completed_by cR sR j_other (aR j))
    (forall j_other, I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job (ct_decidable_eq Job) arrL j_other ->
       Lean.eq (job_task j) (job_task j_other) -> I.LT_lt_inst1 Lean.Nat I.instLTNat (aL j_other) (aL j) ->
       Lean.eq (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job (ct_decidable_eq Job) cL sL j_other (aL j)) I.Bool_true).
Proof.
  apply: ct_forall_identity => jo.
  apply: ct_imp; first exact (ctr_arrives_in Job arrR arrL Harr jo).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task jo)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha jo) (Ha j)).
  exact (ct_bool_truth _ _ (ctr_US_completed_by Job sR sL Hs cR cL Hc jo _ _ (Ha j))).
Qed.

Lemma ctr_TW_WCRT (Task : eqType) tcR tcL (Htc : CtrParRel Task tcR tcL) slR slL (Hsl : CtrParRel Task slR slL)
    tsR tsL (Hts : CtrSetRel Task tsR tsL) tsk :
  SubNatRel (@WCRT_OneJobTDMA.WCRT Task tcR slR tsR tsk) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_WCRT Task (ct_decidable_eq Task) tcL slL tsL tsk).
Proof.
  exact (ctr_TW_WCRT_formula _ _ (ctr_TD_TDMA_cycle Task tsR tsL Hts slR slL Hsl) _ _ (Hsl tsk) _ _ (Htc tsk)).
Qed.

(* ------------------------------------------------------------------ *)
(** * The informative reflection [TDMA_policy_case_RT_le_Period] *)

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section SCDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CtrSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (dR : Job -> nat) (dL : Job -> Lean.Nat).
Hypotheses (Ha : CtrParRel Job aR aL) (Hc : CtrParRel Job cR cL) (Hd : CtrParRel Job dR dL).

Lemma ctr_SC_job_misses_no_deadline j :
  PropSPropRel (Schedulability.job_misses_no_deadline aR cR dR sR j) (I.Prosa_Classic_Model_Schedule_Uni_Schedulability_Schedulability_job_misses_no_deadline Job dJ aL cL dL sL j).
Proof. exact (ct_bool_truth _ _ (ctr_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) (Hd j)))). Qed.

Lemma ctr_SC_task_misses_no_deadline (job_task : Job -> Task) arrR arrL (Harr : CtrArrRel Job arrR arrL) tsk :
  PropSPropRel (Schedulability.task_misses_no_deadline aR cR dR job_task arrR sR tsk)
    (I.Prosa_Classic_Model_Schedule_Uni_Schedulability_Schedulability_task_misses_no_deadline Job dJ aL cL dL Task dT job_task arrL sL tsk).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ctr_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  exact (ctr_SC_job_misses_no_deadline j).
Qed.

End SCDefs.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem ResponseTimeAnalysisTDMA_is_valid_tdma_bound_correspondence (Task : eqType) tdR tdL (Htd : CtrParRel Task tdR tdL) tsk bR bL (Hb : SubNatRel bR bL) :
  PropSPropRel (@ResponseTimeAnalysisTDMA.is_valid_tdma_bound Task tdR tsk bR) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaRtaTheory_ResponseTimeAnalysisTDMA_is_valid_tdma_bound Task (ct_decidable_eq Task) tdL tsk bL).
Proof. exact (sub_nat_le_correspondence _ _ _ _ Hb (Htd tsk)). Qed.

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
  | |- SubNatRel (?f ?x) (?g ?x) => match goal with H : CtrParRel _ f g |- _ => exact (H x) end
  end.

Ltac crel_isnat T := first [ unify T nat | unify T Lean.Nat ].

Ltac crel_intro_defs T :=
  lazymatch T with
  | ArrivalSequence.arrival_sequence _ => apply: (ctr_forall_arr _); intros ? ? ?
  | UniprocessorSchedule.schedule _ => apply: (ctr_forall_sched _); intros ? ? ?
  | PolicyTDMA.TDMA_slot _ => apply: (ctr_forall_par _); intros ? ? ?
  | PolicyTDMA.TDMA_slot_order _ => apply: (ctr_forall_ord _); intros ? ? ?
  | seqset.set_of _ => apply: (ctr_forall_set _); intros ? ? ?
  | _ => apply: ct_forall_identity; intro
  end.

Ltac crel_intro T :=
  tryif crel_isnat T then (apply: ct_forall_nat; intros ? ? ?) else
  lazymatch T with
  | ?A -> ?B => tryif crel_isnat B then (apply: ctr_forall_par; intros ? ? ?) else crel_intro_defs T
  | _ => crel_intro_defs T
  end.

Ltac crel :=
  first
  [ assumption
  | crel_hyp; crel
  | lazymatch goal with
    | |- forall _, _ => intro; crel
    | |- SubNatRel ?a _ => crel_n a
    | |- CtBoolRel ?b _ => crel_b b
    | |- ClListRel _ ?l _ => crel_l l
    | |- PropSPropRel ?P _ => crel_p P
    end ]
with crel_n a :=
  lazymatch a with
  | addn _ _ => eapply sub_add_correspondence; crel
  | subn _ _ => eapply ct_sub_rel; crel
  | S _ => eapply ctr_succ_rel; crel
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
  | _ <-> _ => eapply ctr_iff; crel
  | _ <> _ => eapply ctr_ne
  | ~ _ => eapply ct_imp; [crel | exact ctr_false_rel]
  | @Logic.eq bool _ _ => eapply ct_bool_eq; crel
  | @Logic.eq ?T _ _ => tryif crel_isnat T then (eapply sub_nat_eq_correspondence; crel) else crel_eq_defs
  | is_true (leq _ _) => first [ eapply sub_nat_lt_correspondence; crel | eapply sub_nat_le_correspondence; crel
                              | eapply ct_bool_truth; crel ]
  | is_true _ => first [ crel_p_defs | eapply ct_bool_truth; crel ]
  | _ => crel_p_defs
  end
with crel_eq_defs := first [ eapply ct_eq_rel | fail; crel ]
with crel_n_defs := first [ eapply ctr_TW_WCRT; crel
    | eapply ctr_US_service; crel
    | eapply ctr_US_service_during; crel
    | eapply ctr_US_service_at; crel ]
with crel_b_defs := first [ eapply ctr_US_completed_by; crel
    | eapply ctr_US_scheduled_at; crel
    | eapply ctr_TD_is_valid_time_slot; crel
    | eapply ctr_J_job_cost_le_task_cost; crel
    | eapply ctr_US_pending; crel
    | eapply ctr_US_backlogged; crel
    | eapply ctr_has_arrived; crel
    | eapply ctr_arrives_at; crel
    | eapply ctr_J_job_cost_positive; crel
    | eapply ctr_J_job_deadline_positive; crel
    | eapply ctr_J_job_cost_le_deadline; crel ]
with crel_l_defs := first [ fail ]
with crel_p_defs := first [ eapply ctr_arrives_in; crel
    | eapply ctr_consistent; crel
    | eapply ctr_set_mem; crel
    | eapply ctr_TA_sporadic_task_model; crel
    | eapply ctr_J_valid_sporadic_job; crel
    | eapply ctr_US_jobs_must_arrive_to_execute; crel
    | eapply ctr_US_completed_jobs_dont_execute; crel
    | eapply ctr_TDP_Respects_TDMA_policy; crel
    | eapply ctr_RT_is_response_time_bound_of_task; crel
    | eapply ctr_SC_task_misses_no_deadline; crel
    | eapply ResponseTimeAnalysisTDMA_is_valid_tdma_bound_correspondence; crel
    | eapply ctr_mem; crel
    | eapply ctr_uniq; crel
    | eapply ctr_J_valid_realtime_job; crel
    | eapply ctr_J_job_deadline_eq_task_deadline; crel
    | eapply ctr_RT_is_response_time_bound_of_job; crel ].

Ltac crel_spine :=
  repeat lazymatch goal with
  | |- PropSPropRel (forall x : ?T, _) _ =>
      lazymatch type of T with Prop => eapply ct_imp; [ crel | idtac ] | _ => crel_intro T end
  end.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_any_job_completed_before_period (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeAnalysisTDMA.any_job_completed_before_period Task p0 p1 p2 Job)).
Definition tgt_any_job_completed_before_period (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaRtaTheory_ResponseTimeAnalysisTDMA_any_job_completed_before_period Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem ResponseTimeAnalysisTDMA_any_job_completed_before_period_correspondence (Task Job : eqType) :
  PropSPropRel (src_any_job_completed_before_period Task Job) (tgt_any_job_completed_before_period Task Job).
Proof. unfold src_any_job_completed_before_period, tgt_any_job_completed_before_period. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_all_previous_jobs_of_same_task_completed (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeAnalysisTDMA.all_previous_jobs_of_same_task_completed Task p0 p1 p2 Job)).
Definition tgt_all_previous_jobs_of_same_task_completed (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaRtaTheory_ResponseTimeAnalysisTDMA_all_previous_jobs_of_same_task_completed Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem ResponseTimeAnalysisTDMA_all_previous_jobs_of_same_task_completed_correspondence (Task Job : eqType) :
  PropSPropRel (src_all_previous_jobs_of_same_task_completed Task Job) (tgt_all_previous_jobs_of_same_task_completed Task Job).
Proof. unfold src_all_previous_jobs_of_same_task_completed, tgt_all_previous_jobs_of_same_task_completed. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_uniprocessor_response_time_bound_TDMA (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeAnalysisTDMA.uniprocessor_response_time_bound_TDMA Task p0 p1 p2 Job)).
Definition tgt_uniprocessor_response_time_bound_TDMA (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaRtaTheory_ResponseTimeAnalysisTDMA_uniprocessor_response_time_bound_TDMA Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem ResponseTimeAnalysisTDMA_uniprocessor_response_time_bound_TDMA_correspondence (Task Job : eqType) :
  PropSPropRel (src_uniprocessor_response_time_bound_TDMA Task Job) (tgt_uniprocessor_response_time_bound_TDMA Task Job).
Proof. unfold src_uniprocessor_response_time_bound_TDMA, tgt_uniprocessor_response_time_bound_TDMA. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_taskset_schedulable_by_tdma (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeAnalysisTDMA.taskset_schedulable_by_tdma Task p0 p1 p2 Job)).
Definition tgt_taskset_schedulable_by_tdma (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaRtaTheory_ResponseTimeAnalysisTDMA_taskset_schedulable_by_tdma Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem ResponseTimeAnalysisTDMA_taskset_schedulable_by_tdma_correspondence (Task Job : eqType) :
  PropSPropRel (src_taskset_schedulable_by_tdma Task Job) (tgt_taskset_schedulable_by_tdma Task Job).
Proof. unfold src_taskset_schedulable_by_tdma, tgt_taskset_schedulable_by_tdma. crel_spine. crel. Unshelve. all: crel. Qed.

Definition src_jobs_schedulable_by_tdma_rta (Task Job : eqType) : Prop :=
  forall p0 p1 p2 : Task -> nat,
    ltac:(type_of_term (@ResponseTimeAnalysisTDMA.jobs_schedulable_by_tdma_rta Task p0 p1 p2 Job)).
Definition tgt_jobs_schedulable_by_tdma_rta (Task Job : eqType) : SProp :=
  forall p0 p1 p2 : Task -> Lean.Nat,
    ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaRtaTheory_ResponseTimeAnalysisTDMA_jobs_schedulable_by_tdma_rta Task (ct_decidable_eq Task) p0 p1 p2 Job (ct_decidable_eq Job))).
Theorem ResponseTimeAnalysisTDMA_jobs_schedulable_by_tdma_rta_correspondence (Task Job : eqType) :
  PropSPropRel (src_jobs_schedulable_by_tdma_rta Task Job) (tgt_jobs_schedulable_by_tdma_rta Task Job).
Proof. unfold src_jobs_schedulable_by_tdma_rta, tgt_jobs_schedulable_by_tdma_rta. crel_spine. crel. Unshelve. all: crel. Qed.
