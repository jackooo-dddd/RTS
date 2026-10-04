From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div.
From prosa Require Import util.seqset classic.model.time classic.util.list classic.util.div_mod classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.arrival.basic.task_arrival classic.model.policy_tdma classic.model.schedule.uni.schedule classic.model.schedule.uni.response_time classic.model.schedule.uni.basic.platform_tdma classic.model.schedule.uni.end_time classic.analysis.uni.basic.tdma_wcrt_analysis.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicTdmaWcrt.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicTdmaWcrtBase ClassicTdmaWcrtList.



Module I := ImportedClassicTdmaWcrt.
Local Open Scope nat_scope.

(** Certificates for [classic/analysis/uni/basic/tdma_wcrt_analysis.v] (ProsaBuddy classic, commit f692cb7).

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

Lemma ctw_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma ctw_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma ctw_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) ctw_false_rel). Qed.

Lemma ctw_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma ctw_uniq (T : eqType) s sL : ClListRel cid s sL -> PropSPropRel (uniq s) (I.List_Nodup T sL).
Proof. exact (cl_uniq_rel_list T T cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) s sL). Qed.

Lemma ctw_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma ctw_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma ctw_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma ctw_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (ctw_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => ctw_unmap_rel T l) PR PL).
Qed.

Definition CtwParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma ctw_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CtwParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (ctw_forall_cover _ _ (CtwParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint ctw_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ctw_natl s') end.

Definition ctw_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma ctw_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) ctw_one) (ctw_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) ctw_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ctw_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ctw_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma ctw_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma ctw_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma ctw_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH ctw_cl_append. reflexivity.
Qed.

Lemma ctw_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CtwFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CtwArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition ctw_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition ctw_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma ctw_arr_canonical aR : CtwArrRel aR (ctw_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /ctw_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma ctw_arr_surjective aL : CtwArrRel (ctw_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma ctw_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CtwArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (ctw_forall_cover _ _ CtwArrRel ctw_arr_to_target ctw_arr_to_source ctw_arr_canonical ctw_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma ctw_arrives_in aR aL (Ha : CtwArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (ctw_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma ctw_has_arrived pR pL (Hp : CtwParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint ctw_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (ctw_snatl s') end.

Lemma ctw_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (ctw_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (ctw_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma ctw_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ctw_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (ctw_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma ctw_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CtwFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma ctw_fun_canonical FR FL (HF : CtwFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma ctw_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma ctw_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CtwFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := ctw_nat_sub_canonical nR mR.
  rewrite ctw_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (ctw_foldr_add FL FR (ctw_fun_canonical FR FL HF)).
  by rewrite ctw_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition ctw_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition ctw_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma ctw_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma ctw_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (ctw_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CtwSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition ctw_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition ctw_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma ctw_sched_canonical sR : CtwSchedRel sR (ctw_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /ctw_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma ctw_sched_surjective sL : CtwSchedRel (ctw_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /ctw_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma ctw_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CtwSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (ctw_forall_cover _ _ CtwSchedRel ctw_sched_to_target ctw_sched_to_source ctw_sched_canonical ctw_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ctw_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CtwSchedRel Job sR (ctw_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CtwSchedRel Job (ctw_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (ctw_sched_canonical Job) (ctw_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CtwSchedRel Job sR sL.

Lemma ctw_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (ctw_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (ctw_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma ctw_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (ctw_US_scheduled_at j tR tL Ht)). Qed.

Lemma ctw_service_at_fun j : CtwFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (ctw_US_service_at j kR kL Hk). Qed.

Lemma ctw_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (ctw_ico _ _ _ _ _ _ H1 H2 (ctw_service_at_fun j)). Qed.

Lemma ctw_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (ctw_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma ctw_US_completed_by cR cL (Hc : CtwParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (ctw_US_service j tR tL Ht)). Qed.

Lemma ctw_US_pending aR aL (Ha : CtwParRel Job aR aL) cR cL (Hc : CtwParRel Job cR cL) j tR tL
    (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.pending aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_pending Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ctw_has_arrived Job aR aL Ha j tR tL Ht)
           (ct_bool_not _ _ (ctw_US_completed_by cR cL Hc j tR tL Ht))).
Qed.

Lemma ctw_US_backlogged aR aL (Ha : CtwParRel Job aR aL) cR cL (Hc : CtwParRel Job cR cL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.backlogged aR cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_backlogged Job dJ aL cL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (ctw_US_pending aR aL Ha cR cL Hc j tR tL Ht)
           (ct_bool_not _ _ (ctw_US_scheduled_at j tR tL Ht))).
Qed.

Lemma ctw_US_jobs_must_arrive_to_execute aR aL (Ha : CtwParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (ctw_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma ctw_US_completed_jobs_dont_execute cR cL (Hc : CtwParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (ctw_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma ctw_J_job_cost_positive cR cL (Hc : CtwParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma ctw_J_job_deadline_positive dR dL (Hd : CtwParRel Job dR dL) j :
  CtBoolRel (Job.job_deadline_positive dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_positive Job dJ dL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd j)). Qed.

Lemma ctw_J_job_cost_le_deadline cR cL dR dL (Hc : CtwParRel Job cR cL) (Hd : CtwParRel Job dR dL) j :
  CtBoolRel (Job.job_cost_le_deadline cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_deadline Job dJ cL dL j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Hd j)). Qed.

Lemma ctw_J_valid_realtime_job cR cL dR dL (Hc : CtwParRel Job cR cL) (Hd : CtwParRel Job dR dL) j :
  PropSPropRel (Job.valid_realtime_job cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_realtime_job Job dJ cL dL j).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (ctw_J_job_cost_positive cR cL Hc j)).
  apply: ct_and; first exact (ct_bool_truth _ _ (ctw_J_job_cost_le_deadline cR cL dR dL Hc Hd j)).
  exact (ct_bool_truth _ _ (ctw_J_job_deadline_positive dR dL Hd j)).
Qed.

Lemma ctw_J_job_cost_le_task_cost tcR tcL (Htc : CtwParRel Task tcR tcL) cR cL (Hc : CtwParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma ctw_J_job_deadline_eq_task_deadline tdR tdL (Htd : CtwParRel Task tdR tdL) dR dL (Hd : CtwParRel Job dR dL)
    (job_task : Job -> Task) j :
  PropSPropRel (Job.job_deadline_eq_task_deadline tdR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_eq_task_deadline Task dT tdL Job dJ dL job_task j).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))). Qed.

Lemma ctw_J_valid_sporadic_job tcR tcL tdR tdL (Htc : CtwParRel Task tcR tcL) (Htd : CtwParRel Task tdR tdL)
    cR cL dR dL (Hc : CtwParRel Job cR cL) (Hd : CtwParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task dT tcL tdL Job dJ cL dL job_task j).
Proof.
  apply: ct_and; first exact (ctw_J_valid_realtime_job cR cL dR dL Hc Hd j).
  apply: ct_and; first exact (ct_bool_truth _ _ (ctw_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
  exact (ctw_J_job_deadline_eq_task_deadline tdR tdL Htd dR dL Hd job_task j).
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

Lemma ctw_sum_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs) FR x) (I.Prosa_Util_Sum_sumSeq X (cl_map cid xs) FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicTdmaWcrtInterface_production_sumSeq_nil X FL)).
  - rewrite big_cons. cbn [cl_map].
    refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ClassicTdmaWcrtInterface_production_sumSeq_cons X FL x (cl_map cid xs)))).
    exact (sub_add_correspondence _ _ _ _ (HF x) IH).
Qed.

Lemma ctw_sum_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (I.Prosa_Util_Sum_sumSeq X xsL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (ctw_sum_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumSeq X l FL) _ _ Hxs)).
Qed.

Variable PR : X -> bool.
Variable PL : X -> I.Bool.
Hypothesis HP : forall x, CtBoolRel (PR x) (PL x).

Lemma ctw_sum_filtered_canonical (xs : seq X) :
  SubNatRel (\sum_(x <- xs | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X (cl_map cid xs) PL FL).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil.
    exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ClassicTdmaWcrtInterface_production_sumFiltered_nil X PL FL)).
  - rewrite big_cons. cbn [cl_map].
    have Hx := HP x. unfold CtBoolRel in Hx.
    destruct (PR x).
    + refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicTdmaWcrtInterface_production_sumFiltered_cons_true
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
      exact (sub_add_correspondence _ _ _ _ (HF x) IH).
    + exact (sub_imported_eq_trans _ _ _ IH (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ClassicTdmaWcrtInterface_production_sumFiltered_cons_false
          X PL FL x (cl_map cid xs) (sub_imported_eq_sym _ _ Hx)))).
Qed.

Lemma ctw_sum_filtered_rel xsR xsL : ClListRel cid xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (I.Prosa_Util_Sum_sumFiltered X xsL PL FL).
Proof.
  intro Hxs.
  exact (sub_imported_eq_trans _ _ _ (ctw_sum_filtered_canonical xsR)
    (sub_imported_eq_congr (fun l => I.Prosa_Util_Sum_sumFiltered X l PL FL) _ _ Hxs)).
Qed.

End TdmaSums.

(* ------------------------------------------------------------------ *)
(** * Task sets, slots and slot orders *)

Section TdmaRel.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Notation LSet := (I.Prosa_Util_Seqset_set Task dT).

Definition CtwSetRel (sR : {set Task}) (sL : LSet) : SProp :=
  ClListRel cid (@prosa.util.seqset._set_seq Task sR) (I.Prosa_Util_Seqset_set_val Task dT sL).

Lemma ctw_uniq_rel (xs : seq Task) : PropSPropRel (uniq xs) (I.List_Nodup Task (cl_map cid xs)).
Proof. exact (cl_uniq_rel Task Task cid cid (fun _ => Logic.eq_refl _) (fun _ => Logic.eq_refl _) xs). Qed.

Definition ctw_set_to_target (sR : {set Task}) : LSet :=
  match sR with
  | @prosa.util.seqset.Build_set _ xs Hu =>
      I.Prosa_Util_Seqset_set_mk Task dT (cl_map cid xs) (prop_to_sprop _ _ (ctw_uniq_rel xs) Hu)
  end.

Lemma ctw_import_uniq (xs : I.List Task) (Hn : I.List_Nodup Task xs) : uniq (cl_unmap cid xs).
Proof.
  apply (sprop_to_prop _ _ (ctw_uniq_rel (cl_unmap cid xs))).
  rewrite (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) xs). exact Hn.
Qed.

Definition ctw_set_to_source (sL : LSet) : {set Task} :=
  match sL with
  | I.Prosa_Util_Seqset_set_mk xs Hn => @prosa.util.seqset.Build_set Task (cl_unmap cid xs) (ctw_import_uniq xs Hn)
  end.

Lemma ctw_set_canonical sR : CtwSetRel sR (ctw_set_to_target sR).
Proof. destruct sR. exact (@Lean.eq_refl _ _). Qed.

Lemma ctw_set_surjective sL : CtwSetRel (ctw_set_to_source sL) sL.
Proof.
  destruct sL as [xs Hn]. unfold CtwSetRel. cbn.
  exact (coq_eq_to_imported_eq _ _ (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) xs)).
Qed.

Lemma ctw_forall_set (PR : {set Task} -> Prop) (PL : LSet -> SProp) :
  (forall sR sL, CtwSetRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (ctw_forall_cover _ _ CtwSetRel ctw_set_to_target ctw_set_to_source ctw_set_canonical ctw_set_surjective PR PL). Qed.

Lemma ctw_set_mem x sR sL (Hs : CtwSetRel sR sL) :
  PropSPropRel (x \in sR) (I.Membership_mem Task LSet (I.Prosa_Util_Seqset_instMembershipSet Task dT) sL x).
Proof. exact (cl_mem_rel_list Task Task cid cid (fun _ => Logic.eq_refl _) x _ _ Hs). Qed.

Definition CtwOrdRel (oR : rel Task) (oL : Task -> Task -> I.Bool) : SProp := forall a b, CtBoolRel (oR a b) (oL a b).

Definition ctw_ord_to_target (oR : rel Task) : Task -> Task -> I.Bool := fun a b => ct_b2l (oR a b).
Definition ctw_ord_to_source (oL : Task -> Task -> I.Bool) : rel Task := fun a b => ct_l2b (oL a b).

Lemma ctw_ord_canonical oR : CtwOrdRel oR (ctw_ord_to_target oR).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma ctw_ord_surjective oL : CtwOrdRel (ctw_ord_to_source oL) oL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma ctw_forall_ord (PR : rel Task -> Prop) (PL : (Task -> Task -> I.Bool) -> SProp) :
  (forall oR oL, CtwOrdRel oR oL -> PropSPropRel (PR oR) (PL oL)) -> PropSPropRel (forall o, PR o) (forall o, PL o).
Proof. exact (ctw_forall_cover _ _ CtwOrdRel ctw_ord_to_target ctw_ord_to_source ctw_ord_canonical ctw_ord_surjective PR PL). Qed.

Lemma ctw_neq x y : CtBoolRel (x != y) (I.Bool_not (I.Decidable_decide (Lean.eq x y) (dT x y))).
Proof. exact (ct_bool_not _ _ (ct_decide_eq Task x y)). Qed.

End TdmaRel.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section TdmaDefs.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).

Lemma ctw_TD_TDMA_slot :
  And (forall sR : PolicyTDMA.TDMA_slot Task, CtwParRel Task sR (fun x => sub_nat_to_imported (sR x)))
      (forall sL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT, CtwParRel Task (fun x => sub_nat_to_rocq (sL x)) sL).
Proof.
  exact (And_intro _ _ (fun sR x => sub_nat_rel_canonical (sR x)) (fun sL x => sub_nat_rel_surjective (sL x))).
Qed.

Lemma ctw_TD_TDMA_slot_order :
  And (forall oR : PolicyTDMA.TDMA_slot_order Task, CtwOrdRel Task oR (ctw_ord_to_target Task oR))
      (forall oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT, CtwOrdRel Task (ctw_ord_to_source Task oL) oL).
Proof. exact (And_intro _ _ (ctw_ord_canonical Task) (ctw_ord_surjective Task)). Qed.

Lemma ctw_TD_is_valid_time_slot task slR slL (Hsl : CtwParRel Task slR slL) :
  CtBoolRel (PolicyTDMA.is_valid_time_slot task slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_is_valid_time_slot Task dT task slL).
Proof. exact (ct_decide_lt _ _ _ _ (sub_nat_rel_canonical 0) (Hsl task)). Qed.

Lemma ctw_TD_TDMA_cycle sR sL (Hs : CtwSetRel Task sR sL) slR slL (Hsl : CtwParRel Task slR slL) :
  SubNatRel (PolicyTDMA.TDMA_cycle sR slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_cycle Task dT sL slL).
Proof. exact (ctw_sum_rel Task slR slL Hsl _ _ Hs). Qed.

Lemma ctw_TD_Task_slot_offset sR sL (Hs : CtwSetRel Task sR sL) oR oL (Ho : CtwOrdRel Task oR oL)
    task slR slL (Hsl : CtwParRel Task slR slL) :
  SubNatRel (PolicyTDMA.Task_slot_offset sR oR task slR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_slot_offset Task dT sL oL task slL).
Proof.
  exact (ctw_sum_filtered_rel Task slR slL Hsl _
    (fun p => I.Bool_and (oL p task) (I.Bool_not (I.Decidable_decide (Lean.eq p task) (dT p task))))
    (fun p => ct_bool_and _ _ _ _ (Ho p task) (ctw_neq Task p task)) _ _ Hs).
Qed.

Lemma ctw_TD_Task_in_time_slot sR sL (Hs : CtwSetRel Task sR sL) oR oL (Ho : CtwOrdRel Task oR oL)
    task slR slL (Hsl : CtwParRel Task slR slL) tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (PolicyTDMA.Task_in_time_slot sR oR task slR tR) (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_in_time_slot Task dT sL oL task slL tL).
Proof.
  have HC := ctw_TD_TDMA_cycle sR sL Hs slR slL Hsl.
  have HO := ctw_TD_Task_slot_offset sR sL Hs oR oL Ho task slR slL Hsl.
  apply: ct_decide_lt; last exact (Hsl task).
  apply: dm_mod_correspondence; last exact HC.
  apply: dm_sub_correspondence; last exact (dm_mod_correspondence _ _ _ _ HO HC).
  exact (sub_add_correspondence _ _ _ _ Ht HC).
Qed.

End TdmaDefs.

Lemma ctw_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

Lemma ctw_iff (P Q : Prop) (PL QL : SProp) :
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

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section TDPDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CtwSchedRel Job sR sL.
Variables (tsR : {set Task}) (tsL : I.Prosa_Util_Seqset_set Task dT).
Hypothesis Hts : CtwSetRel Task tsR tsL.
Variables (slR : PolicyTDMA.TDMA_slot Task) (slL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT).
Hypothesis Hsl : CtwParRel Task slR slL.
Variables (oR : PolicyTDMA.TDMA_slot_order Task) (oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT).
Hypothesis Ho : CtwOrdRel Task oR oL.
Variable job_task : Job -> Task.

Lemma ctw_in_slot j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (PolicyTDMA.Task_in_time_slot tsR oR (job_task j) slR tR)
    (I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_Task_in_time_slot Task dT tsL oL (job_task j) slL tL).
Proof. exact (ctw_TD_Task_in_time_slot Task tsR tsL Hts oR oL Ho (job_task j) slR slL Hsl tR tL Ht). Qed.

Lemma ctw_TDP_sched_implies_in_slot j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (Platform_TDMA.sched_implies_in_slot job_task sR tsR slR oR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_sched_implies_in_slot Task dT Job dJ job_task sL tsL slL oL j tL).
Proof.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (ctw_in_slot j tR tL Ht)).
Qed.

Lemma ctw_TDP_backlogged_implies_not_in_slot_or_other_job_sched aR aL (Ha : CtwParRel Job aR aL)
    cR cL (Hc : CtwParRel Job cR cL) arrR arrL (Harr : CtwArrRel Job arrR arrL) j tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (Platform_TDMA.backlogged_implies_not_in_slot_or_other_job_sched aR cR job_task arrR sR tsR slR oR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_backlogged_implies_not_in_slot_or_other_job_sched Task dT Job dJ aL cL job_task arrL sL tsL slL oL j tL).
Proof.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_backlogged Job sR sL Hs aR aL Ha cR cL Hc j tR tL Ht)).
  apply: ct_or.
  - apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_in_slot j tR tL Ht)).
    exact ctw_false_rel.
  - apply: ct_exists_identity => j_other.
    apply: ct_and; first exact (ctw_arrives_in Job arrR arrL Harr j_other).
    apply: ct_and; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha j_other) (Ha j)).
    apply: ct_and; first exact (ct_eq_rel Task (job_task j) (job_task j_other)).
    exact (ct_bool_truth _ _ (ctw_US_scheduled_at Job sR sL Hs j_other tR tL Ht)).
Qed.

Lemma ctw_TDP_Respects_TDMA_policy aR aL (Ha : CtwParRel Job aR aL)
    cR cL (Hc : CtwParRel Job cR cL) arrR arrL (Harr : CtwArrRel Job arrR arrL) :
  PropSPropRel (Platform_TDMA.Respects_TDMA_policy aR cR job_task arrR sR tsR slR oR)
    (I.Prosa_Classic_Model_Schedule_Uni_Basic_PlatformTdma_Platform_TDMA_Respects_TDMA_policy Task dT Job dJ aL cL job_task arrL sL tsL slL oL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_and; first exact (ctw_TDP_sched_implies_in_slot j tR tL Ht).
  exact (ctw_TDP_backlogged_implies_not_in_slot_or_other_job_sched aR aL Ha cR cL Hc arrR arrL Harr j tR tL Ht).
Qed.

End TDPDefs.

(* ------------------------------------------------------------------ *)
(** * [diagnosis_option] (constructor-wise, related instants) *)

Notation nc := sub_nat_to_imported.
Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Definition ctw_dg_to_target (d : end_time.diagnosis_option) : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option :=
  match d with
  | end_time.OK t => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK (nc t)
  | end_time.Failure t => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_Failure (nc t)
  end.
Definition ctw_dg_to_source (d : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option) : end_time.diagnosis_option :=
  match d with
  | I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK t => end_time.OK (sub_nat_to_rocq t)
  | I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_Failure t => end_time.Failure (sub_nat_to_rocq t)
  end.
Definition CtwDgRel (dR : end_time.diagnosis_option) (dL : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option) : SProp :=
  Lean.eq (ctw_dg_to_target dR) dL.

Lemma ctw_dg_ts d : Logic.eq (ctw_dg_to_source (ctw_dg_to_target d)) d.
Proof. case: d => t /=; by rewrite sub_nat_rocq_roundtrip. Qed.

Lemma ctw_dg_eq dR1 dL1 dR2 dL2 (H1 : CtwDgRel dR1 dL1) (H2 : CtwDgRel dR2 dL2) :
  PropSPropRel (Logic.eq dR1 dR2) (Lean.eq dL1 dL2).
Proof.
  rewrite -(EQ H1) -(EQ H2). clear H1 H2. apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := f_equal ctw_dg_to_source (EQ E). by rewrite !ctw_dg_ts in E'.
Qed.

Lemma ctw_OK tR tL (Ht : SubNatRel tR tL) : CtwDgRel (end_time.OK tR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK tL).
Proof. exact (sub_imported_eq_congr (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK) _ _ Ht). Qed.

Lemma ctw_not_rel (P : Prop) (PL : SProp) : PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof. intro H. exact (ct_imp _ _ _ _ H ctw_false_rel). Qed.

(* ------------------------------------------------------------------ *)
(** * [end_time_option] and [end_time_predicate] *)

Section ETEndTime.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CtwSchedRel Job sR sL.
Variable job : Job.
Notation SA := (ctw_US_scheduled_at Job sR sL Hs job).

Lemma ctw_etp_fwd tR cR eR :
  end_time.end_time_predicate sR job tR cR eR -> I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job dJ sL job (nc tR) (nc cR) (nc eR).
Proof.
  intro H.
  refine (end_time.end_time_predicate_sind sR job (fun t c e => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job dJ sL job (nc t) (nc c) (nc e)) _ _ _ tR cR eR H).
  - intro t. exact (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate_C0_ Job dJ sL job (nc t)).
  - intros t c e Hn _ IH. exact (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate_S_C_not_sched Job dJ sL job (nc t) (nc c) (nc e)
      (prop_to_sprop _ _ (ctw_not_rel _ _ (ct_bool_truth _ _ (SA t _ (sub_nat_rel_canonical t)))) Hn) IH).
  - intros t c e Hy _ IH. exact (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate_S_C_sched Job dJ sL job (nc t) (nc c) (nc e)
      (prop_to_sprop _ _ (ct_bool_truth _ _ (SA t _ (sub_nat_rel_canonical t))) Hy) IH).
Qed.

Lemma ctw_back_rel tL : SubNatRel (sub_nat_to_rocq tL) tL.
Proof. exact (sub_nat_imported_roundtrip tL). Qed.

Lemma ctw_etp_bwd tL cL eL :
  I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job dJ sL job tL cL eL ->
  StrictlyInhabited (end_time.end_time_predicate sR job (sub_nat_to_rocq tL) (sub_nat_to_rocq cL) (sub_nat_to_rocq eL)).
Proof.
  intro H. induction H as [t | t c e Hn _ IH | t c e Hy _ IH].
  - exact (strictly_inhabits (end_time.C0_ sR job (sub_nat_to_rocq t))).
  - exact (match IH with strictly_inhabits p =>
      strictly_inhabits (end_time.S_C_not_sched sR job (sub_nat_to_rocq t) (sub_nat_to_rocq c) (sub_nat_to_rocq e)
        (sprop_to_prop _ _ (ctw_not_rel _ _ (ct_bool_truth _ _ (SA _ _ (ctw_back_rel t)))) Hn) p) end).
  - exact (match IH with strictly_inhabits p =>
      strictly_inhabits (end_time.S_C_sched sR job (sub_nat_to_rocq t) (sub_nat_to_rocq c) (sub_nat_to_rocq e)
        (sprop_to_prop _ _ (ct_bool_truth _ _ (SA _ _ (ctw_back_rel t))) Hy) p) end).
Qed.

Lemma ctw_etp tR tL (Ht : SubNatRel tR tL) cR cL (Hc : SubNatRel cR cL) eR eL (He : SubNatRel eR eL) :
  PropSPropRel (end_time.end_time_predicate sR job tR cR eR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job dJ sL job tL cL eL).
Proof.
  have Et := cl_nat_logic _ _ Ht. have Ec := cl_nat_logic _ _ Hc. have Ee := cl_nat_logic _ _ He. subst tL cL eL.
  apply prop_sprop_rel_intro; first exact (ctw_etp_fwd tR cR eR).
  intro H. have S := ctw_etp_bwd _ _ _ H. rewrite !sub_nat_rocq_roundtrip in S. exact S.
Qed.

End ETEndTime.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma ctw_dg_st d : Logic.eq (ctw_dg_to_target (ctw_dg_to_source d)) d.
Proof.
  case: d => t /=; by rewrite (EQ (sub_nat_imported_roundtrip t)).
Qed.

(** The inductive [diagnosis_option]: the constructor-wise relation is total in both directions. *)
Lemma ctw_ET_diagnosis_option :
  And (forall dR : end_time.diagnosis_option, CtwDgRel dR (ctw_dg_to_target dR))
      (forall dL : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option, CtwDgRel (ctw_dg_to_source dL) dL).
Proof.
  exact (And_intro _ _ (fun dR => @Lean.eq_refl _ _) (fun dL => coq_eq_to_imported_eq _ _ (ctw_dg_st dL))).
Qed.

(** The inductive [end_time_predicate]: equivalent at related inputs (both directions by induction). *)
Lemma ctw_ET_end_time_predicate (Job : eqType) sR sL (Hs : CtwSchedRel Job sR sL) job
    tR tL (Ht : SubNatRel tR tL) cR cL (Hc : SubNatRel cR cL) eR eL (He : SubNatRel eR eL) :
  PropSPropRel (@end_time.end_time_predicate Job sR job tR cR eR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job (ct_decidable_eq Job) sL job tL cL eL).
Proof. exact (ctw_etp Job sR sL Hs job _ _ Ht _ _ Hc _ _ He). Qed.

Lemma ctw_ET_completes_at (Job : eqType) aR aL (Ha : CtwParRel Job aR aL) cR cL (Hc : CtwParRel Job cR cL)
    sR sL (Hs : CtwSchedRel Job sR sL) job tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@end_time.completes_at Job aR cR sR job tR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_completes_at Job (ct_decidable_eq Job) aL cL sL job tL).
Proof. exact (ctw_etp Job sR sL Hs job _ _ (Ha job) _ _ (Hc job) _ _ Ht). Qed.

(* ------------------------------------------------------------------ *)
(** * Conditionals *)

(** A Lean [ite] on a decidable proposition against a Rocq Boolean [if], given the relation of the
    Boolean test to the proposition (any decision procedure). *)
Lemma ctw_ite_nat (bR : bool) (P : SProp) (d : I.Decidable P) (H : PropSPropRel (is_true bR) P)
    xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR) (I.ite Lean.Nat P d xL yL).
Proof.
  destruct d as [Hf | Ht]; destruct bR; cbn.
  - exact (ct_false_elim _ (Hf (prop_to_sprop _ _ H (Logic.eq_refl true)))).
  - exact Hy.
  - exact Hx.
  - exact (ct_false_elim _ (ct_coq_false_to_target (match sprop_to_prop _ _ H Ht with end))).
Qed.

Lemma ctw_eqn0 nR nL (Hn : SubNatRel nR nL) :
  PropSPropRel (is_true (nR == 0)) (Lean.eq nL (I.OfNat_ofNat_inst1 Lean.Nat 0 (I.instOfNatNat 0))).
Proof.
  have E := sub_nat_eq_correspondence _ _ _ _ Hn (sub_nat_rel_canonical 0).
  apply prop_sprop_rel_intro.
  - move=> /eqP H. exact (prop_to_sprop _ _ E H).
  - intro H. apply strictly_inhabits. apply/eqP. exact (sprop_to_prop _ _ E H).
Qed.

(* ------------------------------------------------------------------ *)
(** * The section-local arithmetic [Let]s (Lean [LEAN_HELPER] definitions) *)

Section Arith.
Variable Task : eqType.
Notation dT := (ct_decidable_eq Task).
Variables (tsR : {set Task}) (tsL : I.Prosa_Util_Seqset_set Task dT).
Hypothesis Hts : CtwSetRel Task tsR tsL.
Variables (slR : PolicyTDMA.TDMA_slot Task) (slL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot Task dT).
Hypothesis Hsl : CtwParRel Task slR slL.
Variables (oR : PolicyTDMA.TDMA_slot_order Task) (oL : I.Prosa_Classic_Model_PolicyTdma_PolicyTDMA_TDMA_slot_order Task dT).
Hypothesis Ho : CtwOrdRel Task oR oL.
Variable tsk : Task.
Notation HC := (ctw_TD_TDMA_cycle Task tsR tsL Hts slR slL Hsl).
Notation HO := (ctw_TD_Task_slot_offset Task tsR tsL Hts oR oL Ho tsk slR slL Hsl).
Notation cyc := (PolicyTDMA.TDMA_cycle tsR slR).
Notation FS t := ((t + cyc - PolicyTDMA.Task_slot_offset tsR oR tsk slR %% cyc) %% cyc).

Lemma ctw_FS tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (FS tR) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_from_start_of_slot Task dT slL oL tsL tsk tL).
Proof.
  exact (dm_mod_correspondence _ _ _ _
    (dm_sub_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht HC) (dm_mod_correspondence _ _ _ _ HO HC)) HC).
Qed.

Lemma ctw_TNS tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (cyc - FS tR) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_to_next_slot Task dT slL oL tsL tsk tL).
Proof. exact (dm_sub_correspondence _ _ _ _ HC (ctw_FS _ _ Ht)). Qed.

Lemma ctw_TES tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (slR tsk - FS tR) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_to_end_of_slot Task dT slL oL tsL tsk tL).
Proof. exact (dm_sub_correspondence _ _ _ _ (Hsl tsk) (ctw_FS _ _ Ht)). Qed.

Lemma ctw_DUR cR cL (Hc : SubNatRel cR cL) :
  SubNatRel ((div_ceil cR (slR tsk) - 1) * (cyc - slR tsk) + cR)
    (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_duration_to_finish_from_start_of_slot_with Task dT slL tsL tsk cL).
Proof.
  exact (dm_add_correspondence _ _ _ _
    (dm_mul_correspondence _ _ _ _
      (dm_sub_correspondence _ _ _ _ (dm_div_ceil_correspondence _ _ _ _ Hc (Hsl tsk)) (sub_nat_rel_canonical 1))
      (dm_sub_correspondence _ _ _ _ HC (Hsl tsk))) Hc).
Qed.

Theorem WCRT_OneJobTDMA_formula_rt_correspondence aR aL (Ha : SubNatRel aR aL) cR cL (Hc : SubNatRel cR cL) :
  SubNatRel (@WCRT_OneJobTDMA.formula_rt Task slR oR tsR tsk aR cR) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_formula_rt Task dT slL oL tsL tsk aL cL).
Proof.
  have HIN := ctw_TD_Task_in_time_slot Task tsR tsL Hts oR oL Ho tsk slR slL Hsl aR aL Ha.
  apply: ctw_ite_nat; [exact (ctw_eqn0 _ _ Hc) | exact (sub_nat_rel_canonical 0) |].
  apply: ctw_ite_nat; [exact (ct_bool_truth _ _ HIN) | |].
  - apply: ctw_ite_nat; [exact (sub_nat_le_correspondence _ _ _ _ Hc (ctw_TES _ _ Ha)) | exact Hc |].
    exact (sub_add_correspondence _ _ _ _ (ctw_TNS _ _ Ha) (ctw_DUR _ _ (dm_sub_correspondence _ _ _ _ Hc (ctw_TES _ _ Ha)))).
  - exact (sub_add_correspondence _ _ _ _ (ctw_TNS _ _ Ha) (ctw_DUR _ _ Hc)).
Qed.

End Arith.

Theorem WCRT_OneJobTDMA_WCRT_formula_correspondence cyR cyL (Hcy : SubNatRel cyR cyL) sR sL (Hs : SubNatRel sR sL) wR wL (Hw : SubNatRel wR wL) :
  SubNatRel (WCRT_OneJobTDMA.WCRT_formula cyR sR wR) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_WCRT_formula cyL sL wL).
Proof.
  exact (dm_add_correspondence _ _ _ _
    (dm_mul_correspondence _ _ _ _ (dm_div_ceil_correspondence _ _ _ _ Hw Hs) (dm_sub_correspondence _ _ _ _ Hcy Hs)) Hw).
Qed.

(* ------------------------------------------------------------------ *)
(** * Section hypotheses shared by the lemmas *)

Lemma ctw_allprev (Task Job : eqType) aR aL (Ha : CtwParRel Job aR aL) cR cL (Hc : CtwParRel Job cR cL) (job_task : Job -> Task)
    arrR arrL (Harr : CtwArrRel Job arrR arrL) sR sL (Hs : CtwSchedRel Job sR sL) j :
  PropSPropRel
    (forall j_other, ArrivalSequence.arrives_in arrR j_other -> job_task j = job_task j_other ->
       aR j_other < aR j -> UniprocessorSchedule.completed_by cR sR j_other (aR j))
    (forall j_other, I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job (ct_decidable_eq Job) arrL j_other ->
       Lean.eq (job_task j) (job_task j_other) -> I.LT_lt_inst1 Lean.Nat I.instLTNat (aL j_other) (aL j) ->
       Lean.eq (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job (ct_decidable_eq Job) cL sL j_other (aL j)) I.Bool_true).
Proof.
  apply: ct_forall_identity => jo.
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr jo).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task jo)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha jo) (Ha j)).
  exact (ct_bool_truth _ _ (ctw_US_completed_by Job sR sL Hs cR cL Hc jo _ _ (Ha j))).
Qed.

Theorem WCRT_OneJobTDMA_job_response_time_tdma_in_at_most_one_job_is_pending_correspondence (Task Job : eqType)
    aR aL (Ha : CtwParRel Job aR aL) cR cL (Hc : CtwParRel Job cR cL)
    tsR tsL (Hts : CtwSetRel Task tsR tsL) slR slL (Hsl : CtwParRel Task slR slL) oR oL (Ho : CtwOrdRel Task oR oL) tsk j :
  SubNatRel (@WCRT_OneJobTDMA.job_response_time_tdma_in_at_most_one_job_is_pending Task Job aR cR slR oR tsR tsk j)
    (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_job_response_time_tdma_in_at_most_one_job_is_pending Task (ct_decidable_eq Task) Job (ct_decidable_eq Job) aL cL slL oL tsL tsk j).
Proof. exact (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (Ha j) _ _ (Hc j)). Qed.

Theorem WCRT_OneJobTDMA_WCRT_correspondence (Task : eqType) tcR tcL (Htc : CtwParRel Task tcR tcL) slR slL (Hsl : CtwParRel Task slR slL)
    tsR tsL (Hts : CtwSetRel Task tsR tsL) tsk :
  SubNatRel (@WCRT_OneJobTDMA.WCRT Task tcR slR tsR tsk) (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_WCRT Task (ct_decidable_eq Task) tcL slL tsL tsk).
Proof.
  exact (WCRT_OneJobTDMA_WCRT_formula_correspondence _ _ (ctw_TD_TDMA_cycle Task tsR tsL Hts slR slL Hsl) _ _ (Hsl tsk) _ _ (Htc tsk)).
Qed.

(* ------------------------------------------------------------------ *)
(** * The informative reflection [TDMA_policy_case_RT_le_Period] *)

Definition ctw_reflect_forward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    reflect PR bR -> I.Prosa_Classic_Util_List_BoolReflect PL bL.
Proof.
  destruct Hb. intro HR. destruct HR as [Htrue | Hfalse].
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isTrue PL (prop_to_sprop _ _ HP Htrue)).
  - exact (I.Prosa_Classic_Util_List_BoolReflect_isFalse PL
      (fun HL => ct_coq_false_to_target (Hfalse (sprop_to_prop _ _ HP HL)))).
Defined.

Definition ctw_reflect_backward_at_bool (PR : Prop) (PL : SProp) (HP : PropSPropRel PR PL) (bL : I.Bool) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR (ct_l2b bL) :=
  fun HL =>
    match HL in I.Prosa_Classic_Util_List_BoolReflect _ b return reflect PR (ct_l2b b) with
    | I.Prosa_Classic_Util_List_BoolReflect_isTrue Htrue => ReflectT PR (sprop_to_prop _ _ HP Htrue)
    | I.Prosa_Classic_Util_List_BoolReflect_isFalse Hfalse =>
        ReflectF PR (fun HR => interpret_strict Logic.False
          (ct_target_false_to_strict (Hfalse (prop_to_sprop _ _ HP HR))))
    end.

Definition ctw_reflect_backward (PR : Prop) (PL : SProp) (bR : bool) (bL : I.Bool)
    (HP : PropSPropRel PR PL) (Hb : CtBoolRel bR bL) :
    I.Prosa_Classic_Util_List_BoolReflect PL bL -> reflect PR bR.
Proof. destruct Hb. destruct bR; cbn; exact (ctw_reflect_backward_at_bool PR PL HP _). Defined.

(** [TDMA_policy_case_RT_le_Period] is an informative reflection (a [reflect] value); it is related by
    constructor-preserving maps in both directions, at related inputs obtained from the two-way totals of every
    input relation. *)
Definition src_TDMA_policy_case_RT_le_Period (Task Job : eqType) : Type :=
  ltac:(let X := type of (@WCRT_OneJobTDMA.TDMA_policy_case_RT_le_Period Task Job) in exact X).
Definition tgt_TDMA_policy_case_RT_le_Period (Task Job : eqType) : Type :=
  ltac:(let X := type of (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_TDMA_policy_case_RT_le_Period Task (ct_decidable_eq Task) Job (ct_decidable_eq Job)) in exact X).

Theorem WCRT_OneJobTDMA_TDMA_policy_case_RT_le_Period_correspondence (Task Job : eqType) :
  Datatypes.prod (src_TDMA_policy_case_RT_le_Period Task Job -> tgt_TDMA_policy_case_RT_le_Period Task Job)
                 (tgt_TDMA_policy_case_RT_le_Period Task Job -> src_TDMA_policy_case_RT_le_Period Task Job).
Proof.
  unfold src_TDMA_policy_case_RT_le_Period, tgt_TDMA_policy_case_RT_le_Period. split.
  - intros f aL cL job_task arrL sL HmustL HcjdL slL oL tsL tsk j HjtL HarrL HtdmaL HallL tL HpL.
    pose aR := fun x => sub_nat_to_rocq (aL x). pose cR := fun x => sub_nat_to_rocq (cL x).
    pose slR := fun x => sub_nat_to_rocq (slL x).
    have Ha : CtwParRel Job aR aL := fun x => sub_nat_rel_surjective (aL x).
    have Hc : CtwParRel Job cR cL := fun x => sub_nat_rel_surjective (cL x).
    have Hsl : CtwParRel Task slR slL := fun x => sub_nat_rel_surjective (slL x).
    have Harr := ctw_arr_surjective Job arrL. have Hs := ctw_sched_surjective Job sL.
    have Ho := ctw_ord_surjective Task oL. have Hts := ctw_set_surjective Task tsL.
    have Ht := sub_nat_rel_surjective tL.
    have HmustR := sprop_to_prop _ _ (ctw_US_jobs_must_arrive_to_execute Job _ _ Hs aR aL Ha) HmustL.
    have HcjdR := sprop_to_prop _ _ (ctw_US_completed_jobs_dont_execute Job _ _ Hs cR cL Hc) HcjdL.
    have HjtR := sprop_to_prop _ _ (ct_eq_rel Task (job_task j) tsk) HjtL.
    have HarrR := sprop_to_prop _ _ (ctw_arrives_in Job _ _ Harr j) HarrL.
    have HtdmaR := sprop_to_prop _ _ (ctw_TDP_Respects_TDMA_policy Task Job _ _ Hs _ _ Hts _ _ Hsl _ _ Ho job_task aR aL Ha cR cL Hc _ _ Harr) HtdmaL.
    have HallR := sprop_to_prop _ _ (ctw_allprev Task Job aR aL Ha cR cL Hc job_task _ _ Harr _ _ Hs j) HallL.
    have HpR := sprop_to_prop _ _ (ct_bool_truth _ _ (ctw_US_pending Job _ _ Hs aR aL Ha cR cL Hc j _ _ Ht)) HpL.
    exact (ctw_reflect_forward _ _ _ _
      (ct_bool_truth _ _ (ctw_TD_Task_in_time_slot Task _ _ Hts _ _ Ho tsk _ _ Hsl _ _ Ht))
      (ctw_US_scheduled_at Job _ _ Hs j _ _ Ht)
      (f aR cR job_task _ _ HmustR HcjdR slR _ _ tsk j HjtR HarrR HtdmaR HallR _ HpR)).
  - intros g aR cR job_task arrR sR HmustR HcjdR slR oR tsR tsk j HjtR HarrR HtdmaR HallR tR HpR.
    have Ha : CtwParRel Job aR (fun x => sub_nat_to_imported (aR x)) := fun x => sub_nat_rel_canonical (aR x).
    have Hc : CtwParRel Job cR (fun x => sub_nat_to_imported (cR x)) := fun x => sub_nat_rel_canonical (cR x).
    have Hsl : CtwParRel Task slR (fun x => sub_nat_to_imported (slR x)) := fun x => sub_nat_rel_canonical (slR x).
    have Harr := ctw_arr_canonical Job arrR. have Hs := ctw_sched_canonical Job sR.
    have Ho := ctw_ord_canonical Task oR. have Hts := ctw_set_canonical Task tsR.
    have Ht := sub_nat_rel_canonical tR.
    have HmustL := prop_to_sprop _ _ (ctw_US_jobs_must_arrive_to_execute Job _ _ Hs aR _ Ha) HmustR.
    have HcjdL := prop_to_sprop _ _ (ctw_US_completed_jobs_dont_execute Job _ _ Hs cR _ Hc) HcjdR.
    have HjtL := prop_to_sprop _ _ (ct_eq_rel Task (job_task j) tsk) HjtR.
    have HarrL := prop_to_sprop _ _ (ctw_arrives_in Job _ _ Harr j) HarrR.
    have HtdmaL := prop_to_sprop _ _ (ctw_TDP_Respects_TDMA_policy Task Job _ _ Hs _ _ Hts _ _ Hsl _ _ Ho job_task aR _ Ha cR _ Hc _ _ Harr) HtdmaR.
    have HallL := prop_to_sprop _ _ (ctw_allprev Task Job aR _ Ha cR _ Hc job_task _ _ Harr _ _ Hs j) HallR.
    have HpL := prop_to_sprop _ _ (ct_bool_truth _ _ (ctw_US_pending Job _ _ Hs aR _ Ha cR _ Hc j _ _ Ht)) HpR.
    exact (ctw_reflect_backward _ _ _ _
      (ct_bool_truth _ _ (ctw_TD_Task_in_time_slot Task _ _ Hts _ _ Ho tsk _ _ Hsl _ _ Ht))
      (ctw_US_scheduled_at Job _ _ Hs j _ _ Ht)
      (g _ _ job_task _ _ HmustL HcjdL _ _ _ tsk j HjtL HarrL HtdmaL HallL _ HpL)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_at_most_one_job_is_pending (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.at_most_one_job_is_pending Task Job)).
Definition tgt_at_most_one_job_is_pending (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_at_most_one_job_is_pending Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_at_most_one_job_is_pending_correspondence (Task Job : eqType) :
  PropSPropRel (src_at_most_one_job_is_pending Task Job) (tgt_at_most_one_job_is_pending Task Job).
Proof.
  unfold src_at_most_one_job_is_pending, tgt_at_most_one_job_is_pending.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_identity => jo.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr jo).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (Ha jo) (Ha j)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc jo _ _ Ht)).
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) (job_task jo)).
  exact (ct_eq_rel Job j jo).
Qed.

Definition src_pendingArrival (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> nat, ltac:(type_of_term (@WCRT_OneJobTDMA.pendingArrival Task task_cost task_deadline Job)).
Definition tgt_pendingArrival (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_pendingArrival Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_pendingArrival_correspondence (Task Job : eqType) :
  PropSPropRel (src_pendingArrival Task Job) (tgt_pendingArrival Task Job).
Proof.
  unfold src_pendingArrival, tgt_pendingArrival.
  apply: (ctw_forall_par Task) => tcR tcL Htc.
  apply: (ctw_forall_par Task) => tdR tdL Htd.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: (ctw_forall_par Job) => dR dL Hd.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ctw_J_valid_sporadic_job Task Job tcR tcL tdR tdL Htc Htd cR cL dR dL Hc Hd job_task j).
  exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ (Ha j))).
Qed.

Definition src_pendingSt (Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.pendingSt Job)).
Definition tgt_pendingSt (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_pendingSt Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_pendingSt_correspondence (Job : eqType) :
  PropSPropRel (src_pendingSt Job) (tgt_pendingSt Job).
Proof.
  unfold src_pendingSt, tgt_pendingSt.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ (ctw_succ_rel _ _ Ht))).
Qed.

Definition src_pendingSt_Sched (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.pendingSt_Sched Task Job)).
Definition tgt_pendingSt_Sched (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_pendingSt_Sched Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_pendingSt_Sched_correspondence (Task Job : eqType) :
  PropSPropRel (src_pendingSt_Sched Task Job) (tgt_pendingSt_Sched Task Job).
Proof.
  unfold src_pendingSt_Sched, tgt_pendingSt_Sched.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (ctw_US_service Job sR sL Hs j _ _ Ht) (ctw_succ_rel _ _ (ctw_succ_rel _ _ Hc'))) (Hc j)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ (ctw_succ_rel _ _ Ht))).
Qed.

Definition src_to_next_slot_pos (Task : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.to_next_slot_pos Task)).
Definition tgt_to_next_slot_pos (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_to_next_slot_pos Task (ct_decidable_eq Task))).
Theorem WCRT_OneJobTDMA_to_next_slot_pos_correspondence (Task : eqType) :
  PropSPropRel (src_to_next_slot_pos Task) (tgt_to_next_slot_pos Task).
Proof.
  unfold src_to_next_slot_pos, tgt_to_next_slot_pos.
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
Qed.

Definition src_lt_to_next_slot_1LR (Task : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.lt_to_next_slot_1LR Task)).
Definition tgt_lt_to_next_slot_1LR (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_lt_to_next_slot_1LR Task (ct_decidable_eq Task))).
Theorem WCRT_OneJobTDMA_lt_to_next_slot_1LR_correspondence (Task : eqType) :
  PropSPropRel (src_lt_to_next_slot_1LR Task) (tgt_lt_to_next_slot_1LR Task).
Proof.
  unfold src_lt_to_next_slot_1LR, tgt_lt_to_next_slot_1LR.
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_forall_nat => aR' aL' Ha'.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (ctw_succ_rel _ _ Ha') (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
  exact (sub_nat_lt_correspondence _ _ _ _ Ha' (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (ctw_succ_rel _ _ Ht))).
Qed.

Definition src_lt_to_next_slot_LR (Task : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.lt_to_next_slot_LR Task)).
Definition tgt_lt_to_next_slot_LR (Task : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_lt_to_next_slot_LR Task (ct_decidable_eq Task))).
Theorem WCRT_OneJobTDMA_lt_to_next_slot_LR_correspondence (Task : eqType) :
  PropSPropRel (src_lt_to_next_slot_LR Task) (tgt_lt_to_next_slot_LR Task).
Proof.
  unfold src_lt_to_next_slot_LR, tgt_lt_to_next_slot_LR.
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_forall_nat => bR bL Hb.
  apply: ct_forall_nat => aR' aL' Ha'.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ha' Hb) (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
  exact (sub_nat_lt_correspondence _ _ _ _ Ha' (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (sub_add_correspondence _ _ _ _ Ht Hb))).
Qed.

Definition src_S_t_not_sched (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.S_t_not_sched Task Job)).
Definition tgt_S_t_not_sched (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_S_t_not_sched Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_S_t_not_sched_correspondence (Task Job : eqType) :
  PropSPropRel (src_S_t_not_sched Task Job) (tgt_S_t_not_sched Task Job).
Proof.
  unfold src_S_t_not_sched, tgt_S_t_not_sched.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 1) (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
  exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ (ctw_succ_rel _ _ Ht))).
Qed.

Definition src_duration_not_sched (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.duration_not_sched Task Job)).
Definition tgt_duration_not_sched (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_duration_not_sched Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_duration_not_sched_correspondence (Task Job : eqType) :
  PropSPropRel (src_duration_not_sched Task Job) (tgt_duration_not_sched Task Job).
Proof.
  unfold src_duration_not_sched, tgt_duration_not_sched.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  apply: ct_forall_nat => dR dL Hd'.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hd' (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
  exact (ct_and _ _ _ _ (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ (sub_add_correspondence _ _ _ _ Ht Hd'))) (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ Ht Hd')))).
Qed.

Definition src_pending_Nsched_sched (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.pending_Nsched_sched Task Job)).
Definition tgt_pending_Nsched_sched (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_pending_Nsched_sched Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_pending_Nsched_sched_correspondence (Task Job : eqType) :
  PropSPropRel (src_pending_Nsched_sched Task Job) (tgt_pending_Nsched_sched Task Job).
Proof.
  unfold src_pending_Nsched_sched, tgt_pending_Nsched_sched.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ Ht (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)))).
Qed.

Definition src_at_next_start_of_slot_schedulabe (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.at_next_start_of_slot_schedulabe Task Job)).
Definition tgt_at_next_start_of_slot_schedulabe (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_at_next_start_of_slot_schedulabe Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_at_next_start_of_slot_schedulabe_correspondence (Task Job : eqType) :
  PropSPropRel (src_at_next_start_of_slot_schedulabe Task Job) (tgt_at_next_start_of_slot_schedulabe Task Job).
Proof.
  unfold src_at_next_start_of_slot_schedulabe, tgt_at_next_start_of_slot_schedulabe.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_bool_truth _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ (sub_add_correspondence _ _ _ _ Ht (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)))).
Qed.

Definition src_formula_not_sched_St (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.formula_not_sched_St Task Job)).
Definition tgt_formula_not_sched_St (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_formula_not_sched_St Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_formula_not_sched_St_correspondence (Task Job : eqType) :
  PropSPropRel (src_formula_not_sched_St Task Job) (tgt_formula_not_sched_St Task Job).
Proof.
  unfold src_formula_not_sched_St, tgt_formula_not_sched_St.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht _ _ (ctw_succ_rel _ _ Hc'))) (sub_add_correspondence _ _ _ _ (ctw_succ_rel _ _ Ht) (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (ctw_succ_rel _ _ Ht) _ _ (ctw_succ_rel _ _ Hc')))).
Qed.

Definition src_formula_sched_St (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.formula_sched_St Task Job)).
Definition tgt_formula_sched_St (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_formula_sched_St Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_formula_sched_St_correspondence (Task Job : eqType) :
  PropSPropRel (src_formula_sched_St Task Job) (tgt_formula_sched_St Task Job).
Proof.
  unfold src_formula_sched_St, tgt_formula_sched_St.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht _ _ (ctw_succ_rel _ _ Hc'))) (sub_add_correspondence _ _ _ _ (ctw_succ_rel _ _ Ht) (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (ctw_succ_rel _ _ Ht) _ _ Hc'))).
Qed.

Definition src_formula_not_sched_interval (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.formula_not_sched_interval Task Job)).
Definition tgt_formula_not_sched_interval (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_formula_not_sched_interval Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_formula_not_sched_interval_correspondence (Task Job : eqType) :
  PropSPropRel (src_formula_not_sched_interval Task Job) (tgt_formula_not_sched_interval Task Job).
Proof.
  unfold src_formula_not_sched_interval, tgt_formula_not_sched_interval.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  apply: ct_forall_nat => dR dL Hd'.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hd' (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht _ _ (ctw_succ_rel _ _ Hc'))) (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht Hd') (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (sub_add_correspondence _ _ _ _ Ht Hd') _ _ (ctw_succ_rel _ _ Hc')))).
Qed.

Definition src_formula_not_sched_to_next_slot (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.formula_not_sched_to_next_slot Task Job)).
Definition tgt_formula_not_sched_to_next_slot (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_formula_not_sched_to_next_slot Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_formula_not_sched_to_next_slot_correspondence (Task Job : eqType) :
  PropSPropRel (src_formula_not_sched_to_next_slot Task Job) (tgt_formula_not_sched_to_next_slot Task Job).
Proof.
  unfold src_formula_not_sched_to_next_slot, tgt_formula_not_sched_to_next_slot.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht _ _ (ctw_succ_rel _ _ Hc'))) (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)) (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (sub_add_correspondence _ _ _ _ Ht (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)) _ _ (ctw_succ_rel _ _ Hc')))).
Qed.

Definition src_job_not_sched_to_cunsume_1unit (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.job_not_sched_to_cunsume_1unit Task Job)).
Definition tgt_job_not_sched_to_cunsume_1unit (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_job_not_sched_to_cunsume_1unit Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_job_not_sched_to_cunsume_1unit_correspondence (Task Job : eqType) :
  PropSPropRel (src_job_not_sched_to_cunsume_1unit Task Job) (tgt_job_not_sched_to_cunsume_1unit Task Job).
Proof.
  unfold src_job_not_sched_to_cunsume_1unit, tgt_job_not_sched_to_cunsume_1unit.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht _ _ (ctw_succ_rel _ _ Hc'))) (sub_add_correspondence _ _ _ _ (ctw_succ_rel _ _ (sub_add_correspondence _ _ _ _ Ht (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht))) (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (ctw_succ_rel _ _ (sub_add_correspondence _ _ _ _ Ht (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht))) _ _ Hc'))).
Qed.

Definition src_end_time_predicate_not_sched_eq (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.end_time_predicate_not_sched_eq Task Job)).
Definition tgt_end_time_predicate_not_sched_eq (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_end_time_predicate_not_sched_eq Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_end_time_predicate_not_sched_eq_correspondence (Task Job : eqType) :
  PropSPropRel (src_end_time_predicate_not_sched_eq Task Job) (tgt_end_time_predicate_not_sched_eq Task Job).
Proof.
  unfold src_end_time_predicate_not_sched_eq, tgt_end_time_predicate_not_sched_eq.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => dR dL Hd'.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (ctw_etp Job sR sL Hs j _ _ Ht _ _ (ctw_succ_rel _ _ Hc') _ _ He).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hd' (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
  exact (ctw_etp Job sR sL Hs j _ _ (sub_add_correspondence _ _ _ _ Ht Hd') _ _ (ctw_succ_rel _ _ Hc') _ _ He).
Qed.

Definition src_end_time_predicate_not_sched_eq_rev (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.end_time_predicate_not_sched_eq_rev Task Job)).
Definition tgt_end_time_predicate_not_sched_eq_rev (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_end_time_predicate_not_sched_eq_rev Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_end_time_predicate_not_sched_eq_rev_correspondence (Task Job : eqType) :
  PropSPropRel (src_end_time_predicate_not_sched_eq_rev Task Job) (tgt_end_time_predicate_not_sched_eq_rev Task Job).
Proof.
  unfold src_end_time_predicate_not_sched_eq_rev, tgt_end_time_predicate_not_sched_eq_rev.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => dR dL Hd'.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (ctw_etp Job sR sL Hs j _ _ (sub_add_correspondence _ _ _ _ Ht Hd') _ _ (ctw_succ_rel _ _ Hc') _ _ He).
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Hd' (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
  exact (ctw_etp Job sR sL Hs j _ _ Ht _ _ (ctw_succ_rel _ _ Hc') _ _ He).
Qed.

Definition src_end_time_predicate_eq (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.end_time_predicate_eq Task Job)).
Definition tgt_end_time_predicate_eq (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_end_time_predicate_eq Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_end_time_predicate_eq_correspondence (Task Job : eqType) :
  PropSPropRel (src_end_time_predicate_eq Task Job) (tgt_end_time_predicate_eq Task Job).
Proof.
  unfold src_end_time_predicate_eq, tgt_end_time_predicate_eq.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ctw_iff _ _ _ _ (ctw_etp Job sR sL Hs j _ _ Ht _ _ (ctw_succ_rel _ _ Hc') _ _ He) (ctw_etp Job sR sL Hs j _ _ (ctw_succ_rel _ _ (sub_add_correspondence _ _ _ _ Ht (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht))) _ _ Hc' _ _ He)).
Qed.

Definition src_service_is_zero_in_Nsched_duration (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.service_is_zero_in_Nsched_duration Task Job)).
Definition tgt_service_is_zero_in_Nsched_duration (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_service_is_zero_in_Nsched_duration Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_service_is_zero_in_Nsched_duration_correspondence (Task Job : eqType) :
  PropSPropRel (src_service_is_zero_in_Nsched_duration Task Job) (tgt_service_is_zero_in_Nsched_duration Task Job).
Proof.
  unfold src_service_is_zero_in_Nsched_duration, tgt_service_is_zero_in_Nsched_duration.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => dR dL Hd'.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_false _ _ (ctw_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ Hd' (ctw_TNS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (ctw_US_service Job sR sL Hs j _ _ (sub_add_correspondence _ _ _ _ Ht Hd')) (ctw_US_service Job sR sL Hs j _ _ Ht)).
Qed.

Definition src_completes_at_end_time_pre (Task Job : eqType) : Prop :=
  ltac:(type_of_term (@WCRT_OneJobTDMA.completes_at_end_time_pre Task Job)).
Definition tgt_completes_at_end_time_pre (Task Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_completes_at_end_time_pre Task (ct_decidable_eq Task) Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_completes_at_end_time_pre_correspondence (Task Job : eqType) :
  PropSPropRel (src_completes_at_end_time_pre Task Job) (tgt_completes_at_end_time_pre Task Job).
Proof.
  unfold src_completes_at_end_time_pre, tgt_completes_at_end_time_pre.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_forall_nat => cR' cL' Hc'.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_US_pending Job sR sL Hs aR aL Ha cR cL Hc j _ _ Ht)).
  apply: ct_imp; first exact (sub_nat_eq_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (ctw_US_service Job sR sL Hs j _ _ Ht) Hc') (Hc j)).
  exact (ctw_etp Job sR sL Hs j _ _ Ht _ _ Hc' _ _ (sub_add_correspondence _ _ _ _ Ht (WCRT_OneJobTDMA_formula_rt_correspondence Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ Ht _ _ Hc'))).
Qed.

Definition src_completes_at_end_time (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> nat, ltac:(type_of_term (@WCRT_OneJobTDMA.completes_at_end_time Task task_cost task_deadline Job)).
Definition tgt_completes_at_end_time (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_completes_at_end_time Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_completes_at_end_time_correspondence (Task Job : eqType) :
  PropSPropRel (src_completes_at_end_time Task Job) (tgt_completes_at_end_time Task Job).
Proof.
  unfold src_completes_at_end_time, tgt_completes_at_end_time.
  apply: (ctw_forall_par Task) => tcR tcL Htc.
  apply: (ctw_forall_par Task) => tdR tdL Htd.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: (ctw_forall_par Job) => dR dL Hd.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ctw_J_valid_sporadic_job Task Job tcR tcL tdR tdL Htc Htd cR cL dR dL Hc Hd job_task j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  exact (ctw_ET_completes_at Job aR aL Ha cR cL Hc sR sL Hs j _ _ (sub_add_correspondence _ _ _ _ (Ha j) (WCRT_OneJobTDMA_job_response_time_tdma_in_at_most_one_job_is_pending_correspondence Task Job aR aL Ha cR cL Hc tsR tsL Hts slR slL Hsl oR oL Ho tsk j))).
Qed.

Definition src_response_time_le_WCRT (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> nat, ltac:(type_of_term (@WCRT_OneJobTDMA.response_time_le_WCRT Task task_cost task_deadline Job)).
Definition tgt_response_time_le_WCRT (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_response_time_le_WCRT Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_response_time_le_WCRT_correspondence (Task Job : eqType) :
  PropSPropRel (src_response_time_le_WCRT Task Job) (tgt_response_time_le_WCRT Task Job).
Proof.
  unfold src_response_time_le_WCRT, tgt_response_time_le_WCRT.
  apply: (ctw_forall_par Task) => tcR tcL Htc.
  apply: (ctw_forall_par Task) => tdR tdL Htd.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: (ctw_forall_par Job) => dR dL Hd.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ctw_J_valid_sporadic_job Task Job tcR tcL tdR tdL Htc Htd cR cL dR dL Hc Hd job_task j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_J_job_cost_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task j)).
  exact (sub_nat_le_correspondence _ _ _ _ (WCRT_OneJobTDMA_job_response_time_tdma_in_at_most_one_job_is_pending_correspondence Task Job aR aL Ha cR cL Hc tsR tsL Hts slR slL Hsl oR oL Ho tsk j) (WCRT_OneJobTDMA_WCRT_correspondence Task tcR tcL Htc slR slL Hsl tsR tsL Hts tsk)).
Qed.

Definition src_exists_WCRT (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> nat, ltac:(type_of_term (@WCRT_OneJobTDMA.exists_WCRT Task task_cost task_deadline Job)).
Definition tgt_exists_WCRT (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_exists_WCRT Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_exists_WCRT_correspondence (Task Job : eqType) :
  PropSPropRel (src_exists_WCRT Task Job) (tgt_exists_WCRT Task Job).
Proof.
  unfold src_exists_WCRT, tgt_exists_WCRT.
  apply: (ctw_forall_par Task) => tcR tcL Htc.
  apply: (ctw_forall_par Task) => tdR tdL Htd.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: (ctw_forall_par Job) => dR dL Hd.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ctw_J_valid_sporadic_job Task Job tcR tcL tdR tdL Htc Htd cR cL dR dL Hc Hd job_task j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_J_job_cost_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task j)).
  apply: ct_imp; first exact (ct_and _ _ _ _ (sub_nat_eq_correspondence _ _ _ _ (Hc j) (Htc tsk))
    (sub_nat_eq_correspondence _ _ _ _ (ctw_FS Task tsR tsL Hts slR slL Hsl oR oL Ho tsk _ _ (Ha j)) (Hsl tsk))).
  exact (sub_nat_eq_correspondence _ _ _ _ (WCRT_OneJobTDMA_job_response_time_tdma_in_at_most_one_job_is_pending_correspondence Task Job aR aL Ha cR cL Hc tsR tsL Hts slR slL Hsl oR oL Ho tsk j) (WCRT_OneJobTDMA_WCRT_correspondence Task tcR tcL Htc slR slL Hsl tsR tsL Hts tsk)).
Qed.

Definition src_job_completed_by_WCRT (Task Job : eqType) : Prop :=
  forall task_cost task_deadline : Task -> nat, ltac:(type_of_term (@WCRT_OneJobTDMA.job_completed_by_WCRT Task task_cost task_deadline Job)).
Definition tgt_job_completed_by_WCRT (Task Job : eqType) : SProp :=
  forall task_cost task_deadline : Task -> Lean.Nat, ltac:(type_of_term (I.Prosa_Classic_Analysis_Uni_Basic_TdmaWcrtAnalysis_WCRT_OneJobTDMA_job_completed_by_WCRT Task (ct_decidable_eq Task) task_cost task_deadline Job (ct_decidable_eq Job))).
Theorem WCRT_OneJobTDMA_job_completed_by_WCRT_correspondence (Task Job : eqType) :
  PropSPropRel (src_job_completed_by_WCRT Task Job) (tgt_job_completed_by_WCRT Task Job).
Proof.
  unfold src_job_completed_by_WCRT, tgt_job_completed_by_WCRT.
  apply: (ctw_forall_par Task) => tcR tcL Htc.
  apply: (ctw_forall_par Task) => tdR tdL Htd.
  apply: (ctw_forall_par Job) => aR aL Ha.
  apply: (ctw_forall_par Job) => cR cL Hc.
  apply: (ctw_forall_par Job) => dR dL Hd.
  apply: ct_forall_identity => job_task.
  apply: (ctw_forall_arr Job) => arrR arrL Harr.
  apply: (ctw_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (ctw_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (ctw_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: (ctw_forall_par Task) => slR slL Hsl.
  apply: (ctw_forall_ord Task) => oR oL Ho.
  apply: (ctw_forall_set Task) => tsR tsL Hts.
  apply: ct_forall_identity => tsk.
  apply: ct_imp; first exact (ctw_set_mem Task tsk tsR tsL Hts).
  apply: ct_forall_identity => j.
  apply: ct_imp; first exact (ct_eq_rel Task (job_task j) tsk).
  apply: ct_imp; first exact (ctw_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ctw_J_valid_sporadic_job Task Job tcR tcL tdR tdL Htc Htd cR cL dR dL Hc Hd job_task j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_TD_is_valid_time_slot Task tsk slR slL Hsl)).
  apply: ct_imp; first exact (ctw_TDP_Respects_TDMA_policy Task Job sR sL Hs tsR tsL Hts slR slL Hsl oR oL Ho job_task aR aL Ha cR cL Hc arrR arrL Harr).
  apply: ct_imp; first exact (ctw_allprev Task Job aR aL Ha cR cL Hc job_task arrR arrL Harr sR sL Hs j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ctw_J_job_cost_le_task_cost Task Job tcR tcL Htc cR cL Hc job_task j)).
  exact (ct_bool_truth _ _ (ctw_US_completed_by Job sR sL Hs cR cL Hc j _ _ (sub_add_correspondence _ _ _ _ (Ha j) (WCRT_OneJobTDMA_WCRT_correspondence Task tcR tcL Htc slR slL Hsl tsR tsL Hts tsk)))).
Qed.
