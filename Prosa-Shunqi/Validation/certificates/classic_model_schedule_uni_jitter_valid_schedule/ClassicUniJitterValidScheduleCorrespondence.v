From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.priority classic.model.arrival.jitter.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.jitter.schedule classic.model.schedule.uni.jitter.platform classic.model.schedule.uni.jitter.valid_schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniJitterValidSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniJitterValidScheduleBase ClassicUniJitterValidScheduleList.

Module I := ImportedClassicUniJitterValidSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/jitter/valid_schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by the eqType's decision
    procedure ([ct_decidable_eq]); times by [SubNatRel]; job parameters pointwise through [SubNatRel]; uniprocessor
    schedules pointwise through the option map; arrival sequences pointwise on related times; JLDP policies pointwise on
    related times and Booleans.  The conjuncts are related through the accepted classic uniprocessor (jitter) schedule
    and platform certificates (re-bound below). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cvj_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cvj_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cvj_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Lemma cvj_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cvj_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cvj_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cvj_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cvj_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cvj_unmap_rel T l) PR PL).
Qed.

Definition CvjParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cvj_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CvjParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cvj_forall_cover _ _ (CvjParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cvj_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cvj_natl s') end.

Definition cvj_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cvj_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cvj_one) (cvj_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cvj_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cvj_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cvj_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cvj_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cvj_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CvjFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

Section Rel.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LArr := (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).

Definition CvjArrRel (aR : ArrivalSequence.arrival_sequence Job) (aL : LArr) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Definition cvj_arr_to_target (aR : ArrivalSequence.arrival_sequence Job) : LArr :=
  fun tL => cl_map cid (aR (sub_nat_to_rocq tL)).

Definition cvj_arr_to_source (aL : LArr) : ArrivalSequence.arrival_sequence Job :=
  fun tR => cl_unmap cid (aL (sub_nat_to_imported tR)).

Lemma cvj_arr_canonical aR : CvjArrRel aR (cvj_arr_to_target aR).
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. rewrite /cvj_arr_to_target sub_nat_rocq_roundtrip. reflexivity.
Qed.

Lemma cvj_arr_surjective aL : CvjArrRel (cvj_arr_to_source aL) aL.
Proof.
  intros tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) _).
Qed.

Lemma cvj_forall_arr (PR : ArrivalSequence.arrival_sequence Job -> Prop) (PL : LArr -> SProp) :
  (forall aR aL, CvjArrRel aR aL -> PropSPropRel (PR aR) (PL aL)) -> PropSPropRel (forall a, PR a) (forall a, PL a).
Proof. exact (cvj_forall_cover _ _ CvjArrRel cvj_arr_to_target cvj_arr_to_source cvj_arr_canonical cvj_arr_surjective PR PL). Qed.

End Rel.

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cvj_arrives_in aR aL (Ha : CvjArrRel Job aR aL) j :
  PropSPropRel (ArrivalSequence.arrives_in aR j)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrives_in Job dJ aL j).
Proof. apply: ct_exists_nat => tR tL Ht. exact (cvj_mem Job j _ _ (Ha tR tL Ht)). Qed.

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs2.

Fixpoint cvj_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cvj_snatl s') end.

Lemma cvj_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cvj_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cvj_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cvj_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cvj_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cvj_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cvj_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CvjFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cvj_fun_canonical FR FL (HF : CvjFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cvj_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cvj_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CvjFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cvj_nat_sub_canonical nR mR.
  rewrite cvj_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cvj_foldr_add FL FR (cvj_fun_canonical FR FL HF)).
  by rewrite cvj_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cvj_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cvj_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cvj_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cvj_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cvj_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CvjSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cvj_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cvj_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cvj_sched_canonical sR : CvjSchedRel sR (cvj_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cvj_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cvj_sched_surjective sL : CvjSchedRel (cvj_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cvj_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cvj_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CvjSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cvj_forall_cover _ _ CvjSchedRel cvj_sched_to_target cvj_sched_to_source cvj_sched_canonical cvj_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cvj_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CvjSchedRel Job sR (cvj_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CvjSchedRel Job (cvj_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cvj_sched_canonical Job) (cvj_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CvjSchedRel Job sR sL.

Lemma cvj_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cvj_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cvj_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cvj_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cvj_US_scheduled_at j tR tL Ht)). Qed.

Lemma cvj_service_at_fun j : CvjFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cvj_US_service_at j kR kL Hk). Qed.

Lemma cvj_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cvj_ico _ _ _ _ _ _ H1 H2 (cvj_service_at_fun j)). Qed.

Lemma cvj_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cvj_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cvj_US_completed_by cR cL (Hc : CvjParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cvj_US_service j tR tL Ht)). Qed.

Lemma cvj_US_jobs_come_from_arrival_sequence arrR arrL (Harr : CvjArrRel Job arrR arrL) :
  PropSPropRel (UniprocessorSchedule.jobs_come_from_arrival_sequence sR arrR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_come_from_arrival_sequence Job dJ sL arrL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cvj_US_scheduled_at j tR tL Ht)).
  exact (cvj_arrives_in Job arrR arrL Harr j).
Qed.

Lemma cvj_US_completed_jobs_dont_execute cR cL (Hc : CvjParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cvj_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cvj_AJ_actual_arrival pR pL (Hp : CvjParRel Job pR pL) qR qL (Hq : CvjParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cvj_AJ_jitter_has_passed pR pL (Hp : CvjParRel Job pR pL) qR qL (Hq : CvjParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cvj_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

End JitterArrDefs.

Section UjschedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CvjSchedRel Job sR sL.

Lemma cvj_UJ_pending aR aL (Ha : CvjParRel Job aR aL) cR cL (Hc : CvjParRel Job cR cL)
    jjR jjL (Hjj : CvjParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cvj_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cvj_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Lemma cvj_UJ_backlogged aR aL (Ha : CvjParRel Job aR aL) cR cL (Hc : CvjParRel Job cR cL)
    jjR jjL (Hjj : CvjParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_backlogged Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (cvj_UJ_pending aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cvj_US_scheduled_at Job sR sL Hs j tR tL Ht))).
Qed.

Lemma cvj_UJ_jobs_execute_after_jitter aR aL (Ha : CvjParRel Job aR aL) jjR jjL (Hjj : CvjParRel Job jjR jjL) :
  PropSPropRel (UniprocessorScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cvj_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (cvj_AJ_jitter_has_passed Job aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.

End UjschedDefs.

(** Priority relations (as in the accepted classic priority certificate). *)
Definition CvjRelRel (T : Type) (rR : T -> T -> bool) (rL : T -> T -> I.Bool) : SProp :=
  forall a b, CtBoolRel (rR a b) (rL a b).

Lemma cvj_rel_canonical (T : Type) (rR : T -> T -> bool) : CvjRelRel T rR (fun a b => ct_b2l (rR a b)).
Proof. intros a b. exact (ct_bool_canonical _). Qed.

Lemma cvj_rel_surjective (T : Type) (rL : T -> T -> I.Bool) : CvjRelRel T (fun a b => ct_l2b (rL a b)) rL.
Proof. intros a b. exact (ct_bool_surjective _). Qed.

Lemma cvj_forall_rel (T : Type) (PR : (T -> T -> bool) -> Prop) (PL : (T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CvjRelRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cvj_forall_cover _ _ (CvjRelRel T) (fun rR a b => ct_b2l (rR a b)) (fun rL a b => ct_l2b (rL a b))
           (cvj_rel_canonical T) (cvj_rel_surjective T) PR PL).
Qed.

Definition CvjJldpRel (T : Type) (rR : nat -> T -> T -> bool) (rL : Lean.Nat -> T -> T -> I.Bool) : SProp :=
  forall tR tL, SubNatRel tR tL -> CvjRelRel T (rR tR) (rL tL).

Lemma cvj_jldp_canonical (T : Type) (rR : nat -> T -> T -> bool) :
  CvjJldpRel T rR (fun tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b)).
Proof.
  intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. rewrite sub_nat_rocq_roundtrip.
  exact (ct_bool_canonical _).
Qed.

Lemma cvj_jldp_surjective (T : Type) (rL : Lean.Nat -> T -> T -> I.Bool) :
  CvjJldpRel T (fun tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) rL.
Proof. intros tR tL Ht a b. have E := cl_nat_logic _ _ Ht. subst tL. exact (ct_bool_surjective _). Qed.

(* ------------------------------------------------------------------ *)
(** * Arrival sequences *)

Lemma cvj_forall_jldp (T : Type) (PR : (nat -> T -> T -> bool) -> Prop) (PL : (Lean.Nat -> T -> T -> I.Bool) -> SProp) :
  (forall rR rL, CvjJldpRel T rR rL -> PropSPropRel (PR rR) (PL rL)) -> PropSPropRel (forall r, PR r) (forall r, PL r).
Proof.
  exact (cvj_forall_cover _ _ (CvjJldpRel T) (fun rR tL a b => ct_b2l (rR (sub_nat_to_rocq tL) a b))
           (fun rL tR a b => ct_l2b (rL (sub_nat_to_imported tR) a b)) (cvj_jldp_canonical T) (cvj_jldp_surjective T) PR PL).
Qed.

Section UjplatDefs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CvjSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat) (jjR : Job -> nat) (jjL : Job -> Lean.Nat).
Hypotheses (Ha : CvjParRel Job aR aL) (Hc : CvjParRel Job cR cL) (Hjj : CvjParRel Job jjR jjL).
Variables (arrR : ArrivalSequence.arrival_sequence Job)
  (arrL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job dJ).
Hypothesis Harr : CvjArrRel Job arrR arrL.

Notation BL := (cvj_UJ_backlogged Job sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj).
Notation SA := (cvj_US_scheduled_at Job sR sL Hs).

Lemma cvj_UJP_work_conserving :
  PropSPropRel (Platform.work_conserving aR cR jjR arrR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_work_conserving Job dJ aL cL jjL arrL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cvj_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_exists_identity => j_other.
  exact (ct_bool_truth _ _ (SA j_other tR tL Ht)).
Qed.

Lemma cvj_UJP_respects_JLDP_policy hR hL (Hh : CvjJldpRel Job hR hL) :
  PropSPropRel (Platform.respects_JLDP_policy aR cR jjR arrR sR hR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Platform_Platform_respects_JLDP_policy Job dJ aL cL jjL arrL sL hL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_identity => j_hp. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (cvj_arrives_in Job arrR arrL Harr j).
  apply: ct_imp; first exact (ct_bool_truth _ _ (BL j tR tL Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SA j_hp tR tL Ht)).
  exact (ct_bool_truth _ _ (Hh tR tL Ht j_hp j)).
Qed.

End UjplatDefs.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Theorem ValidJitterAwareSchedule_valid_jitter_aware_schedule_correspondence (Task Job : eqType) aR aL (Ha : CvjParRel Job aR aL)
    (job_task : Job -> Task) arrR arrL (Harr : CvjArrRel Job arrR arrL) hR hL (Hh : CvjJldpRel Job hR hL)
    cR cL (Hc : CvjParRel Job cR cL) jjR jjL (Hjj : CvjParRel Job jjR jjL) sR sL (Hs : CvjSchedRel Job sR sL) :
  PropSPropRel (ValidJitterAwareSchedule.valid_jitter_aware_schedule aR arrR hR cR jjR sR)
    (I.Prosa_Classic_Model_Schedule_Uni_Jitter_ValidSchedule_ValidJitterAwareSchedule_valid_jitter_aware_schedule Job (ct_decidable_eq Job) aL arrL hL cL jjL sL).
Proof.
  apply: ct_and; first exact (cvj_US_jobs_come_from_arrival_sequence Job sR sL Hs arrR arrL Harr).
  apply: ct_and; first exact (cvj_UJ_jobs_execute_after_jitter Job sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_and; first exact (cvj_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_and; first exact (cvj_UJP_work_conserving Job sR sL Hs aR aL cR cL jjR jjL Ha Hc Hjj arrR arrL Harr).
  exact (cvj_UJP_respects_JLDP_policy Job sR sL Hs aR aL cR cL jjR jjL Ha Hc Hjj arrR arrL Harr hR hL Hh).
Qed.
