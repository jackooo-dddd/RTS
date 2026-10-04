From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.jitter.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.jitter.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniJitterSchedule.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniJitterScheduleBase ClassicUniJitterScheduleList.

Module I := ImportedClassicUniJitterSchedule.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/jitter/schedule.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by the eqType's decision
    procedure ([ct_decidable_eq]); times by [SubNatRel]; job parameters pointwise through [SubNatRel]; uniprocessor
    schedules pointwise through the option map; all with two-way totals.  The imported uniprocessor schedule and
    jitter arrival definitions are related as in the accepted classic certificates (re-bound below, through the
    kernel-guarded body projections of [ClassicUniJitterScheduleInterface]); the two statements whose types contain
    [Finset.Ico] sums are exported through kernel-checked normalization guards.

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cuj_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cuj_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cuj_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cuj_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cuj_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CujParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cuj_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CujParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cuj_forall_cover _ _ (CujParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cuj_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cuj_natl s') end.

Definition cuj_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cuj_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cuj_one) (cuj_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cuj_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cuj_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cuj_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cuj_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cuj_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CujFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
  forall nR nL, SubNatRel nR nL -> ClListRel cid (fR nR) (fL nL).

(* ------------------------------------------------------------------ *)
(** * Arrival sequences and parameters *)

(** The imported [ArrivalSequence] definitions this file's statements mention, related on related inputs. *)
Section ArrivalDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

End ArrivalDefs.

Section ArrivalDefs2.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cuj_has_arrived pR pL (Hp : CujParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cuj_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cuj_snatl s') end.

Lemma cuj_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cuj_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cuj_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cuj_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cuj_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cuj_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cuj_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CujFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cuj_fun_canonical FR FL (HF : CujFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cuj_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cuj_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CujFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cuj_nat_sub_canonical nR mR.
  rewrite cuj_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cuj_foldr_add FL FR (cuj_fun_canonical FR FL HF)).
  by rewrite cuj_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cuj_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cuj_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cuj_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cuj_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CujSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cuj_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cuj_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cuj_sched_canonical sR : CujSchedRel sR (cuj_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cuj_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cuj_sched_surjective sL : CujSchedRel (cuj_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cuj_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cuj_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CujSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cuj_forall_cover _ _ CujSchedRel cuj_sched_to_target cuj_sched_to_source cuj_sched_canonical cuj_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cuj_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CujSchedRel Job sR (cuj_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CujSchedRel Job (cuj_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cuj_sched_canonical Job) (cuj_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CujSchedRel Job sR sL.

Lemma cuj_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cuj_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cuj_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cuj_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cuj_US_scheduled_at j tR tL Ht)). Qed.

Lemma cuj_service_at_fun j : CujFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cuj_US_service_at j kR kL Hk). Qed.

Lemma cuj_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cuj_ico _ _ _ _ _ _ H1 H2 (cuj_service_at_fun j)). Qed.

Lemma cuj_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cuj_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cuj_US_completed_by cR cL (Hc : CujParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cuj_US_service j tR tL Ht)). Qed.

Lemma cuj_US_jobs_must_arrive_to_execute aR aL (Ha : CujParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cuj_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cuj_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma cuj_US_completed_jobs_dont_execute cR cL (Hc : CujParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (cuj_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** The imported [ArrivalSequenceWithJitter] definitions (as in the accepted classic jitter arrival_sequence certificate). *)
Section JitterArrDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).

Lemma cuj_AJ_actual_arrival pR pL (Hp : CujParRel Job pR pL) qR qL (Hq : CujParRel Job qR qL) j :
  SubNatRel (ArrivalSequenceWithJitter.actual_arrival pR qR j) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_actual_arrival Job dJ pL qL j).
Proof. exact (sub_add_correspondence _ _ _ _ (Hp j) (Hq j)). Qed.

Lemma cuj_AJ_jitter_has_passed pR pL (Hp : CujParRel Job pR pL) qR qL (Hq : CujParRel Job qR qL) j
    tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequenceWithJitter.jitter_has_passed pR qR j tR) (I.Prosa_Classic_Model_Arrival_Jitter_ArrivalSequence_ArrivalSequenceWithJitter_jitter_has_passed Job dJ pL qL j tL).
Proof. exact (ct_decide_le _ _ _ _ (cuj_AJ_actual_arrival pR pL Hp qR qL Hq j) Ht). Qed.

End JitterArrDefs.


(* ------------------------------------------------------------------ *)
(** * Definitions *)

Notation JHP := cuj_AJ_jitter_has_passed.
Notation AAJ := cuj_AJ_actual_arrival.

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CujSchedRel Job sR sL.

Theorem UniprocessorScheduleWithJitter_pending_correspondence aR aL (Ha : CujParRel Job aR aL) cR cL (Hc : CujParRel Job cR cL)
    jjR jjL (Hjj : CujParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.pending aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_pending Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (JHP Job aR aL Ha jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cuj_US_completed_by Job sR sL Hs cR cL Hc j tR tL Ht))).
Qed.

Theorem UniprocessorScheduleWithJitter_backlogged_correspondence aR aL (Ha : CujParRel Job aR aL) cR cL (Hc : CujParRel Job cR cL)
    jjR jjL (Hjj : CujParRel Job jjR jjL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorScheduleWithJitter.backlogged aR cR jjR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_backlogged Job dJ aL cL jjL sL j tL).
Proof.
  exact (ct_bool_and _ _ _ _ (UniprocessorScheduleWithJitter_pending_correspondence aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)
           (ct_bool_not _ _ (cuj_US_scheduled_at Job sR sL Hs j tR tL Ht))).
Qed.

Theorem UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence aR aL (Ha : CujParRel Job aR aL) jjR jjL (Hjj : CujParRel Job jjR jjL) :
  PropSPropRel (UniprocessorScheduleWithJitter.jobs_execute_after_jitter aR jjR sR) (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_jobs_execute_after_jitter Job dJ aL jjL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cuj_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (JHP Job aR aL Ha jjR jjL Hjj j tR tL Ht)).
Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation c0 := (sub_nat_rel_canonical 0).
Ltac cuj_prefix := apply: cuj_forall_par => aR aL Ha; apply: cuj_forall_par => jjR jjL Hjj;
  apply: cuj_forall_sched => sR sL Hs.

Definition src_jobs_with_jitter_must_arrive_to_execute (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorScheduleWithJitter.jobs_with_jitter_must_arrive_to_execute Job)).
Definition tgt_jobs_with_jitter_must_arrive_to_execute (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_jobs_with_jitter_must_arrive_to_execute Job (ct_decidable_eq Job))).

Theorem UniprocessorScheduleWithJitter_jobs_with_jitter_must_arrive_to_execute_correspondence (Job : eqType) :
  PropSPropRel (src_jobs_with_jitter_must_arrive_to_execute Job) (tgt_jobs_with_jitter_must_arrive_to_execute Job).
Proof.
  unfold src_jobs_with_jitter_must_arrive_to_execute, tgt_jobs_with_jitter_must_arrive_to_execute. cuj_prefix.
  apply: ct_imp; first exact (UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence Job sR sL Hs aR aL Ha jjR jjL Hjj).
  exact (cuj_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
Qed.

Definition src_jitter_has_passed_implies_arrived (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorScheduleWithJitter.jitter_has_passed_implies_arrived Job)).
Definition tgt_jitter_has_passed_implies_arrived (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_jitter_has_passed_implies_arrived Job (ct_decidable_eq Job))).

Theorem UniprocessorScheduleWithJitter_jitter_has_passed_implies_arrived_correspondence (Job : eqType) :
  PropSPropRel (src_jitter_has_passed_implies_arrived Job) (tgt_jitter_has_passed_implies_arrived Job).
Proof.
  unfold src_jitter_has_passed_implies_arrived, tgt_jitter_has_passed_implies_arrived.
  apply: cuj_forall_par => aR aL Ha; apply: cuj_forall_par => jjR jjL Hjj. apply: ct_forall_identity => j.
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (JHP Job aR aL Ha jjR jjL Hjj j tR tL Ht)).
  exact (ct_bool_truth _ _ (cuj_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Definition src_service_before_jitter_is_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorScheduleWithJitter.service_before_jitter_is_zero Job)).
Definition tgt_service_before_jitter_is_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_service_before_jitter_is_zero Job (ct_decidable_eq Job))).

Theorem UniprocessorScheduleWithJitter_service_before_jitter_is_zero_correspondence (Job : eqType) :
  PropSPropRel (src_service_before_jitter_is_zero Job) (tgt_service_before_jitter_is_zero Job).
Proof.
  unfold src_service_before_jitter_is_zero, tgt_service_before_jitter_is_zero. cuj_prefix.
  apply: ct_imp; first exact (UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence Job sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (sub_nat_lt_correspondence _ _ _ _ Ht (AAJ Job aR aL Ha jjR jjL Hjj j)).
  exact (sub_nat_eq_correspondence _ _ _ _ (cuj_US_service_at Job sR sL Hs j tR tL Ht) c0).
Qed.

Definition src_cumulative_service_before_jitter_is_zero (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorScheduleWithJitter.cumulative_service_before_jitter_is_zero Job)).
Definition tgt_cumulative_service_before_jitter_is_zero (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_cumulative_service_before_jitter_is_zero Job (ct_decidable_eq Job))).

Theorem UniprocessorScheduleWithJitter_cumulative_service_before_jitter_is_zero_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_service_before_jitter_is_zero Job) (tgt_cumulative_service_before_jitter_is_zero Job).
Proof.
  unfold src_cumulative_service_before_jitter_is_zero, tgt_cumulative_service_before_jitter_is_zero. cuj_prefix.
  apply: ct_imp; first exact (UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence Job sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  apply: ct_imp; first exact (sub_nat_le_correspondence _ _ _ _ H2 (AAJ Job aR aL Ha jjR jjL Hjj j)).
  exact (sub_nat_eq_correspondence _ _ _ _ (cuj_ico _ _ _ _ _ _ H1 H2 (cuj_service_at_fun Job sR sL Hs j)) c0).
Qed.

Definition src_ignore_service_before_jitter (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorScheduleWithJitter.ignore_service_before_jitter Job)).
Definition tgt_ignore_service_before_jitter (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_ignore_service_before_jitter Job (ct_decidable_eq Job))).

Theorem UniprocessorScheduleWithJitter_ignore_service_before_jitter_correspondence (Job : eqType) :
  PropSPropRel (src_ignore_service_before_jitter Job) (tgt_ignore_service_before_jitter Job).
Proof.
  unfold src_ignore_service_before_jitter, tgt_ignore_service_before_jitter. cuj_prefix.
  apply: ct_imp; first exact (UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence Job sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  have Hx := AAJ Job aR aL Ha jjR jjL Hjj j.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ H1 Hx) (ct_decide_le _ _ _ _ Hx H2))).
  exact (sub_nat_eq_correspondence _ _ _ _ (cuj_ico _ _ _ _ _ _ H1 H2 (cuj_service_at_fun Job sR sL Hs j))
           (cuj_ico _ _ _ _ _ _ Hx H2 (cuj_service_at_fun Job sR sL Hs j))).
Qed.

Definition src_scheduled_implies_pending (Job : eqType) : Prop :=
  ltac:(type_of_term (@UniprocessorScheduleWithJitter.scheduled_implies_pending Job)).
Definition tgt_scheduled_implies_pending (Job : eqType) : SProp :=
  ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Jitter_Schedule_UniprocessorScheduleWithJitter_scheduled_implies_pending Job (ct_decidable_eq Job))).

Theorem UniprocessorScheduleWithJitter_scheduled_implies_pending_correspondence (Job : eqType) :
  PropSPropRel (src_scheduled_implies_pending Job) (tgt_scheduled_implies_pending Job).
Proof.
  unfold src_scheduled_implies_pending, tgt_scheduled_implies_pending.
  apply: cuj_forall_par => aR aL Ha. apply: cuj_forall_par => cR cL Hc. apply: cuj_forall_par => jjR jjL Hjj.
  apply: cuj_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (UniprocessorScheduleWithJitter_jobs_execute_after_jitter_correspondence Job sR sL Hs aR aL Ha jjR jjL Hjj).
  apply: ct_imp; first exact (cuj_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cuj_US_scheduled_at Job sR sL Hs j tR tL Ht)).
  exact (ct_bool_truth _ _ (UniprocessorScheduleWithJitter_pending_correspondence Job sR sL Hs aR aL Ha cR cL Hc jjR jjL Hjj j tR tL Ht)).
Qed.
