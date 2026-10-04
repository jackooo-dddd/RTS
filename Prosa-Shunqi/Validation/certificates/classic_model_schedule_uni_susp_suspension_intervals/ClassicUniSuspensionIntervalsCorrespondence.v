From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import util.unit_growth classic.model.time classic.model.suspension classic.model.arrival.basic.arrival_sequence classic.model.schedule.uni.schedule classic.model.schedule.uni.susp.last_execution classic.model.schedule.uni.susp.suspension_intervals.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicUniSuspensionIntervals.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicUniSuspensionIntervalsBase ClassicUniSuspensionIntervalsList ClassicUniSuspensionIntervalsOrd.

Module I := ImportedClassicUniSuspensionIntervals.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/susp/suspension_intervals.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by the eqType's decision
    procedure ([ct_decidable_eq]); times by [SubNatRel]; job parameters pointwise through [SubNatRel]; suspension
    functions pointwise on related service values; uniprocessor schedules pointwise through the option map; all with
    two-way totals.  The imported uniprocessor schedule, suspension and last-execution definitions are related as in
    the accepted classic certificates (re-bound below, through the kernel-checked equations and kernel-guarded body
    projections of [ClassicUniSuspensionIntervalsInterface]).

    Statements: the source side is the exact elaborated type of the pinned lemma (via [type of]; the source proof
    is not used). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma csi_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma csi_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma csi_ne (T : Type) (x y : T) : PropSPropRel (x <> y) (I.Ne T x y).
Proof. exact (ct_imp _ _ _ _ (ct_eq_rel T x y) csi_false_rel). Qed.

Lemma csi_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma csi_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma csi_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma csi_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (csi_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => csi_unmap_rel T l) PR PL).
Qed.

Definition CsiParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma csi_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CsiParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (csi_forall_cover _ _ (CsiParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint csi_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (csi_natl s') end.

Definition csi_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma csi_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) csi_one) (csi_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) csi_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (csi_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma csi_map_natl {B : Type} (f : Lean.Nat -> B) : forall s,
  Logic.eq (I.List_map_inst1 Lean.Nat B f (csi_natl s)) (cl_map (fun k => f (sub_nat_to_imported k)) s).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (I.List_cons B (f (sub_nat_to_imported k)) (I.List_map_inst1 Lean.Nat B f (csi_natl s)))
                   (I.List_cons B (f (sub_nat_to_imported k)) (cl_map (fun k => f (sub_nat_to_imported k)) s))).
  by rewrite IH.
Qed.

Lemma csi_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma csi_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma csi_cl_append {A : Type} : forall s1 s2 : seq A,
  Logic.eq (cl_map cid (s1 ++ s2)) (I.List_append A (cl_map cid s1) (cl_map cid s2)).
Proof.
  elim => [|x s1 IH] s2; first reflexivity.
  change (Logic.eq (I.List_cons A x (cl_map cid (s1 ++ s2))) (I.List_cons A x (I.List_append A (cl_map cid s1) (cl_map cid s2)))).
  by rewrite IH.
Qed.

Lemma csi_flatten {A : Type} : forall L : seq (seq A),
  Logic.eq (I.List_flatten A (cl_map (cl_map cid) L)) (cl_map cid (flatten L)).
Proof.
  elim => [|s L IH] //=.
  change (Logic.eq (I.List_append A (cl_map cid s) (I.List_flatten A (cl_map (cl_map cid) L))) (cl_map cid (s ++ flatten L))).
  rewrite IH csi_cl_append. reflexivity.
Qed.

Lemma csi_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsiFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
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

Lemma csi_has_arrived pR pL (Hp : CsiParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint csi_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (csi_snatl s') end.

Lemma csi_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (csi_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (csi_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma csi_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (csi_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (csi_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma csi_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CsiFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma csi_fun_canonical FR FL (HF : CsiFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma csi_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma csi_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CsiFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := csi_nat_sub_canonical nR mR.
  rewrite csi_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (csi_foldr_add FL FR (csi_fun_canonical FR FL HF)).
  by rewrite csi_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition csi_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition csi_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma csi_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma csi_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (csi_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CsiSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition csi_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition csi_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma csi_sched_canonical sR : CsiSchedRel sR (csi_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /csi_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma csi_sched_surjective sL : CsiSchedRel (csi_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /csi_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma csi_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CsiSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (csi_forall_cover _ _ CsiSchedRel csi_sched_to_target csi_sched_to_source csi_sched_canonical csi_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma csi_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CsiSchedRel Job sR (csi_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CsiSchedRel Job (csi_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (csi_sched_canonical Job) (csi_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsiSchedRel Job sR sL.

Lemma csi_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (csi_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (csi_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma csi_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (csi_US_scheduled_at j tR tL Ht)). Qed.

Lemma csi_service_at_fun j : CsiFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (csi_US_service_at j kR kL Hk). Qed.

Lemma csi_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (csi_ico _ _ _ _ _ _ H1 H2 (csi_service_at_fun j)). Qed.

Lemma csi_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (csi_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma csi_US_completed_by cR cL (Hc : CsiParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (csi_US_service j tR tL Ht)). Qed.

Lemma csi_US_jobs_must_arrive_to_execute aR aL (Ha : CsiParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csi_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (csi_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

Lemma csi_US_completed_jobs_dont_execute cR cL (Hc : CsiParRel Job cR cL) :
  PropSPropRel (UniprocessorSchedule.completed_jobs_dont_execute cR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_jobs_dont_execute Job dJ cL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  exact (sub_nat_le_correspondence _ _ _ _ (csi_US_service j tR tL Ht) (Hc j)).
Qed.

End USchedDefs.

(** * [\max] over ordinals against [maxFiltered] over [List.finRange] *)

Lemma csi_foldr_max (f : Lean.Nat -> Lean.Nat) (g : nat -> nat)
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

Lemma csi_max_rel nR nL (Hn : SubNatRel nR nL) (QR : 'I_nR -> bool) (QL : Fin nL -> I.Bool) (HQ : CoOrdPredRel nR nL QR QL) :
  SubNatRel (\max_(i < nR | QR i) nat_of_ord i)
    (I.Prosa_Util_Sum_maxFiltered_inst1 (Fin nL) (I.List_finRange nL) QL (fun o => I.Fin_val nL o)).
Proof.
  have E := co_nat_logic _ _ Hn. subst nL. apply: coq_eq_to_imported_eq. apply: Logic.eq_sym.
  rewrite (imported_eq_to_coq_eq _ _ (I.Prosa_Validation_ClassicUniSuspensionIntervalsInterface_maxFiltered_finRange
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
  exact (csi_foldr_max _ _ (co_fam_related nR sub_nat_to_imported (fun i => if QR i then nat_of_ord i else 0)
           (fun oL => I.cond Lean.Nat (QL oL) (I.Fin_val _ oL) (sub_nat_to_imported 0)) 0 HF) (iota 0 nR)).
Qed.

Lemma csi_ite_rel bR bL (Hb : CtBoolRel bR bL) xR xL (Hx : SubNatRel xR xL) yR yL (Hy : SubNatRel yR yL) :
  SubNatRel (if bR then xR else yR)
    (I.ite Lean.Nat (Lean.eq bL I.Bool_true) (I.instDecidableEqBool bL I.Bool_true) xL yL).
Proof. rewrite (ct_bool_rel_logic _ _ Hb). destruct bR; [exact Hx | exact Hy]. Qed.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma csi_LE_time_after_last_execution (Job : eqType) aR aL (Ha : CsiParRel Job aR aL)
    sR sL (Hs : CsiSchedRel Job sR sL) j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (LastExecution.time_after_last_execution aR sR j tR)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_LastExecution_LastExecution_time_after_last_execution Job (ct_decidable_eq Job) aL sL j tL).
Proof.
  assert (HQ : CoOrdPredRel tR tL (fun o => UniprocessorSchedule.scheduled_at sR j o)
      (fun oL => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job (ct_decidable_eq Job) sL j (I.Fin_val tL oL))).
  { intros o oL Ho. exact (csi_US_scheduled_at Job sR sL Hs j _ _ Ho). }
  exact (csi_ite_rel _ _ (co_exists_rel tR tL Ht _ _ HQ) _ _
           (sub_add_correspondence _ _ _ _ (csi_max_rel tR tL Ht _ _ HQ) (sub_nat_rel_canonical 1)) _ _ (Ha j)).
Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Section SuspSusp.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSusp := (I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).

Definition CsiSuspRel (sR : Suspension.job_suspension Job) (sL : LSusp) : SProp :=
  forall j tR tL, SubNatRel tR tL -> SubNatRel (sR j tR) (sL j tL).

Definition csi_susp_to_target (sR : Suspension.job_suspension Job) : LSusp :=
  fun j tL => sub_nat_to_imported (sR j (sub_nat_to_rocq tL)).

Definition csi_susp_to_source (sL : LSusp) : Suspension.job_suspension Job :=
  fun j tR => sub_nat_to_rocq (sL j (sub_nat_to_imported tR)).

Lemma csi_susp_canonical sR : CsiSuspRel sR (csi_susp_to_target sR).
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  unfold csi_susp_to_target. rewrite sub_nat_rocq_roundtrip. exact (sub_nat_rel_canonical _).
Qed.

Lemma csi_susp_surjective sL : CsiSuspRel (csi_susp_to_source sL) sL.
Proof.
  intros j tR tL Ht. have E := cl_nat_logic _ _ Ht. subst tL.
  exact (sub_nat_rel_surjective _).
Qed.

Lemma csi_forall_susp (PR : Suspension.job_suspension Job -> Prop) (PL : LSusp -> SProp) :
  (forall sR sL, CsiSuspRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (csi_forall_cover _ _ CsiSuspRel csi_susp_to_target csi_susp_to_source csi_susp_canonical csi_susp_surjective PR PL). Qed.

End SuspSusp.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma csi_SU_job_suspension (Job : eqType) :
  And (forall sR : Suspension.job_suspension Job, CsiSuspRel Job sR (csi_susp_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job (ct_decidable_eq Job), CsiSuspRel Job (csi_susp_to_source Job sL) sL).
Proof. exact (And_intro _ _ (csi_susp_canonical Job) (csi_susp_surjective Job)). Qed.

Lemma csi_SU_total_suspension (Job : eqType) cR cL (Hc : CsiParRel Job cR cL) sR sL (Hs : CsiSuspRel Job sR sL) j :
  SubNatRel (Suspension.total_suspension cR sR j) (I.Prosa_Classic_Model_Suspension_Suspension_total_suspension Job (ct_decidable_eq Job) cL sL j).
Proof. exact (csi_ico 0 _ (cR j) (cL j) (sR j) (sL j) (sub_nat_rel_canonical 0) (Hc j) (Hs j)). Qed.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CsiSchedRel Job sR sL.
Variables (aR : Job -> nat) (aL : Job -> Lean.Nat) (cR : Job -> nat) (cL : Job -> Lean.Nat).
Hypotheses (Ha : CsiParRel Job aR aL) (Hc : CsiParRel Job cR cL).
Variables (nR : Suspension.job_suspension Job) (nL : I.Prosa_Classic_Model_Suspension_Suspension_job_suspension Job dJ).
Hypothesis Hn : CsiSuspRel Job nR nL.

Notation TALE := (csi_LE_time_after_last_execution Job aR aL Ha sR sL Hs).

Theorem SuspensionIntervals_suspension_duration_correspondence j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (SuspensionIntervals.suspension_duration aR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspension_duration Job dJ aL nL sL j tL).
Proof. exact (Hn j _ _ (csi_US_service Job sR sL Hs j _ _ (TALE j tR tL Ht))). Qed.

Theorem SuspensionIntervals_suspended_at_correspondence j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (SuspensionIntervals.suspended_at aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_at Job dJ aL cL nL sL j tL).
Proof.
  have HT := TALE j tR tL Ht.
  exact (ct_bool_and _ _ _ _ (ct_bool_not _ _ (csi_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht))
           (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Ht)
              (ct_decide_lt _ _ _ _ Ht (sub_add_correspondence _ _ _ _ HT (SuspensionIntervals_suspension_duration_correspondence j tR tL Ht))))).
Qed.

Theorem SuspensionIntervals_cumulative_suspension_during_correspondence j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (SuspensionIntervals.cumulative_suspension_during aR cR nR sR j t1R t2R)
    (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_cumulative_suspension_during Job dJ aL cL nL sL j t1L t2L).
Proof. exact (csi_ico _ _ _ _ _ _ H1 H2 (fun kR kL Hk => ct_bool_to_nat _ _ (SuspensionIntervals_suspended_at_correspondence j kR kL Hk))). Qed.

Theorem SuspensionIntervals_cumulative_suspension_correspondence j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (SuspensionIntervals.cumulative_suspension aR cR nR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_cumulative_suspension Job dJ aL cL nL sL j tL).
Proof. exact (SuspensionIntervals_cumulative_suspension_during_correspondence j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Theorem SuspensionIntervals_respects_self_suspensions_correspondence :
  PropSPropRel (SuspensionIntervals.respects_self_suspensions aR cR nR sR) (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_respects_self_suspensions Job dJ aL cL nL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csi_US_scheduled_at Job sR sL Hs j _ _ Ht)).
  exact (ct_imp _ _ _ _ (ct_bool_truth _ _ (SuspensionIntervals_suspended_at_correspondence j tR tL Ht)) csi_false_rel).
Qed.
End Defs.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Notation SUS := SuspensionIntervals_suspended_at_correspondence.
Notation DUR := SuspensionIntervals_suspension_duration_correspondence.
Notation RSS := SuspensionIntervals_respects_self_suspensions_correspondence.
Notation TALE := csi_LE_time_after_last_execution.

Definition src_same_service_in_suspension_interval (Job : eqType) : Prop :=
   ltac:(type_of_term (@SuspensionIntervals.same_service_in_suspension_interval Job)).
Definition tgt_same_service_in_suspension_interval (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_same_service_in_suspension_interval Job (ct_decidable_eq Job))).

Theorem SuspensionIntervals_same_service_in_suspension_interval_correspondence (Job : eqType) :
  PropSPropRel (src_same_service_in_suspension_interval Job) (tgt_same_service_in_suspension_interval Job).
Proof.
  unfold src_same_service_in_suspension_interval, tgt_same_service_in_suspension_interval.
  apply: csi_forall_par => aR aL Ha. apply: csi_forall_par => cR cL Hc. apply: csi_forall_susp => nR nL Hn.
  apply: csi_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (RSS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => iR iL Hi.
  have HT := TALE Job aR aL Ha sR sL Hs j tR tL Ht.
  apply: ct_imp.
  { exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Hi)
       (ct_decide_le _ _ _ _ Hi (sub_add_correspondence _ _ _ _ HT (DUR Job sR sL Hs aR aL Ha nR nL Hn j tR tL Ht))))). }
  exact (sub_nat_eq_correspondence _ _ _ _ (csi_US_service Job sR sL Hs j _ _ Hi) (csi_US_service Job sR sL Hs j _ _ HT)).
Qed.
Definition src_suspended_in_suspension_interval (Job : eqType) : Prop :=
   ltac:(type_of_term (@SuspensionIntervals.suspended_in_suspension_interval Job)).
Definition tgt_suspended_in_suspension_interval (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_in_suspension_interval Job (ct_decidable_eq Job))).

Theorem SuspensionIntervals_suspended_in_suspension_interval_correspondence (Job : eqType) :
  PropSPropRel (src_suspended_in_suspension_interval Job) (tgt_suspended_in_suspension_interval Job).
Proof.
  unfold src_suspended_in_suspension_interval, tgt_suspended_in_suspension_interval.
  apply: csi_forall_par => aR aL Ha. apply: csi_forall_par => cR cL Hc. apply: csi_forall_susp => nR nL Hn.
  apply: csi_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (RSS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => iR iL Hi.
  have HT := TALE Job aR aL Ha sR sL Hs j tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (csi_US_completed_by Job sR sL Hs cR cL Hc j _ _ Hi))).
  apply: ct_imp.
  { exact (ct_bool_truth _ _ (ct_bool_and _ _ _ _ (ct_decide_le _ _ _ _ HT Hi)
       (ct_decide_lt _ _ _ _ Hi (sub_add_correspondence _ _ _ _ HT (DUR Job sR sL Hs aR aL Ha nR nL Hn j tR tL Ht))))). }
  exact (ct_bool_truth _ _ (SUS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Hi)).
Qed.
Definition src_suspended_implies_arrived (Job : eqType) : Prop :=
   ltac:(type_of_term (@SuspensionIntervals.suspended_implies_arrived Job)).
Definition tgt_suspended_implies_arrived (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_implies_arrived Job (ct_decidable_eq Job))).

Theorem SuspensionIntervals_suspended_implies_arrived_correspondence (Job : eqType) :
  PropSPropRel (src_suspended_implies_arrived Job) (tgt_suspended_implies_arrived Job).
Proof.
  unfold src_suspended_implies_arrived, tgt_suspended_implies_arrived.
  apply: csi_forall_par => aR aL Ha. apply: csi_forall_par => cR cL Hc. apply: csi_forall_susp => nR nL Hn.
  apply: csi_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SUS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht)).
  exact (ct_bool_truth _ _ (csi_has_arrived Job aR aL Ha j _ _ Ht)).
Qed.
Definition src_suspended_implies_not_completed (Job : eqType) : Prop :=
   ltac:(type_of_term (@SuspensionIntervals.suspended_implies_not_completed Job)).
Definition tgt_suspended_implies_not_completed (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_suspended_implies_not_completed Job (ct_decidable_eq Job))).

Theorem SuspensionIntervals_suspended_implies_not_completed_correspondence (Job : eqType) :
  PropSPropRel (src_suspended_implies_not_completed Job) (tgt_suspended_implies_not_completed Job).
Proof.
  unfold src_suspended_implies_not_completed, tgt_suspended_implies_not_completed.
  apply: csi_forall_par => aR aL Ha. apply: csi_forall_par => cR cL Hc. apply: csi_forall_susp => nR nL Hn.
  apply: csi_forall_sched => sR sL Hs.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (SUS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht)).
  exact (ct_bool_truth _ _ (ct_bool_not _ _ (csi_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht))).
Qed.
Definition src_cumulative_suspension_le_total_suspension (Job : eqType) : Prop :=
   ltac:(type_of_term (@SuspensionIntervals.cumulative_suspension_le_total_suspension Job)).
Definition tgt_cumulative_suspension_le_total_suspension (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_cumulative_suspension_le_total_suspension Job (ct_decidable_eq Job))).

Theorem SuspensionIntervals_cumulative_suspension_le_total_suspension_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_suspension_le_total_suspension Job) (tgt_cumulative_suspension_le_total_suspension Job).
Proof.
  unfold src_cumulative_suspension_le_total_suspension, tgt_cumulative_suspension_le_total_suspension.
  apply: csi_forall_par => aR aL Ha. apply: csi_forall_par => cR cL Hc. apply: csi_forall_susp => nR nL Hn.
  apply: csi_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (RSS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
  apply: ct_forall_identity => j. apply: ct_forall_nat => t1R t1L H1. apply: ct_forall_nat => t2R t2L H2.
  exact (sub_nat_le_correspondence _ _ _ _ (SuspensionIntervals_cumulative_suspension_during_correspondence Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ H1 _ _ H2)
           (csi_SU_total_suspension Job cR cL Hc nR nL Hn j)).
Qed.
Definition src_cumulative_suspension_eq_total_suspension (Job : eqType) : Prop :=
   ltac:(type_of_term (@SuspensionIntervals.cumulative_suspension_eq_total_suspension Job)).
Definition tgt_cumulative_suspension_eq_total_suspension (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_cumulative_suspension_eq_total_suspension Job (ct_decidable_eq Job))).

Theorem SuspensionIntervals_cumulative_suspension_eq_total_suspension_correspondence (Job : eqType) :
  PropSPropRel (src_cumulative_suspension_eq_total_suspension Job) (tgt_cumulative_suspension_eq_total_suspension Job).
Proof.
  unfold src_cumulative_suspension_eq_total_suspension, tgt_cumulative_suspension_eq_total_suspension.
  apply: csi_forall_par => aR aL Ha. apply: csi_forall_par => cR cL Hc. apply: csi_forall_susp => nR nL Hn.
  apply: csi_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (RSS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csi_US_completed_by Job sR sL Hs cR cL Hc j _ _ Ht)).
  exact (sub_nat_eq_correspondence _ _ _ _ (SuspensionIntervals_cumulative_suspension_correspondence Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht)
           (csi_SU_total_suspension Job cR cL Hc nR nL Hn j)).
Qed.
Definition src_executes_before_suspension (Job : eqType) : Prop :=
   ltac:(type_of_term (@SuspensionIntervals.executes_before_suspension Job)).
Definition tgt_executes_before_suspension (Job : eqType) : SProp :=
   ltac:(type_of_term (I.Prosa_Classic_Model_Schedule_Uni_Susp_SuspensionIntervals_SuspensionIntervals_executes_before_suspension Job (ct_decidable_eq Job))).

Theorem SuspensionIntervals_executes_before_suspension_correspondence (Job : eqType) :
  PropSPropRel (src_executes_before_suspension Job) (tgt_executes_before_suspension Job).
Proof.
  unfold src_executes_before_suspension, tgt_executes_before_suspension.
  apply: csi_forall_par => aR aL Ha. apply: csi_forall_par => cR cL Hc. apply: csi_forall_susp => nR nL Hn.
  apply: csi_forall_sched => sR sL Hs.
  apply: ct_imp; first exact (csi_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (csi_US_completed_jobs_dont_execute Job sR sL Hs cR cL Hc).
  apply: ct_imp; first exact (RSS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn).
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (csi_has_arrived Job aR aL Ha j _ _ Ht)).
  apply: ct_imp; first exact (ct_bool_truth _ _ (ct_bool_not _ _ (SUS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ Ht))).
  apply: ct_imp; first exact (ct_bool_truth _ _ (SUS Job sR sL Hs aR aL cR cL Ha Hc nR nL Hn j _ _ (csi_succ_rel _ _ Ht))).
  exact (ct_bool_truth _ _ (csi_US_scheduled_at Job sR sL Hs j _ _ Ht)).
Qed.
