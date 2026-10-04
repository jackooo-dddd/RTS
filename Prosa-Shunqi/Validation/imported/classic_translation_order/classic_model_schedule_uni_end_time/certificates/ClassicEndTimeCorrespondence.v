From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job classic.model.schedule.uni.schedule classic.model.schedule.uni.end_time.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicEndTime.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicEndTimeBase ClassicEndTimeList.



Module I := ImportedClassicEndTime.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/uni/end_time.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job type is an [eqType], identified, with the Lean [DecidableEq] instance given by the eqType's decision
    procedure ([ct_decidable_eq]); times, costs and fuel by [SubNatRel]; job parameters pointwise through
    [SubNatRel]; uniprocessor schedules pointwise through the option map (two-way totals).  The inductive
    [diagnosis_option] is related constructor-wise ([OK]/[Failure] with related instants, an injective embedding
    with a left inverse); the fuel-bounded fixpoint [end_time_option] by induction on the fuel against the
    kernel-checked Lean equations [end_time_option_c0/_wf0/_step] exported with the artifact; the inductive
    [end_time_predicate] (Rocq [Prop], Lean [Prop] = [SProp] after import) constructor-wise in both directions by
    induction on the derivations; the uniprocessor service (a [Finset.Ico] sum) through the projection fixture as
    in the accepted platform-definitions certificate. *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cet_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cet_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cet_unmap_rel (T : Type) (l : I.List T) : ClListRel cid (cl_unmap cid l) l.
Proof. apply: coq_eq_to_imported_eq. exact (cl_map_unmap cid cid (fun _ => Logic.eq_refl _) l). Qed.

Lemma cet_cl_map_inj (T : Type) (s1 s2 : seq T) : Logic.eq (cl_map cid s1) (cl_map cid s2) -> Logic.eq s1 s2.
Proof.
  intro E. rewrite -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s1) -(cl_unmap_map cid cid (fun _ => Logic.eq_refl _) s2).
  by rewrite E.
Qed.

Lemma cet_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Lemma cet_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall sR sL, ClListRel (B := T) cid sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof.
  exact (cet_forall_cover _ _ (fun sR sL => ClListRel (B := T) cid sR sL) (cl_map cid) (cl_unmap cid)
           (fun s => @Lean.eq_refl _ _) (fun l => cet_unmap_rel T l) PR PL).
Qed.

Definition CetParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cet_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CetParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cet_forall_cover _ _ (CetParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

Fixpoint cet_natl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cet_natl s') end.

Definition cet_one : Lean.Nat := I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1).

Lemma cet_iota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) cet_one) (cet_natl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) cet_one))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cet_natl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cet_cl_map_comp {A B C : Type} (f : A -> B) (g : B -> C) : forall s : seq A,
  Logic.eq (cl_map (fun x => g (f x)) s) (cl_map g (map f s)).
Proof. elim => [|x s IH] //=. by rewrite IH. Qed.

Lemma cet_cl_map_ext {A B : Type} (f g : A -> B) (H : forall x, Logic.eq (f x) (g x)) : forall s : seq A,
  Logic.eq (cl_map f s) (cl_map g s).
Proof. elim => [|x s IH] //=. by rewrite H IH. Qed.

Lemma cet_big_seq {A : Type} (F : nat -> seq A) : forall s : seq nat,
  Logic.eq (\big[cat/[::]]_(i <- s) F i) (flatten (map F s)).
Proof. elim => [|x s IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CetFamRel (A : Type) (fR : nat -> seq A) (fL : Lean.Nat -> I.List A) : SProp :=
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

Lemma cet_has_arrived pR pL (Hp : CetParRel Job pR pL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (ArrivalSequence.has_arrived pR j tR)
    (I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_has_arrived Job dJ pL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hp j) Ht). Qed.

End ArrivalDefs2.

Fixpoint cet_snatl (s : seq nat) : I.List_inst1 Lean.Nat :=
  match s with [::] => I.List_nil_inst1 _ | x :: s' => I.List_cons_inst1 _ (sub_nat_to_imported x) (cet_snatl s') end.

Lemma cet_siota_range : forall n s,
  Logic.eq (I.List_range' (sub_nat_to_imported s) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)) (cet_snatl (iota s n)).
Proof.
  elim => [|n IH] s; first reflexivity.
  change (Logic.eq (I.List_cons_inst1 _ (sub_nat_to_imported s)
      (I.List_range' (sub_nat_to_imported (S s)) (sub_nat_to_imported n) (Lean.Nat_succ Lean.Nat_zero)))
    (I.List_cons_inst1 _ (sub_nat_to_imported s) (cet_snatl (iota (S s) n)))).
  by rewrite IH.
Qed.

Lemma cet_foldr_add (f : Lean.Nat -> Lean.Nat) (g : nat -> nat) (Hf : forall k, Logic.eq (f (sub_nat_to_imported k)) (sub_nat_to_imported (g k))) :
  forall s, Logic.eq (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cet_snatl s)))
                     (sub_nat_to_imported (foldr addn 0 (map g s))).
Proof.
  elim => [|k s IH] //=.
  change (Logic.eq (Lean.Nat_add (f (sub_nat_to_imported k))
            (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero (I.List_map_inst3 Lean.Nat Lean.Nat f (cet_snatl s))))
         (sub_nat_to_imported (g k + foldr addn 0 (map g s)))).
  rewrite IH Hf. exact (imported_eq_to_coq_eq _ _ (sub_add_canonical _ _)).
Qed.

Lemma cet_big_fold (xs : seq nat) (F : nat -> nat) : Logic.eq (\sum_(i <- xs) F i) (foldr addn 0 (map F xs)).
Proof. elim: xs => [|x xs IH]; first by rewrite big_nil. by rewrite big_cons IH. Qed.

Definition CetFunRel (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) : SProp :=
  forall kR kL, SubNatRel kR kL -> SubNatRel (FR kR) (FL kL).

Lemma cet_fun_canonical FR FL (HF : CetFunRel FR FL) k : Logic.eq (FL (sub_nat_to_imported k)) (sub_nat_to_imported (FR k)).
Proof. exact (cl_nat_logic _ _ (HF _ _ (sub_nat_rel_canonical k))). Qed.

Lemma cet_nat_sub_canonical (a b : nat) :
  Logic.eq (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b)) (sub_nat_to_imported (a - b)).
Proof.
  elim: b => [|b IH]; first by rewrite subn0.
  change (Logic.eq (I.Nat_pred (I.Nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))) (sub_nat_to_imported (a - b.+1))).
  rewrite IH subnS. case: (a - b) => [|k]; reflexivity.
Qed.

Lemma cet_ico mR mL nR nL FR FL (Hm : SubNatRel mR mL) (Hn : SubNatRel nR nL) (HF : CetFunRel FR FL) :
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (I.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add Lean.Nat_zero
       (I.List_map_inst3 Lean.Nat Lean.Nat FL (I.List_range' mL (I.Nat_sub nL mL) (Lean.Nat_succ Lean.Nat_zero)))).
Proof.
  rewrite (cl_nat_logic _ _ Hm) (cl_nat_logic _ _ Hn).
  have -> : Logic.eq (I.Nat_sub (sub_nat_to_imported nR) (sub_nat_to_imported mR)) (sub_nat_to_imported (nR - mR))
    := cet_nat_sub_canonical nR mR.
  rewrite cet_siota_range.
  apply: coq_eq_to_imported_eq. apply: Logic.eq_sym. rewrite (cet_foldr_add FL FR (cet_fun_canonical FR FL HF)).
  by rewrite cet_big_fold.
Qed.

(* ------------------------------------------------------------------ *)
(** * Options and uniprocessor schedules *)

(** Transport along the target equality (definitional UIP), as in the accepted global schedule certificate. *)
Definition cet_tr {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> Type) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Definition cet_trs {A : Type} {x y : A} (E : Lean.eq x y) (P : A -> SProp) (h : P x) : P y :=
  match E in Lean.eq _ z return P z with Lean.eq_refl => h end.

Lemma cet_opt_inj (A : Type) (o1 o2 : option A) : Logic.eq (cl_opt o1) (cl_opt o2) -> Logic.eq o1 o2.
Proof. intro E. by rewrite -(cl_unopt_opt o1) -(cl_unopt_opt o2) E. Qed.

Lemma cet_opt_eqb_rel (A : eqType) (o1 o2 : option A) :
  PropSPropRel (is_true (o1 == o2)) (Lean.eq (cl_opt o1) (cl_opt o2)).
Proof.
  apply prop_sprop_rel_intro.
  - move=> /eqP E. rewrite E. exact (@Lean.eq_refl _ _).
  - intro E. apply strictly_inhabits. apply/eqP. exact (cet_opt_inj A o1 o2 (imported_eq_to_coq_eq _ _ E)).
Qed.

Section Sched.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Notation LSched := (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).

Definition CetSchedRel (sR : UniprocessorSchedule.schedule Job) (sL : LSched) : SProp :=
  forall tR tL, SubNatRel tR tL -> Lean.eq (cl_opt (sR tR)) (sL tL).

Definition cet_sched_to_target (sR : UniprocessorSchedule.schedule Job) : LSched := fun tL => cl_opt (sR (sub_nat_to_rocq tL)).
Definition cet_sched_to_source (sL : LSched) : UniprocessorSchedule.schedule Job := fun tR => cl_unopt (sL (sub_nat_to_imported tR)).

Lemma cet_sched_canonical sR : CetSchedRel sR (cet_sched_to_target sR).
Proof. intros tR tL Ht. apply: coq_eq_to_imported_eq. by rewrite /cet_sched_to_target (cl_nat_input _ _ Ht). Qed.

Lemma cet_sched_surjective sL : CetSchedRel (cet_sched_to_source sL) sL.
Proof.
  intros tR tL Ht. apply: coq_eq_to_imported_eq. rewrite /cet_sched_to_source cl_opt_unopt.
  by rewrite (cl_nat_logic _ _ Ht).
Qed.

Lemma cet_forall_sched (PR : UniprocessorSchedule.schedule Job -> Prop) (PL : LSched -> SProp) :
  (forall sR sL, CetSchedRel sR sL -> PropSPropRel (PR sR) (PL sL)) -> PropSPropRel (forall s, PR s) (forall s, PL s).
Proof. exact (cet_forall_cover _ _ CetSchedRel cet_sched_to_target cet_sched_to_source cet_sched_canonical cet_sched_surjective PR PL). Qed.

End Sched.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cet_US_schedule (Job : eqType) :
  And (forall sR : UniprocessorSchedule.schedule Job, CetSchedRel Job sR (cet_sched_to_target Job sR))
      (forall sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job (ct_decidable_eq Job), CetSchedRel Job (cet_sched_to_source Job sL) sL).
Proof. exact (And_intro _ _ (cet_sched_canonical Job) (cet_sched_surjective Job)). Qed.

Section USchedDefs.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CetSchedRel Job sR sL.

Lemma cet_US_scheduled_at j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.scheduled_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_scheduled_at Job dJ sL j tL).
Proof.
  apply: ct_decide_bool.
  exact (cet_tr (Hs tR tL Ht) (fun z => PropSPropRel (sR tR == Some j) (Lean.eq z (cl_opt (Some j))))
           (cet_opt_eqb_rel Job (sR tR) (Some j))).
Qed.

Lemma cet_US_service_at j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service_at sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j tL).
Proof. exact (ct_bool_to_nat _ _ (cet_US_scheduled_at j tR tL Ht)). Qed.

Lemma cet_service_at_fun j : CetFunRel (fun t => UniprocessorSchedule.service_at sR j t) (fun t => I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_at Job dJ sL j t).
Proof. intros kR kL Hk. exact (cet_US_service_at j kR kL Hk). Qed.

Lemma cet_US_service_during j t1R t1L (H1 : SubNatRel t1R t1L) t2R t2L (H2 : SubNatRel t2R t2L) :
  SubNatRel (UniprocessorSchedule.service_during sR j t1R t2R) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service_during Job dJ sL j t1L t2L).
Proof. exact (cet_ico _ _ _ _ _ _ H1 H2 (cet_service_at_fun j)). Qed.

Lemma cet_US_service j tR tL (Ht : SubNatRel tR tL) :
  SubNatRel (UniprocessorSchedule.service sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_service Job dJ sL j tL).
Proof. exact (cet_US_service_during j 0 _ (sub_nat_rel_canonical 0) tR tL Ht). Qed.

Lemma cet_US_completed_by cR cL (Hc : CetParRel Job cR cL) j tR tL (Ht : SubNatRel tR tL) :
  CtBoolRel (UniprocessorSchedule.completed_by cR sR j tR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_completed_by Job dJ cL sL j tL).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (cet_US_service j tR tL Ht)). Qed.

Lemma cet_US_jobs_must_arrive_to_execute aR aL (Ha : CetParRel Job aR aL) :
  PropSPropRel (UniprocessorSchedule.jobs_must_arrive_to_execute aR sR) (I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_jobs_must_arrive_to_execute Job dJ aL sL).
Proof.
  apply: ct_forall_identity => j. apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cet_US_scheduled_at j tR tL Ht)).
  exact (ct_bool_truth _ _ (cet_has_arrived Job aR aL Ha j tR tL Ht)).
Qed.

End USchedDefs.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cet_J_job_cost_positive cR cL (Hc : CetParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cet_J_job_deadline_positive dR dL (Hd : CetParRel Job dR dL) j :
  CtBoolRel (Job.job_deadline_positive dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_positive Job dJ dL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd j)). Qed.

Lemma cet_J_job_cost_le_deadline cR cL dR dL (Hc : CetParRel Job cR cL) (Hd : CetParRel Job dR dL) j :
  CtBoolRel (Job.job_cost_le_deadline cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_deadline Job dJ cL dL j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Hd j)). Qed.

Lemma cet_J_valid_realtime_job cR cL dR dL (Hc : CetParRel Job cR cL) (Hd : CetParRel Job dR dL) j :
  PropSPropRel (Job.valid_realtime_job cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_realtime_job Job dJ cL dL j).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (cet_J_job_cost_positive cR cL Hc j)).
  apply: ct_and; first exact (ct_bool_truth _ _ (cet_J_job_cost_le_deadline cR cL dR dL Hc Hd j)).
  exact (ct_bool_truth _ _ (cet_J_job_deadline_positive dR dL Hd j)).
Qed.

End JobDefs.

Lemma cet_pred_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.-1 (ct_sub nL (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof.
  intro Hn. apply: coq_eq_to_imported_eq. rewrite -subn1.
  exact (imported_eq_to_coq_eq _ _ (ct_sub_rel _ _ _ _ Hn (sub_nat_rel_canonical 1))).
Qed.

(* ------------------------------------------------------------------ *)
(** * [diagnosis_option] (constructor-wise, related instants) *)

Notation nc := sub_nat_to_imported.
Notation EQ H := (imported_eq_to_coq_eq _ _ H).

Definition cet_dg_to_target (d : end_time.diagnosis_option) : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option :=
  match d with
  | end_time.OK t => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK (nc t)
  | end_time.Failure t => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_Failure (nc t)
  end.
Definition cet_dg_to_source (d : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option) : end_time.diagnosis_option :=
  match d with
  | I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK t => end_time.OK (sub_nat_to_rocq t)
  | I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_Failure t => end_time.Failure (sub_nat_to_rocq t)
  end.
Definition CetDgRel (dR : end_time.diagnosis_option) (dL : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option) : SProp :=
  Lean.eq (cet_dg_to_target dR) dL.

Lemma cet_dg_ts d : Logic.eq (cet_dg_to_source (cet_dg_to_target d)) d.
Proof. case: d => t /=; by rewrite sub_nat_rocq_roundtrip. Qed.

Lemma cet_dg_eq dR1 dL1 dR2 dL2 (H1 : CetDgRel dR1 dL1) (H2 : CetDgRel dR2 dL2) :
  PropSPropRel (Logic.eq dR1 dR2) (Lean.eq dL1 dL2).
Proof.
  rewrite -(EQ H1) -(EQ H2). clear H1 H2. apply prop_sprop_rel_intro.
  - move=> ->. exact (@Lean.eq_refl _ _).
  - move=> E. apply strictly_inhabits. have E' := f_equal cet_dg_to_source (EQ E). by rewrite !cet_dg_ts in E'.
Qed.

Lemma cet_OK tR tL (Ht : SubNatRel tR tL) : CetDgRel (end_time.OK tR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK tL).
Proof. exact (sub_imported_eq_congr (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option_OK) _ _ Ht). Qed.

Lemma cet_not_rel (P : Prop) (PL : SProp) : PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof. intro H. exact (ct_imp _ _ _ _ H cet_false_rel). Qed.

(* ------------------------------------------------------------------ *)
(** * [end_time_option] and [end_time_predicate] *)

Section EndTime.
Variable Job : eqType.
Notation dJ := (ct_decidable_eq Job).
Variables (sR : UniprocessorSchedule.schedule Job) (sL : I.Prosa_Classic_Model_Schedule_Uni_Schedule_UniprocessorSchedule_schedule Job dJ).
Hypothesis Hs : CetSchedRel Job sR sL.
Variable job : Job.
Notation SA := (cet_US_scheduled_at Job sR sL Hs job).

Lemma cet_end_time_option_eq : forall wR tR cR,
  Logic.eq (cet_dg_to_target (end_time.end_time_option sR job tR cR wR))
           (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_option Job dJ sL job (nc tR) (nc cR) (nc wR)).
Proof.
  elim => [|w IH] tR [|c].
  - exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicEndTimeInterface_end_time_option_c0 Job dJ sL job (nc tR) (nc 0)))).
  - exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicEndTimeInterface_end_time_option_wf0 Job dJ sL job (nc tR) (nc c)))).
  - exact (Logic.eq_sym (EQ (I.Prosa_Validation_ClassicEndTimeInterface_end_time_option_c0 Job dJ sL job (nc tR) (nc w.+1)))).
  - rewrite (EQ (I.Prosa_Validation_ClassicEndTimeInterface_end_time_option_step Job dJ sL job (nc tR) (nc c) (nc w))).
    have ER : Logic.eq (end_time.end_time_option sR job tR c.+1 w.+1)
      (if UniprocessorSchedule.scheduled_at sR job tR then end_time.end_time_option sR job tR.+1 c w
       else end_time.end_time_option sR job tR.+1 c.+1 w) by [].
    rewrite ER (ct_bool_rel_logic _ _ (SA tR _ (sub_nat_rel_canonical tR))).
    case: (UniprocessorSchedule.scheduled_at sR job tR).
    + exact (IH tR.+1 c).
    + exact (IH tR.+1 c.+1).
Qed.

Lemma cet_end_time_option tR tL (Ht : SubNatRel tR tL) cR cL (Hc : SubNatRel cR cL) wR wL (Hw : SubNatRel wR wL) :
  CetDgRel (end_time.end_time_option sR job tR cR wR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_option Job dJ sL job tL cL wL).
Proof.
  have Et := cl_nat_logic _ _ Ht. have Ec := cl_nat_logic _ _ Hc. have Ew := cl_nat_logic _ _ Hw. subst tL cL wL.
  exact (coq_eq_to_imported_eq _ _ (cet_end_time_option_eq wR tR cR)).
Qed.

Lemma cet_etp_fwd tR cR eR :
  end_time.end_time_predicate sR job tR cR eR -> I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job dJ sL job (nc tR) (nc cR) (nc eR).
Proof.
  intro H.
  refine (end_time.end_time_predicate_sind sR job (fun t c e => I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job dJ sL job (nc t) (nc c) (nc e)) _ _ _ tR cR eR H).
  - intro t. exact (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate_C0_ Job dJ sL job (nc t)).
  - intros t c e Hn _ IH. exact (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate_S_C_not_sched Job dJ sL job (nc t) (nc c) (nc e)
      (prop_to_sprop _ _ (cet_not_rel _ _ (ct_bool_truth _ _ (SA t _ (sub_nat_rel_canonical t)))) Hn) IH).
  - intros t c e Hy _ IH. exact (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate_S_C_sched Job dJ sL job (nc t) (nc c) (nc e)
      (prop_to_sprop _ _ (ct_bool_truth _ _ (SA t _ (sub_nat_rel_canonical t))) Hy) IH).
Qed.

Lemma cet_back_rel tL : SubNatRel (sub_nat_to_rocq tL) tL.
Proof. exact (sub_nat_imported_roundtrip tL). Qed.

Lemma cet_etp_bwd tL cL eL :
  I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job dJ sL job tL cL eL ->
  StrictlyInhabited (end_time.end_time_predicate sR job (sub_nat_to_rocq tL) (sub_nat_to_rocq cL) (sub_nat_to_rocq eL)).
Proof.
  intro H. induction H as [t | t c e Hn _ IH | t c e Hy _ IH].
  - exact (strictly_inhabits (end_time.C0_ sR job (sub_nat_to_rocq t))).
  - exact (match IH with strictly_inhabits p =>
      strictly_inhabits (end_time.S_C_not_sched sR job (sub_nat_to_rocq t) (sub_nat_to_rocq c) (sub_nat_to_rocq e)
        (sprop_to_prop _ _ (cet_not_rel _ _ (ct_bool_truth _ _ (SA _ _ (cet_back_rel t)))) Hn) p) end).
  - exact (match IH with strictly_inhabits p =>
      strictly_inhabits (end_time.S_C_sched sR job (sub_nat_to_rocq t) (sub_nat_to_rocq c) (sub_nat_to_rocq e)
        (sprop_to_prop _ _ (ct_bool_truth _ _ (SA _ _ (cet_back_rel t))) Hy) p) end).
Qed.

Lemma cet_etp tR tL (Ht : SubNatRel tR tL) cR cL (Hc : SubNatRel cR cL) eR eL (He : SubNatRel eR eL) :
  PropSPropRel (end_time.end_time_predicate sR job tR cR eR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job dJ sL job tL cL eL).
Proof.
  have Et := cl_nat_logic _ _ Ht. have Ec := cl_nat_logic _ _ Hc. have Ee := cl_nat_logic _ _ He. subst tL cL eL.
  apply prop_sprop_rel_intro; first exact (cet_etp_fwd tR cR eR).
  intro H. have S := cet_etp_bwd _ _ _ H. rewrite !sub_nat_rocq_roundtrip in S. exact S.
Qed.

End EndTime.

(* ------------------------------------------------------------------ *)
(** * Definitions *)

Lemma cet_dg_st d : Logic.eq (cet_dg_to_target (cet_dg_to_source d)) d.
Proof.
  case: d => t /=; by rewrite (EQ (sub_nat_imported_roundtrip t)).
Qed.

(** The inductive [diagnosis_option]: the constructor-wise relation is total in both directions. *)
Theorem end_time_diagnosis_option_correspondence :
  And (forall dR : end_time.diagnosis_option, CetDgRel dR (cet_dg_to_target dR))
      (forall dL : I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_diagnosis_option, CetDgRel (cet_dg_to_source dL) dL).
Proof.
  exact (And_intro _ _ (fun dR => @Lean.eq_refl _ _) (fun dL => coq_eq_to_imported_eq _ _ (cet_dg_st dL))).
Qed.

(** The inductive [end_time_predicate]: equivalent at related inputs (both directions by induction). *)
Theorem end_time_end_time_predicate_correspondence (Job : eqType) sR sL (Hs : CetSchedRel Job sR sL) job
    tR tL (Ht : SubNatRel tR tL) cR cL (Hc : SubNatRel cR cL) eR eL (He : SubNatRel eR eL) :
  PropSPropRel (@end_time.end_time_predicate Job sR job tR cR eR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate Job (ct_decidable_eq Job) sL job tL cL eL).
Proof. exact (cet_etp Job sR sL Hs job _ _ Ht _ _ Hc _ _ He). Qed.

Theorem end_time_end_time_option_correspondence (Job : eqType) sR sL (Hs : CetSchedRel Job sR sL) job
    tR tL (Ht : SubNatRel tR tL) cR cL (Hc : SubNatRel cR cL) wR wL (Hw : SubNatRel wR wL) :
  CetDgRel (@end_time.end_time_option Job sR job tR cR wR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_option Job (ct_decidable_eq Job) sL job tL cL wL).
Proof. exact (cet_end_time_option Job sR sL Hs job _ _ Ht _ _ Hc _ _ Hw). Qed.

Theorem end_time_completes_at_correspondence (Job : eqType) aR aL (Ha : CetParRel Job aR aL) cR cL (Hc : CetParRel Job cR cL)
    sR sL (Hs : CetSchedRel Job sR sL) job tR tL (Ht : SubNatRel tR tL) :
  PropSPropRel (@end_time.completes_at Job aR cR sR job tR) (I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_completes_at Job (ct_decidable_eq Job) aL cL sL job tL).
Proof. exact (cet_etp Job sR sL Hs job _ _ (Ha job) _ _ (Hc job) _ _ Ht). Qed.

(* ------------------------------------------------------------------ *)
(** * Statements *)

Definition src_end_time_function_predicat_equivalence (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.end_time_function_predicat_equivalence Job)).
Definition tgt_end_time_function_predicat_equivalence (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_function_predicat_equivalence Job (ct_decidable_eq Job))).
Theorem end_time_end_time_function_predicat_equivalence_correspondence (Job : eqType) :
  PropSPropRel (src_end_time_function_predicat_equivalence Job) (tgt_end_time_function_predicat_equivalence Job).
Proof.
  unfold src_end_time_function_predicat_equivalence, tgt_end_time_function_predicat_equivalence.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_forall_nat => eR eL He. apply: ct_forall_nat => wR wL Hw. apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => cR cL Hc.
  apply: ct_imp; first exact (cet_dg_eq _ _ _ _ (cet_end_time_option Job sR sL Hs job _ _ Ht _ _ Hc _ _ Hw) (cet_OK _ _ He)).
  exact (cet_etp Job sR sL Hs job _ _ Ht _ _ Hc _ _ He).
Qed.

Definition src_end_time_predicat_function_equivalence (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.end_time_predicat_function_equivalence Job)).
Definition tgt_end_time_predicat_function_equivalence (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicat_function_equivalence Job (ct_decidable_eq Job))).
Theorem end_time_end_time_predicat_function_equivalence_correspondence (Job : eqType) :
  PropSPropRel (src_end_time_predicat_function_equivalence Job) (tgt_end_time_predicat_function_equivalence Job).
Proof.
  unfold src_end_time_predicat_function_equivalence, tgt_end_time_predicat_function_equivalence.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => cR cL Hc. apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (cet_etp Job sR sL Hs job _ _ Ht _ _ Hc _ _ He).
  apply: ct_exists_nat => wR wL Hw.
  exact (cet_dg_eq _ _ _ _ (cet_end_time_option Job sR sL Hs job _ _ Ht _ _ Hc _ _ Hw) (cet_OK _ _ He)).
Qed.

Definition src_end_time_predicate_not_sched (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.end_time_predicate_not_sched Job)).
Definition tgt_end_time_predicate_not_sched (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate_not_sched Job (ct_decidable_eq Job))).
Theorem end_time_end_time_predicate_not_sched_correspondence (Job : eqType) :
  PropSPropRel (src_end_time_predicate_not_sched Job) (tgt_end_time_predicate_not_sched Job).
Proof.
  unfold src_end_time_predicate_not_sched, tgt_end_time_predicate_not_sched.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => cR cL Hc. apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (cet_not_rel _ _ (ct_bool_truth _ _ (cet_US_scheduled_at Job sR sL Hs job _ _ Ht))).
  apply: ct_imp; first exact (cet_etp Job sR sL Hs job _ _ Ht _ _ (cet_succ_rel _ _ Hc) _ _ He).
  exact (cet_etp Job sR sL Hs job _ _ (cet_succ_rel _ _ Ht) _ _ (cet_succ_rel _ _ Hc) _ _ He).
Qed.

Definition src_end_time_predicate_sched (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.end_time_predicate_sched Job)).
Definition tgt_end_time_predicate_sched (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_predicate_sched Job (ct_decidable_eq Job))).
Theorem end_time_end_time_predicate_sched_correspondence (Job : eqType) :
  PropSPropRel (src_end_time_predicate_sched Job) (tgt_end_time_predicate_sched Job).
Proof.
  unfold src_end_time_predicate_sched, tgt_end_time_predicate_sched.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => cR cL Hc. apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (ct_bool_truth _ _ (cet_US_scheduled_at Job sR sL Hs job _ _ Ht)).
  apply: ct_imp; first exact (cet_etp Job sR sL Hs job _ _ Ht _ _ (cet_succ_rel _ _ Hc) _ _ He).
  exact (cet_etp Job sR sL Hs job _ _ (cet_succ_rel _ _ Ht) _ _ Hc _ _ He).
Qed.

Definition src_arrival_le_end (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.arrival_le_end Job)).
Definition tgt_arrival_le_end (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_arrival_le_end Job (ct_decidable_eq Job))).
Theorem end_time_arrival_le_end_correspondence (Job : eqType) :
  PropSPropRel (src_arrival_le_end Job) (tgt_arrival_le_end Job).
Proof.
  unfold src_arrival_le_end, tgt_arrival_le_end.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => cR cL Hc. apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (cet_etp Job sR sL Hs job _ _ Ht _ _ Hc _ _ He).
  exact (sub_nat_le_correspondence _ _ _ _ Ht He).
Qed.

Definition src_arrival_add_cost_le_end (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.arrival_add_cost_le_end Job)).
Definition tgt_arrival_add_cost_le_end (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_arrival_add_cost_le_end Job (ct_decidable_eq Job))).
Theorem end_time_arrival_add_cost_le_end_correspondence (Job : eqType) :
  PropSPropRel (src_arrival_add_cost_le_end Job) (tgt_arrival_add_cost_le_end Job).
Proof.
  unfold src_arrival_add_cost_le_end, tgt_arrival_add_cost_le_end.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_forall_nat => tR tL Ht. apply: ct_forall_nat => cR cL Hc. apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (cet_etp Job sR sL Hs job _ _ Ht _ _ Hc _ _ He).
  exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ Ht Hc) He).
Qed.

Definition src_service_eq_cost_at_end_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.service_eq_cost_at_end_time Job)).
Definition tgt_service_eq_cost_at_end_time (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_service_eq_cost_at_end_time Job (ct_decidable_eq Job))).
Theorem end_time_service_eq_cost_at_end_time_correspondence (Job : eqType) :
  PropSPropRel (src_service_eq_cost_at_end_time Job) (tgt_service_eq_cost_at_end_time Job).
Proof.
  unfold src_service_eq_cost_at_end_time, tgt_service_eq_cost_at_end_time.
  apply: (cet_forall_par Job) => aR aL Ha. apply: (cet_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (end_time_completes_at_correspondence Job aR aL Ha cR cL Hc sR sL Hs job _ _ He).
  exact (sub_nat_eq_correspondence _ _ _ _ (cet_US_service_during Job sR sL Hs job _ _ (Ha job) _ _ He) (Hc job)).
Qed.

Definition src_completed_by_end_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.completed_by_end_time Job)).
Definition tgt_completed_by_end_time (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_completed_by_end_time Job (ct_decidable_eq Job))).
Theorem end_time_completed_by_end_time_correspondence (Job : eqType) :
  PropSPropRel (src_completed_by_end_time Job) (tgt_completed_by_end_time Job).
Proof.
  unfold src_completed_by_end_time, tgt_completed_by_end_time.
  apply: (cet_forall_par Job) => aR aL Ha. apply: (cet_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cet_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (end_time_completes_at_correspondence Job aR aL Ha cR cL Hc sR sL Hs job _ _ He).
  exact (ct_bool_truth _ _ (cet_US_completed_by Job sR sL Hs cR cL Hc job _ _ He)).
Qed.

Definition src_end_time_positive (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.end_time_positive Job)).
Definition tgt_end_time_positive (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_end_time_positive Job (ct_decidable_eq Job))).
Theorem end_time_end_time_positive_correspondence (Job : eqType) :
  PropSPropRel (src_end_time_positive Job) (tgt_end_time_positive Job).
Proof.
  unfold src_end_time_positive, tgt_end_time_positive.
  apply: (cet_forall_par Job) => aR aL Ha. apply: (cet_forall_par Job) => cR cL Hc.
  apply: (cet_forall_par Job) => dR dL Hd.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cet_US_jobs_must_arrive_to_execute Job sR sL Hs aR aL Ha).
  apply: ct_imp; first exact (cet_J_valid_realtime_job Job cR cL dR dL Hc Hd job).
  apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (end_time_completes_at_correspondence Job aR aL Ha cR cL Hc sR sL Hs job _ _ He).
  exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical 0) He).
Qed.

Definition src_job_uncompletes_at_end_time_sub_1 (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.job_uncompletes_at_end_time_sub_1 Job)).
Definition tgt_job_uncompletes_at_end_time_sub_1 (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_job_uncompletes_at_end_time_sub_1 Job (ct_decidable_eq Job))).
Theorem end_time_job_uncompletes_at_end_time_sub_1_correspondence (Job : eqType) :
  PropSPropRel (src_job_uncompletes_at_end_time_sub_1 Job) (tgt_job_uncompletes_at_end_time_sub_1 Job).
Proof.
  unfold src_job_uncompletes_at_end_time_sub_1, tgt_job_uncompletes_at_end_time_sub_1.
  apply: (cet_forall_par Job) => aR aL Ha. apply: (cet_forall_par Job) => cR cL Hc.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (end_time_completes_at_correspondence Job aR aL Ha cR cL Hc sR sL Hs job _ _ He).
  exact (sub_nat_eq_correspondence _ _ _ _ (cet_US_service_during Job sR sL Hs job _ _ (Ha job) _ _ (cet_pred_rel _ _ He)) (cet_pred_rel _ _ (Hc job))).
Qed.

Definition src_job_uncompleted_before_end_time (Job : eqType) : Prop :=
  ltac:(type_of_term (@end_time.job_uncompleted_before_end_time Job)).
Definition tgt_job_uncompleted_before_end_time (Job : eqType) : SProp :=
  ltac:(type_of_term (@I.Prosa_Classic_Model_Schedule_Uni_EndTime_end_time_job_uncompleted_before_end_time Job (ct_decidable_eq Job))).
Theorem end_time_job_uncompleted_before_end_time_correspondence (Job : eqType) :
  PropSPropRel (src_job_uncompleted_before_end_time Job) (tgt_job_uncompleted_before_end_time Job).
Proof.
  unfold src_job_uncompleted_before_end_time, tgt_job_uncompleted_before_end_time.
  apply: (cet_forall_par Job) => aR aL Ha. apply: (cet_forall_par Job) => cR cL Hc.
  apply: (cet_forall_par Job) => dR dL Hd.
  apply: ct_forall_identity => job. apply: (cet_forall_sched Job) => sR sL Hs.
  apply: ct_imp; first exact (cet_J_valid_realtime_job Job cR cL dR dL Hc Hd job).
  apply: ct_forall_nat => eR eL He.
  apply: ct_imp; first exact (end_time_completes_at_correspondence Job aR aL Ha cR cL Hc sR sL Hs job _ _ He).
  apply: ct_forall_nat => tR tL Ht.
  apply: ct_imp; first exact (ct_and _ _ _ _ (sub_nat_le_correspondence _ _ _ _ (Ha job) Ht) (sub_nat_le_correspondence _ _ _ _ Ht (cet_pred_rel _ _ He))).
  exact (sub_nat_lt_correspondence _ _ _ _ (cet_US_service_during Job sR sL Hs job _ _ (Ha job) _ _ Ht) (Hc job)).
Qed.
