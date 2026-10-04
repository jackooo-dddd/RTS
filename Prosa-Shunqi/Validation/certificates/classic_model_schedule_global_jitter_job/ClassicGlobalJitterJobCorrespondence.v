From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop.
From prosa Require Import classic.model.time classic.model.arrival.basic.job classic.model.schedule.global.jitter.job.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicGlobalJitterJob.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicGlobalJitterJobBase ClassicGlobalJitterJobList.

Module I := ImportedClassicGlobalJitterJob.
Local Open Scope nat_scope.

(** Certificates for [classic/model/schedule/global/jitter/job.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean [DecidableEq] instances given by the
    eqTypes' decision procedures ([ct_decidable_eq]); [job_task] identified; job and task parameters [X -> time]
    pointwise through [SubNatRel]; all with two-way totals.  The imported [Job] definitions are related as in the
    accepted classic job certificate (re-bound below to this export). *)

Ltac type_of_term t := let T := type of t in exact T.
Notation cid := (fun z => z).

(* ------------------------------------------------------------------ *)
(** * Helpers (re-bound to this export from the accepted classic certificates) *)

(** Base definitions (as in the accepted classic base library), provided here when this export's library lacks them. *)

(* ------------------------------------------------------------------ *)
(** * Generic covers and helpers *)

Lemma cgj_forall_cover (A B : Type) (Rel : A -> B -> SProp) (toB : A -> B) (toA : B -> A)
    (HB : forall a, Rel a (toB a)) (HA : forall b, Rel (toA b) b) (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) -> PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HA b)) (HR _)).
  - intro HL. apply strictly_inhabits. intro a. exact (sprop_to_prop _ _ (H _ _ (HB a)) (HL _)).
Qed.

Lemma cgj_false_rel : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - exact ct_coq_false_to_target.
  - exact ct_target_false_to_strict.
Qed.

Lemma cgj_succ_rel nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) nL
                     (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1))).
Proof. intro Hn. exact (sub_imported_eq_congr Lean.Nat_succ _ _ Hn). Qed.

(* ------------------------------------------------------------------ *)
(** * Big concatenation over a half-open interval (as in the accepted arrival_sequence certificate) *)

Definition CgjParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cgj_forall_par (T : Type) (PR : (T -> nat) -> Prop) (PL : (T -> Lean.Nat) -> SProp) :
  (forall pR pL, CgjParRel T pR pL -> PropSPropRel (PR pR) (PL pL)) -> PropSPropRel (forall p, PR p) (forall p, PL p).
Proof.
  exact (cgj_forall_cover _ _ (CgjParRel T) (fun pR j => sub_nat_to_imported (pR j)) (fun pL j => sub_nat_to_rocq (pL j))
           (fun pR j => sub_nat_rel_canonical (pR j)) (fun pL j => sub_nat_rel_surjective (pL j)) PR PL).
Qed.

(** The imported [Job] definitions (as in the accepted classic job certificate). *)
Section JobDefs.
Notation c0 := (sub_nat_rel_canonical 0).
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Lemma cgj_J_job_cost_positive cR cL (Hc : CgjParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Lemma cgj_J_job_deadline_positive dR dL (Hd : CgjParRel Job dR dL) j :
  CtBoolRel (Job.job_deadline_positive dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_positive Job dJ dL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd j)). Qed.

Lemma cgj_J_job_cost_le_deadline cR cL dR dL (Hc : CgjParRel Job cR cL) (Hd : CgjParRel Job dR dL) j :
  CtBoolRel (Job.job_cost_le_deadline cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_deadline Job dJ cL dL j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Hd j)). Qed.

Lemma cgj_J_valid_realtime_job cR cL dR dL (Hc : CgjParRel Job cR cL) (Hd : CgjParRel Job dR dL) j :
  PropSPropRel (Job.valid_realtime_job cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_realtime_job Job dJ cL dL j).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (cgj_J_job_cost_positive cR cL Hc j)).
  apply: ct_and; first exact (ct_bool_truth _ _ (cgj_J_job_cost_le_deadline cR cL dR dL Hc Hd j)).
  exact (ct_bool_truth _ _ (cgj_J_job_deadline_positive dR dL Hd j)).
Qed.

Lemma cgj_J_job_cost_le_task_cost tcR tcL (Htc : CgjParRel Task tcR tcL) cR cL (Hc : CgjParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Lemma cgj_J_job_deadline_eq_task_deadline tdR tdL (Htd : CgjParRel Task tdR tdL) dR dL (Hd : CgjParRel Job dR dL)
    (job_task : Job -> Task) j :
  PropSPropRel (Job.job_deadline_eq_task_deadline tdR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_eq_task_deadline Task dT tdL Job dJ dL job_task j).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))). Qed.

Lemma cgj_J_valid_sporadic_job tcR tcL tdR tdL (Htc : CgjParRel Task tcR tcL) (Htd : CgjParRel Task tdR tdL)
    cR cL dR dL (Hc : CgjParRel Job cR cL) (Hd : CgjParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task dT tcL tdL Job dJ cL dL job_task j).
Proof.
  apply: ct_and; first exact (cgj_J_valid_realtime_job cR cL dR dL Hc Hd j).
  apply: ct_and; first exact (ct_bool_truth _ _ (cgj_J_job_cost_le_task_cost tcR tcL Htc cR cL Hc job_task j)).
  exact (cgj_J_job_deadline_eq_task_deadline tdR tdL Htd dR dL Hd job_task j).
Qed.

End JobDefs.



(* ------------------------------------------------------------------ *)
(** * Definitions *)

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Theorem JobWithJitter_job_jitter_leq_task_jitter_correspondence tjR tjL (Htj : CgjParRel Task tjR tjL)
    jjR jjL (Hjj : CgjParRel Job jjR jjL) (job_task : Job -> Task) j :
  CtBoolRel (JobWithJitter.job_jitter_leq_task_jitter tjR job_task jjR j)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Job_JobWithJitter_job_jitter_leq_task_jitter Task dT tjL Job dJ job_task jjL j).
Proof. exact (ct_decide_le _ _ _ _ (Hjj j) (Htj (job_task j))). Qed.

Theorem JobWithJitter_valid_sporadic_job_with_jitter_correspondence tcR tcL tdR tdL tjR tjL
    (Htc : CgjParRel Task tcR tcL) (Htd : CgjParRel Task tdR tdL) (Htj : CgjParRel Task tjR tjL)
    cR cL dR dL jjR jjL (Hc : CgjParRel Job cR cL) (Hd : CgjParRel Job dR dL) (Hjj : CgjParRel Job jjR jjL)
    (job_task : Job -> Task) j :
  PropSPropRel (JobWithJitter.valid_sporadic_job_with_jitter tcR tdR tjR cR dR job_task jjR j)
    (I.Prosa_Classic_Model_Schedule_Global_Jitter_Job_JobWithJitter_valid_sporadic_job_with_jitter Task dT tcL tdL tjL Job dJ cL dL job_task jjL j).
Proof.
  apply: ct_and; first exact (cgj_J_valid_sporadic_job Task Job tcR tcL tdR tdL Htc Htd cR cL dR dL Hc Hd job_task j).
  exact (ct_bool_truth _ _ (JobWithJitter_job_jitter_leq_task_jitter_correspondence tjR tjL Htj jjR jjL Hjj job_task j)).
Qed.
End Defs.
