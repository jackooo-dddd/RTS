From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From prosa Require Import classic.model.arrival.basic.arrival_sequence classic.model.arrival.basic.job.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedClassicJob.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence ClassicJobBase ClassicJobList.

Module I := ImportedClassicJob.
Local Open Scope nat_scope.

(** Certificates for [classic/model/arrival/basic/job.v] (ProsaBuddy classic, commit f692cb7).

    Inputs: the job and task types are [eqType]s, identified, with the Lean
    [DecidableEq] instances given by the eqTypes' decision procedures
    ([ct_decidable_eq]); [job_task] is identified; job and task parameters
    ([X -> time]) pointwise through [SubNatRel] ([CjParRel]); arrival sequences
    pointwise on related times, with job sequences elementwise ([CjArrRel], as for
    the accepted classic arrival_sequence certificate).  All definitions compute to
    related values on related inputs. *)

Notation cid := (fun z => z).

Definition CjParRel (T : Type) (pR : T -> nat) (pL : T -> Lean.Nat) : SProp := forall x, SubNatRel (pR x) (pL x).

Lemma cj_mem (T : eqType) x s sL : ClListRel cid s sL ->
  PropSPropRel (x \in s) (I.Membership_mem T (I.List T) (I.List_instMembership T) sL x).
Proof. exact (cl_mem_rel_list T T cid cid (fun _ => Logic.eq_refl _) x s sL). Qed.

Definition CjArrRel (Job : eqType) (aR : ArrivalSequence.arrival_sequence Job)
    (aL : I.Prosa_Classic_Model_Arrival_Basic_ArrivalSequence_ArrivalSequence_arrival_sequence Job (ct_decidable_eq Job)) : SProp :=
  forall tR tL, SubNatRel tR tL -> ClListRel cid (aR tR) (aL tL).

Notation c0 := (sub_nat_rel_canonical 0).

Section Defs.
Variables (Task Job : eqType).
Notation dT := (ct_decidable_eq Task).
Notation dJ := (ct_decidable_eq Job).

Theorem Job_job_cost_positive_correspondence cR cL (Hc : CjParRel Job cR cL) j :
  CtBoolRel (Job.job_cost_positive cR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_positive Job dJ cL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hc j)). Qed.

Theorem Job_job_deadline_positive_correspondence dR dL (Hd : CjParRel Job dR dL) j :
  CtBoolRel (Job.job_deadline_positive dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_positive Job dJ dL j).
Proof. exact (ct_decide_lt _ _ _ _ c0 (Hd j)). Qed.

Theorem Job_job_cost_le_deadline_correspondence cR cL dR dL (Hc : CjParRel Job cR cL) (Hd : CjParRel Job dR dL) j :
  CtBoolRel (Job.job_cost_le_deadline cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_deadline Job dJ cL dL j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Hd j)). Qed.

Theorem Job_valid_realtime_job_correspondence cR cL dR dL (Hc : CjParRel Job cR cL) (Hd : CjParRel Job dR dL) j :
  PropSPropRel (Job.valid_realtime_job cR dR j) (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_realtime_job Job dJ cL dL j).
Proof.
  apply: ct_and; first exact (ct_bool_truth _ _ (Job_job_cost_positive_correspondence cR cL Hc j)).
  apply: ct_and; first exact (ct_bool_truth _ _ (Job_job_cost_le_deadline_correspondence cR cL dR dL Hc Hd j)).
  exact (ct_bool_truth _ _ (Job_job_deadline_positive_correspondence dR dL Hd j)).
Qed.

Theorem Job_job_cost_le_task_cost_correspondence tcR tcL (Htc : CjParRel Task tcR tcL) cR cL (Hc : CjParRel Job cR cL)
    (job_task : Job -> Task) j :
  CtBoolRel (Job.job_cost_le_task_cost tcR cR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_cost_le_task_cost Task dT tcL Job dJ cL job_task j).
Proof. exact (ct_decide_le _ _ _ _ (Hc j) (Htc (job_task j))). Qed.

Theorem Job_job_deadline_eq_task_deadline_correspondence tdR tdL (Htd : CjParRel Task tdR tdL) dR dL (Hd : CjParRel Job dR dL)
    (job_task : Job -> Task) j :
  PropSPropRel (Job.job_deadline_eq_task_deadline tdR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_job_deadline_eq_task_deadline Task dT tdL Job dJ dL job_task j).
Proof. exact (sub_nat_eq_correspondence _ _ _ _ (Hd j) (Htd (job_task j))). Qed.

Theorem Job_valid_sporadic_job_correspondence tcR tcL tdR tdL (Htc : CjParRel Task tcR tcL) (Htd : CjParRel Task tdR tdL)
    cR cL dR dL (Hc : CjParRel Job cR cL) (Hd : CjParRel Job dR dL) (job_task : Job -> Task) j :
  PropSPropRel (Job.valid_sporadic_job tcR tdR cR dR job_task j)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_valid_sporadic_job Task dT tcL tdL Job dJ cL dL job_task j).
Proof.
  apply: ct_and; first exact (Job_valid_realtime_job_correspondence cR cL dR dL Hc Hd j).
  apply: ct_and; first exact (ct_bool_truth _ _ (Job_job_cost_le_task_cost_correspondence tcR tcL Htc cR cL Hc job_task j)).
  exact (Job_job_deadline_eq_task_deadline_correspondence tdR tdL Htd dR dL Hd job_task j).
Qed.

Theorem Job_cost_of_jobs_from_arrival_sequence_le_task_cost_correspondence tcR tcL (Htc : CjParRel Task tcR tcL)
    cR cL (Hc : CjParRel Job cR cL) (job_task : Job -> Task) aR aL (Ha : CjArrRel Job aR aL) :
  PropSPropRel (Job.cost_of_jobs_from_arrival_sequence_le_task_cost tcR cR job_task aR)
    (I.Prosa_Classic_Model_Arrival_Basic_Job_Job_cost_of_jobs_from_arrival_sequence_le_task_cost Task dT tcL Job dJ cL job_task aL).
Proof.
  apply: ct_forall_identity => j.
  apply: ct_imp.
  - apply: ct_exists_nat => tR tL Ht. exact (cj_mem Job j _ _ (Ha tR tL Ht)).
  - exact (ct_bool_truth _ _ (Job_job_cost_le_task_cost_correspondence tcR tcL Htc cR cL Hc job_task j)).
Qed.
End Defs.
