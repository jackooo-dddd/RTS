From mathcomp Require Import ssreflect ssrbool eqtype seq.
From FoundationImported Require Import ImportedSeqset.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SeqsetCorrespondence.
From prosa Require Import util.seqset.

Lemma seqset_set_correspondence_certificate :
  forall (T : eqType) (s : @prosa.util.seqset.set T),
    RocqSeqSetRel T s (source_to_imported_seqset T s).
Proof. exact seqset_relation_source_total. Qed.

(** [set_of] only discharges the source phantom and target instance
    parameters.  Its observable carrier relation is exactly the record
    relation above. *)
Lemma seqset_set_of_correspondence_certificate :
  forall (T : eqType) (s : @prosa.util.seqset.set_of T (Phant T)),
    RocqSeqSetRel T s (source_to_imported_seqset T s).
Proof. exact seqset_relation_source_total. Qed.

Definition rocq_set_uniq_type_guard (T : eqType)
    (s : @prosa.util.seqset.set T) : uniq s :=
  @prosa.util.seqset.set_uniq T s.

Definition imported_set_uniq_type_guard (T : eqType)
    (s : Prosa_Util_Seqset_set T (seqset_decidable_eq T)) :
    ImportedSeqset.List_Nodup T
      (Prosa_Util_Seqset_set_val T (seqset_decidable_eq T) s) :=
  Prosa_Util_Seqset_set_uniq T (seqset_decidable_eq T) s.

Lemma seqset_set_uniq_statement_correspondence_certificate :
  forall (T : eqType) (sR : @prosa.util.seqset.set T)
    (sL : Prosa_Util_Seqset_set T (seqset_decidable_eq T)),
    RocqSeqSetRel T sR sL ->
    PropSPropRel (uniq sR)
      (ImportedSeqset.List_Nodup T
        (Prosa_Util_Seqset_set_val T (seqset_decidable_eq T) sL)).
Proof.
  intros T sR sL Hrel. apply prop_sprop_rel_intro.
  - intro Huniq.
    destruct Hrel.
    exact (source_uniq_to_imported_nodup
      (@prosa.util.seqset._set_seq T sR) Huniq).
  - intro Hnodup. destruct Hrel.
    exact (seqset_strict_uniq_transport _ _
      (seqset_seq_roundtrip (@prosa.util.seqset._set_seq T sR))
      (imported_nodup_to_strict_source_uniq _ Hnodup)).
Qed.

Print Assumptions seqset_set_correspondence_certificate.
Print Assumptions seqset_set_of_correspondence_certificate.
Print Assumptions seqset_set_uniq_statement_correspondence_certificate.
