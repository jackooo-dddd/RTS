From LeanImport Require Import Lean.
From prosa Require Import classic.model.time.
From FoundationImported Require Import ImportedClassicTime.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.

Module I := ImportedClassicTime.

(** Certificates for [classic/model/time.v] (ProsaBuddy f692cb7, classic family).

    The three declarations are type definitions: [Time.time := nat] and its aliases
    [Time.duration := time] and [Time.instant := time].  Each is related to its Lean
    counterpart ([abbrev ... := Nat]) through the accepted Nat carrier conversion of
    [SubadditivityNatCorrespondence] ([sub_nat_to_imported] / [sub_nat_to_rocq]), with
    roundtrips in both directions, as for the v0.6 type definitions (e.g. [offset] in
    model/priority/gel.v).  The source side of each lemma is typed at the classic source
    constant, the target side at the imported Lean constant. *)

Lemma Time_time_rocq_roundtrip_certificate (n : prosa.classic.model.time.Time.time) :
  Logic.eq (sub_nat_to_rocq (sub_nat_to_imported n)) n.
Proof. exact (sub_nat_rocq_roundtrip n). Qed.

Lemma Time_time_imported_roundtrip_certificate (n : I.Prosa_Classic_Model_Time_Time_time) :
  Lean.eq (sub_nat_to_imported (sub_nat_to_rocq n)) n.
Proof. exact (sub_nat_imported_roundtrip n). Qed.

Lemma Time_duration_rocq_roundtrip_certificate (n : prosa.classic.model.time.Time.duration) :
  Logic.eq (sub_nat_to_rocq (sub_nat_to_imported n)) n.
Proof. exact (sub_nat_rocq_roundtrip n). Qed.

Lemma Time_duration_imported_roundtrip_certificate (n : I.Prosa_Classic_Model_Time_Time_duration) :
  Lean.eq (sub_nat_to_imported (sub_nat_to_rocq n)) n.
Proof. exact (sub_nat_imported_roundtrip n). Qed.

Lemma Time_instant_rocq_roundtrip_certificate (n : prosa.classic.model.time.Time.instant) :
  Logic.eq (sub_nat_to_rocq (sub_nat_to_imported n)) n.
Proof. exact (sub_nat_rocq_roundtrip n). Qed.

Lemma Time_instant_imported_roundtrip_certificate (n : I.Prosa_Classic_Model_Time_Time_instant) :
  Lean.eq (sub_nat_to_imported (sub_nat_to_rocq n)) n.
Proof. exact (sub_nat_imported_roundtrip n). Qed.
