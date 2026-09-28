Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.AbstractSeqRtaSemanticSource.
Import AbstractSeqRtaSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Require Import prosa.analysis.abstract.search_space prosa.analysis.abstract.definitions.
(* display-only: the official elaborated-type evidence was printed with other [is_in_search_space] and [work_conserving] in scope, so the abstract ones are displayed qualified *)
Module AbstractSeqRtaProbeDisplay. Definition is_in_search_space := tt. Definition work_conserving := tt. End AbstractSeqRtaProbeDisplay.
Import AbstractSeqRtaProbeDisplay.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.abstract_seq_rta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis". Abort.
Print statement_max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis.
Goal True. idtac "END|prosa.analysis.abstract.ideal.abstract_seq_rta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis". Abort.
Goal True. idtac "BEGIN|prosa.analysis.abstract.ideal.abstract_seq_rta.uniprocessor_response_time_bound_seq". Abort.
Print statement_uniprocessor_response_time_bound_seq.
Goal True. idtac "END|prosa.analysis.abstract.ideal.abstract_seq_rta.uniprocessor_response_time_bound_seq". Abort.
