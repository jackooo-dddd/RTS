Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.ProgressSemanticSource.
Import ProgressSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import prosa.behavior.service.
Goal True. idtac "BEGIN|prosa.analysis.definitions.progress.job_has_progressed". Abort.
Check @job_has_progressed.
Goal True. idtac "END|prosa.analysis.definitions.progress.job_has_progressed". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.progress.no_progress". Abort.
Check @no_progress.
Goal True. idtac "END|prosa.analysis.definitions.progress.no_progress". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.progress.no_progress_equiv". Abort.
Print statement_no_progress_equiv.
Goal True. idtac "END|prosa.analysis.definitions.progress.no_progress_equiv". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.progress.no_progress_for". Abort.
Check @no_progress_for.
Goal True. idtac "END|prosa.analysis.definitions.progress.no_progress_for". Abort.
