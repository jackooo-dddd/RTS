Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPriorityInversionSemanticSource.
Import FactsPriorityInversionSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.platform_properties prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.sched_itself_implies_no_priority_inversion". Abort.
Print statement_sched_itself_implies_no_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.sched_itself_implies_no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.priority_inversion_scheduled_at". Abort.
Print statement_priority_inversion_scheduled_at.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.priority_inversion_scheduled_at". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.no_priority_inversion_when_idle". Abort.
Print statement_no_priority_inversion_when_idle.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.no_priority_inversion_when_idle". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.priority_inversion_hep_job". Abort.
Print statement_priority_inversion_hep_job.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.priority_inversion_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.no_priority_inversion_when_hep_job_scheduled". Abort.
Print statement_no_priority_inversion_when_hep_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.no_priority_inversion_when_hep_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.uni_priority_inversion_P". Abort.
Print statement_uni_priority_inversion_P.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.uni_priority_inversion_P". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.inversion.cumulative_priority_inversion_cat". Abort.
Print statement_cumulative_priority_inversion_cat.
Goal True. idtac "END|prosa.analysis.facts.priority.inversion.cumulative_priority_inversion_cat". Abort.
