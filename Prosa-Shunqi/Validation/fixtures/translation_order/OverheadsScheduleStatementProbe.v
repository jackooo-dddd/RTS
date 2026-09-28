Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.OverheadsScheduleSemanticSource.
Import OverheadsScheduleSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_is_a_uniprocessor_model". Abort.
Print statement_overheads_proc_model_is_a_uniprocessor_model.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_is_a_uniprocessor_model". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_provides_unit_supply". Abort.
Print statement_overheads_proc_model_provides_unit_supply.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_provides_unit_supply". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_fully_consuming". Abort.
Print statement_overheads_proc_model_fully_consuming.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.overheads_proc_model_fully_consuming". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.scheduled_job_dec". Abort.
Print statement_scheduled_job_dec.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.scheduled_job_dec". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.scheduled_at_iff_scheduled_job". Abort.
Print statement_scheduled_at_iff_scheduled_job.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.scheduled_at_iff_scheduled_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.model.overheads.schedule.job_scheduled_in_busy_interval_prefix". Abort.
Print statement_job_scheduled_in_busy_interval_prefix.
Goal True. idtac "END|prosa.analysis.facts.model.overheads.schedule.job_scheduled_in_busy_interval_prefix". Abort.
