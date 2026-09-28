Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsPriorityFifoSemanticSource.
Import FactsPriorityFifoSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.schedule.scheduled.
(* display-only: the imports of the source *)
Require Import prosa.model.priority.fifo prosa.model.readiness.basic prosa.model.task.sequentiality prosa.model.schedule.work_conserving prosa.model.processor.platform_properties.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.hep_job_arrival_FIFO". Abort.
Print statement_hep_job_arrival_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.hep_job_arrival_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.not_hep_job_arrival_FIFO". Abort.
Print statement_not_hep_job_arrival_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.not_hep_job_arrival_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.not_hep_job_FIFO". Abort.
Print statement_not_hep_job_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.not_hep_job_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.not_hep_job_always_higher_priority_FIFO". Abort.
Print statement_not_hep_job_always_higher_priority_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.not_hep_job_always_higher_priority_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.FIFO_implies_no_priority_inversion". Abort.
Print statement_FIFO_implies_no_priority_inversion.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.FIFO_implies_no_priority_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.scheduled_implies_higher_priority_completed". Abort.
Print statement_scheduled_implies_higher_priority_completed.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.scheduled_implies_higher_priority_completed". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.FIFO_implies_no_pi". Abort.
Print statement_FIFO_implies_no_pi.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.FIFO_implies_no_pi". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.FIFO_implies_no_service_inversion". Abort.
Print statement_FIFO_implies_no_service_inversion.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.FIFO_implies_no_service_inversion". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.tasks_execute_sequentially". Abort.
Print statement_tasks_execute_sequentially.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.tasks_execute_sequentially". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.fifo_respects_sequential_tasks". Abort.
Print statement_fifo_respects_sequential_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.fifo_respects_sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.no_preemptions_under_FIFO". Abort.
Print statement_no_preemptions_under_FIFO.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.no_preemptions_under_FIFO". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.fifo.FIFO_is_nonpreemptive". Abort.
Print statement_FIFO_is_nonpreemptive.
Goal True. idtac "END|prosa.analysis.facts.priority.fifo.FIFO_is_nonpreemptive". Abort.
