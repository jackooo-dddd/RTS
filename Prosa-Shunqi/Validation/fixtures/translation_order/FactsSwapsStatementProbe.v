Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.FactsSwapsSemanticSource.
Import FactsSwapsSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import prosa.behavior.all prosa.model.processor.platform_properties.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.trivial_swap". Abort.
Print statement_trivial_swap.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.trivial_swap". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.trivial_swap_service_invariant". Abort.
Print statement_trivial_swap_service_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.trivial_swap_service_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_other_times_invariant". Abort.
Print statement_swap_other_times_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_other_times_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_t1". Abort.
Print statement_swap_job_scheduled_t1.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_t1". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_t2". Abort.
Print statement_swap_job_scheduled_t2.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_t2". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_other_times". Abort.
Print statement_swap_job_scheduled_other_times.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_other_times". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_cases". Abort.
Print statement_swap_job_scheduled_cases.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled". Abort.
Print statement_swap_job_scheduled.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_original_cases". Abort.
Print statement_swap_job_scheduled_original_cases.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_original_cases". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_job_scheduled_original". Abort.
Print statement_swap_job_scheduled_original.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_job_scheduled_original". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_before_invariant". Abort.
Print statement_swap_before_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_before_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swap_after_invariant". Abort.
Print statement_swap_after_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swap_after_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.service_before_swap_invariant". Abort.
Print statement_service_before_swap_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.service_before_swap_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.service_after_swap_invariant". Abort.
Print statement_service_after_swap_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.service_after_swap_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.service_of_others_invariant". Abort.
Print statement_service_of_others_invariant.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.service_of_others_invariant". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swapped_service_bound". Abort.
Print statement_swapped_service_bound.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swapped_service_bound". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swapped_completed_jobs_dont_execute". Abort.
Print statement_swapped_completed_jobs_dont_execute.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swapped_completed_jobs_dont_execute". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.swapped_jobs_come_from_arrival_sequence". Abort.
Print statement_swapped_jobs_come_from_arrival_sequence.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.swapped_jobs_come_from_arrival_sequence". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.uninvolved_implies_deadline_met". Abort.
Print statement_uninvolved_implies_deadline_met.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.uninvolved_implies_deadline_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.moved_earlier_implies_deadline_met". Abort.
Print statement_moved_earlier_implies_deadline_met.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.moved_earlier_implies_deadline_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.moved_later_implies_deadline_met". Abort.
Print statement_moved_later_implies_deadline_met.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.moved_later_implies_deadline_met". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.transform.swaps.edf_swap_no_deadline_misses_introduced". Abort.
Print statement_edf_swap_no_deadline_misses_introduced.
Goal True. idtac "END|prosa.analysis.facts.transform.swaps.edf_swap_no_deadline_misses_introduced". Abort.
