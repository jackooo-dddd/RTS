(* Parse evidence for results/transfer_schedulability/criterion.v.
   Compiled against the installed official rocq-prosa 0.6 package of the
   authoritative toolchain (opam switch prosa-0.6: Rocq 9.0.1, MathComp 2.4.0):
     opam exec --switch=prosa-0.6 -- rocq c CriterionOfficialParse.v
   The output (CriterionOfficialParse.log) shows how the official toolchain
   parses the definition bodies; the validation toolchain (Rocq 9.3+rc1,
   MathComp 2.6.0) parses [(t1 < t2) && \sum_(..) F == t2 - t1] as
   [((t1 < t2) && \sum_(..) F) == t2 - t1] instead, so the extracted body of
   [slackless_interval] carries the parentheses of the official parse. *)
From prosa.results.transfer_schedulability Require Import criterion.
Set Printing Parentheses.
Print schedulability_transferred.
Print remaining_cost_bound.
Print critical_jobs.
Print slackless_interval.
Print contiguously_slackless_interval.
Print transfer_schedulability_criterion.
Print nonpositive_slack.
Print contiguously_nps.
