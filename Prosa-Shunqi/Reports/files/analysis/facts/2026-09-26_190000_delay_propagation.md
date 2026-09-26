# analysis/facts/delay_propagation.v — canonical translation report

First experiment timestamp: **2026-09-26 19:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/delay_propagation.v`; layer 14; rank 103.
- Public declarations: **12** (validity of the propagated arrival sequence,
  membership in both directions, validity/correctness of the propagated
  arrival curve, and the stepping-stone lemmas on trigger jobs).
- Dependencies `analysis/definitions/delay_propagation.v`,
  `analysis/facts/behavior/arrivals.v`: accepted.

## Translation

`Prosa/Analysis/Facts/DelayPropagation.lean`, all 12 with Lean proofs.
Binder orders follow the elaborated source types (each lemma only has the
section variables it uses, e.g. `trigger_job_arrival_bounded` has no
`valid_delay_propagation_mapping` hypothesis). Two source-local
(`#[local]`) instances that the statements mention are named Lean helpers
(not inventory declarations): `propagated_arrival_curve` of
`analysis/definitions/delay_propagation.v` (the accepted Rank 89 file did not
need it; it is defined here rather than modifying that accepted file) and
`max_arrivals2` of this file. Representations: `{subset xs <= ys}` and
`{in xs &, injective f}` as their unfolded Boolean-membership forms, `uniq`
as `Nodup`, `[seq f x | x <- s]` as `s.map f`. Lean axioms: `propext`,
`Classical.choice`, `Quot.sound`.

## Source binding

Extraction (proofs need the proof-heavy facts/behavior/arrivals module):
statements from the authoritative elaborated types; the `#[local] Instance
max_arrivals2` is kept as a byte-identical helper block (new pipeline
`helper_blocks`); the MathComp notation modules and `model/task/arrivals` are
added imports. The elaborated type of `propagated_arrival_curve_respected`
hides an implicit `MaxArrivals Task2` instance (the local `max_arrivals2`, out
of scope after its section); one recorded printer repair makes it explicit
(`@taskset_respects_max_arrivals … (@max_arrivals2 …) ts2`), and the statement
prints back exactly the evidence text. All 12 statements equal the
elaborated types.

## Validation

Spec `analysis_facts_delay_propagation.json`. Export 31,767 lines. Chain: the
accepted ArrivalsSeq*/Arrivals, delay-propagation (definition sections only;
the release-jitter section is not replayed because its two remarks are not
exported here) and curves certificates re-bound to
`ImportedFactsDelayPropagation`; new `FactsDelayPropagationCorrespondence.v`
(12 statement certificates, list `map` relation, arrival-curve family
coverage, and the propagated-curve relation `fdp_max_arrivals2_related`,
proved by cases on the window length). Inputs: job-task maps (`Lean.eq`),
job arrivals, the mapping functions (identity carriers), `job2_of`
(pointwise `ArListRel`), delays (pointwise Nat), task sets; type-one arrival
sequences and arrival curves after a hypothesis are covered both ways.
Audit: all certificates `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`,
`semantic_premises=[]`; alias-qualified names added exactly as observed
(`DelayPropagationCorrespondence.I.{True,HEq_inst1}`,
`CurvesCorrespondence.I.{True,HEq_inst1}`).

## Formal acceptance

Coverage **102 / 357 files**, **781 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
