# implementation/facts/maximal_arrival_sequence.v — canonical translation report

First experiment timestamp: **2026-09-27 05:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/facts/maximal_arrival_sequence.v`; layer 14; rank 109.
- Public declarations: **14** (13 lemmas and the theorem `concrete_is_arrival_curve`).
- Dependencies `analysis/facts/model/task_arrivals.v` and `implementation/definitions/maximal_arrival_sequence.v`: accepted.

## Translation

`Prosa/Implementation/Facts/MaximalArrivalSequence.lean`. Representations:
- `uniq` is `Nodup`, `x \in s` is `decide (x ∈ s) = true`, and `size` is `length`.
- `nth 0 s i` is `s.getD i 0`, and `iter t f [::]` is `Nat.repeat f t []`, as in the accepted definitions.
- `\sum_(a <= i < b) F` is `sumSeq (List.range' a (b - a)) F`.
- `t <= h1 <= h2` is the Boolean conjunction of decides.
- `t.-1` is `t - 1`, and `Δ.+1` is `Δ + 1`.

Binder orders follow the elaborated types. For example, `uniq ts` precedes the `MaxArrivals` binder, and `arr_seq_is_a_set` has no job/task classes.

Proofs:
- Membership in the concrete sequence goes through `List.mem_flatMap`.
- The filtered `bigCatSeqAll` uses the accepted `bigcat_filter_eq_filter_bigcat` and `bigcat_seq_uniqK`.
- The interval size uses the accepted `size_of_task_arrivals_between`.
- Prefix growth uses `Nat.repeat` / `List.getD_append`.
- `n_arrivals_at_leq` uses the accepted `supremum_spec` with `≤`, and relates `suffix_sum` to `max_arrivals_at` by prefix inclusion.
- The main theorem inducts on the window length and uses curve monotonicity.

Lean axioms: standard.

## Source binding

The source is bound by extraction. All 14 statements equal their elaborated types. The proof-heavy `facts/model/task_arrivals` import is dropped, and `model/task/arrivals` is imported instead. `implementation/definitions/maximal_arrival_sequence.v` is compiled from the pinned file, and its rebuilt `.olean` matches the manifest.

## Validation

Spec `implementation_facts_maximal_arrival_sequence.json`; export 31,626 lines.

Certificate chain:
- The accepted ArrivalsSeq*/Arrivals/Curves certificates and the JitterSvc*/MaximalArrivalSequence definition certificates, all re-bound to `ImportedFactsMaximalArrivalSequence`.
- The new `FactsMaximalArrivalSequenceCorrespondence.v`:
  - A proved bridge identifies the two structurally identical list encodings of the replayed adapters.
  - The task set, the `MaxArrivals` class (accepted `CvMaxArrivalsRel` totals) and the job generator (accepted `MsGeneratorRel` totals) are covered in both directions, as are Nats.
  - The job/task classes are related pointwise.
  - It contains the 14 statement certificates.

Audit: every certificate is `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, and `semantic_premises=[]`. The observed alias names `MaximalArrivalSequenceCorrespondence.I.{True,HEq_inst1}` were added.

## Formal acceptance

Coverage **108 / 357 files**, **835 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
