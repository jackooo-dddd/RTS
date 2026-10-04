# Reference solutions for the lean-prosa-v06 case-study benchmark

Complete Lean proofs of all 22 benchmark tasks of `lean-prosa-v06` (see its `benchmark/README.md`).
**Keep this folder away from any model under evaluation.**

- `Solutions/<G>/<F>.lean`: one proof per task. Each file restates the case study's theorem with its binders
  in the namespace of the statement module, proves it, and ends with
  `theorem Solutions.<G>.<F>.solution : <statement> := @<theorem>`.
- `Solutions/Support/*.lean`: lemmas shared by several proofs, proved from the library:
  - `Common`: sums, FP carry-in scheduling, per-job interference/completion facts, interference counting.
  - `CommonFp`: the classic Bertogna–Cirinei FP core without the response-time recurrence.
  - `BusyWindow`: the busy-window inequality of Guan et al. (RTSS 2009).
  - `WorkloadArith`, `WorkloadJobs`: sporadic workload bounds (`W_NC`, carry-in bounds) at job level.

To verify, from inside `lean-prosa-v06/`:

```sh
cp -R ../lean-prosa-v06-reference-solutions/Solutions .
python3 benchmark/check.py          # 22/22 passed
```

Several case studies take earlier lemmas of their paper as hypotheses (for example `H_Lemma2_1` or
`Lemma1_09`), sometimes in a stronger form than the paper proves. The reference proofs use these hypotheses as
given. They did not check that each hypothesis set can be satisfied by a real schedule.
