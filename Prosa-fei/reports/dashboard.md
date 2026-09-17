# rt-proofs → Lean 4 Translation Dashboard

> Generated: 2026-04-17T14:19:29.613Z

## Pipeline Overview

```
════════════════════════════════════════════════════════════
  rt-proofs → Lean 4 Translation Pipeline
════════════════════════════════════════════════════════════
  Total files: 317    Processed: 317    Pending: 0
  ▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓▓  100.0%

  Phase 2 — Statement (files):  317✓  0◐  0✗  (317 files)
  Phase 3 — Proof    (files):  219✓  22◐  0✗  (241 files)
  Coq proofs (Qed/Defined): 1804    Truly proven: 1502    Polluted: 0    Sorry: 302    Rate: 83.3%
════════════════════════════════════════════════════════════
```

## By Module

| Module | Layer | Files | Statements | Proofs | Status |
|--------|-------|-------|------------|--------|--------|
| behavior/ | 1 | 3/3 | 3✓ 0✗ | 0✓ 0◐ 0✗ | ✅ Complete |
| classic/ | 1 | 22/22 | 22✓ 0✗ | 15✓ 0◐ 0✗ | ✅ Complete |
| util/ | 1 | 18/18 | 18✓ 0✗ | 14✓ 0◐ 0✗ | ✅ Complete |
| behavior/ | 2 | 3/3 | 3✓ 0✗ | 0✓ 0◐ 0✗ | ✅ Complete |
| classic/ | 2 | 21/21 | 21✓ 0✗ | 20✓ 0◐ 0✗ | ✅ Complete |
| util/ | 2 | 1/1 | 1✓ 0✗ | 0✓ 0◐ 0✗ | ✅ Complete |
| analysis/ | 3 | 3/3 | 3✓ 0✗ | 1✓ 0◐ 0✗ | ✅ Complete |
| behavior/ | 3 | 1/1 | 1✓ 0✗ | 0✓ 0◐ 0✗ | ✅ Complete |
| classic/ | 3 | 59/59 | 59✓ 0✗ | 52✓ 0◐ 0✗ | ✅ Complete |
| model/ | 3 | 12/12 | 12✓ 0✗ | 6✓ 0◐ 0✗ | ✅ Complete |
| analysis/ | 4 | 12/12 | 12✓ 0✗ | 10✓ 0◐ 0✗ | ✅ Complete |
| classic/ | 4 | 72/72 | 72✓ 0✗ | 44✓ 13◐ 0✗ | 🟢 Stmts done |
| model/ | 4 | 26/26 | 26✓ 0✗ | 7✓ 0◐ 0✗ | ✅ Complete |
| analysis/ | 5 | 34/34 | 34✓ 0✗ | 30✓ 0◐ 0✗ | ✅ Complete |
| classic/ | 5 | 15/15 | 15✓ 0✗ | 6✓ 9◐ 0✗ | 🟢 Stmts done |
| model/ | 5 | 2/2 | 2✓ 0✗ | 1✓ 0◐ 0✗ | ✅ Complete |
| results/ | 5 | 13/13 | 13✓ 0✗ | 13✓ 0◐ 0✗ | ✅ Complete |

## Statement Verification (4-Level)

| Verification | Result | Details |
|-------------|--------|---------|
| A: Declaration Inventory | 2933 Coq → 3027 Lean | completeness check |
| B: Structural Signature | ✓2788  ?24  ✗0 | ∀/→ count comparison |
| C: #check Type Print | 317 pass  0 fail | Lean type-checker output |
| D: Semantic Self-Review | 317 consistent  0 flagged | side-by-side meaning check |

## Per-File Details

| # | File | Layer | Stmt | Decls (ok/total) | Proof | Proofs (ok/total) | Sorry | Polluted | A | B | C | D | Duration | Notes |
|---|------|-------|------|------------------|-------|-------------------|-------|----------|---|---|---|---|----------|-------|
| 1 | behavior/time.v | 1 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 1s | definitions only |
| 2 | classic/model/time.v | 1 | ✅ | 3/3 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 1s | definitions only |
| 3 | classic/util/pick.v | 1 | ✅ | 17/17 (100.0%) | ✅ | 9/9 (100.0%) | 0 | — | ✅ | ⚠ | ✅ | ✅ | 4m0s | fully proven |
| 4 | util/counting.v | 1 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2m6s | fully proven |
| 5 | util/epsilon.v | 1 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 6 | util/notation.v | 1 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 1m28s | definitions only |
| 7 | util/rel.v | 1 | ✅ | 3/3 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 5m21s | definitions only |
| 8 | util/rewrite_facilities.v | 1 | ✅ | 11/11 (100.0%) | ✅ | 12/12 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 7m19s | fully proven |
| 9 | util/seqset.v | 1 | ✅ | 6/7 (85.7%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16511m49s | fully proven |
| 10 | util/ssromega.v | 1 | ✅ | 1/3 (33.3%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 1m36s | definitions only |
| 11 | util/supremum.v | 1 | ✅ | 7/7 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 22317m47s | fully proven |
| 12 | util/tactics.v | 1 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2m5s | fully proven |
| 13 | behavior/job.v | 1 | ✅ | 5/5 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 13s | definitions only |
| 14 | classic/model/arrival/basic/job.v | 1 | ✅ | 10/8 (125.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 13s | definitions only |
| 15 | classic/model/arrival/basic/task.v | 1 | ✅ | 11/11 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 39s | definitions only |
| 16 | classic/util/notation.v | 1 | ✅ | 13/6 (216.7%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 13s | definitions only |
| 17 | classic/util/seqset.v | 1 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2m47s | fully proven |
| 18 | classic/util/tactics.v | 1 | ✅ | 14/14 (100.0%) | ✅ | 13/13 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3m5s | fully proven |
| 19 | util/bigcat.v | 1 | ✅ | 4/3 (133.3%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4m45s | fully proven |
| 20 | util/list.v | 1 | ✅ | 36/35 (102.9%) | ✅ | 32/32 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4546m5s | fully proven |
| 21 | util/minmax.v | 1 | ✅ | 7/7 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 20m51s | fully proven |
| 22 | util/nat.v | 1 | ✅ | 9/9 (100.0%) | ✅ | 9/9 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 8m18s | fully proven |
| 23 | util/search_arg.v | 1 | ✅ | 8/8 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 19371m57s | fully proven |
| 24 | util/step_function.v | 1 | ✅ | 3/3 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16340m49s | fully proven |
| 25 | behavior/arrival_sequence.v | 1 | ✅ | 13/13 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 12s | definitions only |
| 26 | classic/implementation/task.v | 1 | ✅ | 4/6 (66.7%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ⚠ | ✅ | ✅ | 4m56s | fully proven |
| 27 | classic/model/arrival/jitter/job.v | 1 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 38s | definitions only |
| 28 | classic/model/schedule/global/jitter/job.v | 1 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 43s | definitions only |
| 29 | classic/util/bigcat.v | 1 | ✅ | 6/6 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 7m50s | fully proven |
| 30 | classic/util/bigord.v | 1 | ✅ | 4/4 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9m22s | fully proven |
| 31 | classic/util/counting.v | 1 | ✅ | 5/5 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 11m39s | fully proven |
| 32 | classic/util/fixedpoint.v | 1 | ✅ | 10/10 (100.0%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13m39s | fully proven |
| 33 | classic/util/induction.v | 1 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2m41s | fully proven |
| 34 | classic/util/list.v | 1 | ✅ | 45/45 (100.0%) | ✅ | 35/35 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16252m49s | fully proven |
| 35 | classic/util/minmax.v | 1 | ✅ | 44/44 (100.0%) | ✅ | 32/32 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 27m7s | fully proven |
| 36 | classic/util/nat.v | 1 | ✅ | 6/6 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 20514m58s | fully proven |
| 37 | classic/util/ord_quantifier.v | 1 | ✅ | 4/4 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4m40s | fully proven |
| 38 | classic/util/powerset.v | 1 | ✅ | 2/2 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 57s | fully proven |
| 39 | classic/util/sorting.v | 1 | ✅ | 6/6 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m6s | fully proven |
| 40 | classic/util/step_function.v | 1 | ✅ | — | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 24s | definitions only |
| 41 | util/div_mod.v | 1 | ✅ | 3/3 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3m52s | fully proven |
| 42 | util/nondecreasing.v | 1 | ✅ | 33/33 (100.0%) | ✅ | 30/30 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 18414m48s | fully proven |
| 43 | util/sum.v | 1 | ✅ | 14/14 (100.0%) | ✅ | 14/14 (100.0%) | 0 | — | ✅ | ⚠ | ✅ | ✅ | 16m15s | fully proven |
| 44 | behavior/schedule.v | 2 | ✅ | 3/2 (150.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 45 | classic/implementation/job.v | 2 | ✅ | 3/3 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 7m28s | fully proven |
| 46 | classic/util/div_mod.v | 2 | ✅ | 15/17 (88.2%) | ✅ | 15/15 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m54s | fully proven |
| 47 | classic/util/sum.v | 2 | ✅ | 7/7 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m45s | fully proven |
| 48 | util/all.v | 2 | ✅ | — | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 49 | behavior/service.v | 2 | ✅ | 11/11 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 50 | classic/util/all.v | 2 | ✅ | — | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 51 | behavior/ready.v | 2 | ✅ | 7/7 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 52 | classic/implementation/global/jitter/task.v | 2 | ✅ | 4/4 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12m7s | fully proven |
| 53 | classic/implementation/uni/jitter/task.v | 2 | ✅ | 4/6 (66.7%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ⚠ | ✅ | ✅ | 15m41s | fully proven |
| 54 | classic/implementation/uni/susp/dynamic/task.v | 2 | ✅ | 4/4 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2m8s | fully proven |
| 55 | classic/model/arrival/basic/arrival_sequence.v | 2 | ✅ | 20/20 (100.0%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ⚠ | ✅ | ✅ | 15m56s | fully proven |
| 56 | classic/model/arrival/jitter/arrival_bounds.v | 2 | ✅ | 10/10 (100.0%) | ✅ | 10/10 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3177m36s | fully proven |
| 57 | classic/model/arrival/jitter/arrival_sequence.v | 2 | ✅ | 15/15 (100.0%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m24s | fully proven |
| 58 | classic/model/policy_tdma.v | 2 | ✅ | 16/16 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4354m21s | fully proven |
| 59 | classic/model/priority.v | 2 | ✅ | 35/35 (100.0%) | ✅ | 9/9 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12m56s | fully proven |
| 60 | classic/model/schedule/global/basic/schedule.v | 2 | ✅ | 39/39 (100.0%) | ✅ | 16/16 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 19m46s | fully proven |
| 61 | classic/model/schedule/global/jitter/constrained_deadlines.v | 2 | ✅ | 10/10 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 18858m7s | fully proven |
| 62 | classic/model/schedule/global/jitter/interference_edf.v | 2 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13m48s | fully proven |
| 63 | classic/model/schedule/global/jitter/platform.v | 2 | ✅ | 6/6 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m7s | fully proven |
| 64 | classic/model/schedule/uni/end_time.v | 2 | ✅ | 15/15 (100.0%) | ✅ | 11/11 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15654m39s | fully proven |
| 65 | classic/model/schedule/uni/schedulability.v | 2 | ✅ | 14/4 (350.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13434m28s | fully proven |
| 66 | classic/model/schedule/uni/schedule.v | 2 | ✅ | 38/38 (100.0%) | ✅ | 21/21 (100.0%) | 0 | — | ✅ | ⚠ | ✅ | ✅ | 12320m40s | fully proven |
| 67 | classic/model/schedule/uni/workload.v | 2 | ✅ | 6/6 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m8s | fully proven |
| 68 | classic/util/find_seq.v | 2 | ✅ | 6/6 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 14m4s | fully proven |
| 69 | behavior/all.v | 3 | ✅ | — | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 70 | classic/analysis/uni/basic/workload_bound_fp.v | 3 | ✅ | 7/6 (116.7%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m19s | fully proven |
| 71 | classic/implementation/arrival_sequence.v | 3 | ✅ | 8/7 (114.3%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m20s | fully proven |
| 72 | classic/implementation/global/jitter/arrival_sequence.v | 3 | ✅ | 10/7 (142.9%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m21s | fully proven |
| 73 | classic/implementation/global/jitter/job.v | 3 | ✅ | 3/5 (60.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12m26s | fully proven |
| 74 | classic/implementation/uni/basic/schedule_tdma.v | 3 | ✅ | 16/11 (145.5%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12309m18s | fully proven |
| 75 | classic/implementation/uni/basic/tdma_rta_example.v | 3 | ✅ | 27/27 (100.0%) | ✅ | 11/11 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 61m7s | fully proven |
| 76 | classic/implementation/uni/jitter/arrival_sequence.v | 3 | ✅ | 8/8 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m7s | fully proven |
| 77 | classic/implementation/uni/jitter/job.v | 3 | ✅ | 3/5 (60.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 7m11s | fully proven |
| 78 | classic/implementation/uni/susp/dynamic/arrival_sequence.v | 3 | ✅ | 10/7 (142.9%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m55s | fully proven |
| 79 | classic/implementation/uni/susp/dynamic/job.v | 3 | ✅ | 3/3 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2m23s | fully proven |
| 80 | classic/model/arrival/basic/arrival_bounds.v | 3 | ✅ | 10/10 (100.0%) | ✅ | 10/10 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m55s | fully proven |
| 81 | classic/model/arrival/basic/task_arrival.v | 3 | ✅ | 11/11 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m56s | fully proven |
| 82 | classic/model/arrival/curves/bounds.v | 3 | ✅ | 7/7 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 83 | classic/model/schedule/apa/affinity.v | 3 | ✅ | 7/7 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12986m56s | fully proven |
| 84 | classic/model/schedule/global/basic/constrained_deadlines.v | 3 | ✅ | 7/7 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4188m7s | fully proven |
| 85 | classic/model/schedule/global/basic/interference_edf.v | 3 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9m43s | fully proven |
| 86 | classic/model/schedule/global/basic/platform.v | 3 | ✅ | 6/6 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 14m20s | fully proven |
| 87 | classic/model/schedule/global/jitter/schedule.v | 3 | ✅ | 15/15 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12m43s | fully proven |
| 88 | classic/model/schedule/global/response_time.v | 3 | ✅ | 5/5 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4m27s | fully proven |
| 89 | classic/model/schedule/global/schedulability.v | 3 | ✅ | 7/7 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16106m4s | fully proven |
| 90 | classic/model/schedule/global/transformation/construction.v | 3 | ✅ | 6/6 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m57s | fully proven |
| 91 | classic/model/schedule/uni/basic/platform.v | 3 | ✅ | 5/5 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m3s | fully proven |
| 92 | classic/model/schedule/uni/basic/platform_tdma.v | 3 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 93 | classic/model/schedule/uni/jitter/schedule.v | 3 | ✅ | 9/9 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 18m55s | fully proven |
| 94 | classic/model/schedule/uni/limited/abstract_RTA/definitions.v | 3 | ✅ | 9/9 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4m22s | fully proven |
| 95 | classic/model/schedule/uni/limited/abstract_RTA/reduction_of_search_space.v | 3 | ✅ | 5/5 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 10m11s | fully proven |
| 96 | classic/model/schedule/uni/nonpreemptive/schedule.v | 3 | ✅ | 12/10 (120.0%) | ✅ | 9/9 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 19m51s | fully proven |
| 97 | classic/model/schedule/uni/response_time.v | 3 | ✅ | 6/6 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13m37s | fully proven |
| 98 | classic/model/schedule/uni/schedule_of_task.v | 3 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 99 | classic/model/schedule/uni/service.v | 3 | ✅ | 18/18 (100.0%) | ✅ | 13/13 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 14857m58s | fully proven |
| 100 | classic/model/schedule/uni/susp/last_execution.v | 3 | ✅ | 11/9 (122.2%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m6s | fully proven |
| 101 | classic/model/schedule/uni/sustainability.v | 3 | ✅ | 26/26 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m44s | fully proven |
| 102 | classic/model/schedule/uni/transformation/construction.v | 3 | ✅ | 7/7 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13m39s | fully proven |
| 103 | classic/model/suspension.v | 3 | ✅ | 3/3 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 104 | analysis/definitions/job_properties.v | 3 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 105 | analysis/facts/behavior/arrivals.v | 3 | ✅ | 12/12 (100.0%) | ✅ | 12/12 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 17794m39s | fully proven |
| 106 | analysis/transform/swap.v | 3 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 107 | classic/analysis/apa/workload_bound.v | 3 | ✅ | 21/21 (100.0%) | ✅ | 19/19 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 1045m13s | fully proven |
| 108 | classic/analysis/global/parallel/workload_bound.v | 3 | ✅ | 18/18 (100.0%) | ✅ | 16/16 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 110618m36s | fully proven |
| 109 | classic/analysis/uni/arrival_curves/workload_bound.v | 3 | ✅ | 8/8 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m7s | fully proven |
| 110 | classic/analysis/uni/basic/fp_rta_comp.v | 3 | ✅ | 16/16 (100.0%) | ✅ | 9/9 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13744m42s | fully proven |
| 111 | classic/analysis/uni/basic/tdma_rta_theory.v | 3 | ✅ | 6/6 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 127161m35s | fully proven |
| 112 | classic/analysis/uni/basic/tdma_wcrt_analysis.v | 3 | ✅ | 30/30 (100.0%) | ✅ | 26/26 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 17811m24s | fully proven |
| 113 | classic/analysis/uni/jitter/workload_bound_fp.v | 3 | ✅ | 6/6 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13614m44s | fully proven |
| 114 | classic/analysis/uni/susp/dynamic/jitter/jitter_schedule.v | 3 | ✅ | 6/6 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 115 | classic/implementation/apa/schedule.v | 3 | ✅ | 2/2 (100.0%) | ✅ | 17/17 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 24456m25s | fully proven |
| 116 | classic/implementation/apa/task.v | 3 | ✅ | 4/4 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3m36s | fully proven |
| 117 | classic/implementation/global/basic/schedule.v | 3 | ✅ | 14/14 (100.0%) | ✅ | 10/10 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 18m8s | fully proven |
| 118 | classic/implementation/global/jitter/schedule.v | 3 | ✅ | 14/14 (100.0%) | ✅ | 10/10 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m46s | fully proven |
| 119 | classic/implementation/uni/basic/schedule.v | 3 | ✅ | 10/10 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m49s | fully proven |
| 120 | classic/implementation/uni/jitter/schedule.v | 3 | ✅ | 12/10 (120.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 11m14s | fully proven |
| 121 | classic/model/arrival/jitter/task_arrival.v | 3 | ✅ | 8/8 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 14m33s | fully proven |
| 122 | classic/model/schedule/apa/interference_edf.v | 3 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m52s | fully proven |
| 123 | classic/model/schedule/global/workload.v | 3 | ✅ | 4/4 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 17m13s | fully proven |
| 124 | classic/model/schedule/partitioned/schedule.v | 3 | ✅ | 5/5 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4m36s | fully proven |
| 125 | classic/model/schedule/uni/jitter/busy_interval.v | 3 | ✅ | 15/15 (100.0%) | ✅ | 12/12 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9629m48s | fully proven |
| 126 | classic/model/schedule/uni/jitter/platform.v | 3 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 127 | classic/model/schedule/uni/jitter/valid_schedule.v | 3 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 128 | classic/model/schedule/uni/limited/platform/definitions.v | 3 | ✅ | 14/14 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m27s | fully proven |
| 129 | classic/model/schedule/uni/limited/schedule.v | 3 | ✅ | 9/9 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m33s | fully proven |
| 130 | classic/model/schedule/uni/nonpreemptive/platform.v | 3 | ✅ | 6/6 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m31s | fully proven |
| 131 | classic/model/schedule/uni/susp/suspension_intervals.v | 3 | ✅ | 12/12 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13255m6s | fully proven |
| 132 | model/preemption/parameter.v | 3 | ✅ | 12/12 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m35s | fully proven |
| 133 | model/processor/ideal.v | 3 | ✅ | 5/5 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3m43s | fully proven |
| 134 | model/processor/multiprocessor.v | 3 | ✅ | 5/5 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 7m49s | fully proven |
| 135 | model/processor/platform_properties.v | 3 | ✅ | 3/3 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 136 | model/processor/spin.v | 3 | ✅ | 4/4 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 7m38s | fully proven |
| 137 | model/processor/varspeed.v | 3 | ✅ | 4/4 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12m40s | fully proven |
| 138 | model/readiness/basic.v | 3 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 12m54s | definitions only |
| 139 | model/readiness/jitter.v | 3 | ✅ | 3/3 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12874m3s | fully proven |
| 140 | model/schedule/edf.v | 3 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 141 | model/schedule/nonpreemptive.v | 3 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 142 | model/schedule/work_conserving.v | 3 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 143 | model/task/concept.v | 3 | ✅ | 12/12 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 144 | analysis/abstract/definitions.v | 4 | ✅ | 9/9 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m16s | fully proven |
| 145 | analysis/abstract/search_space.v | 4 | ✅ | 5/5 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m11s | fully proven |
| 146 | analysis/definitions/task_schedule.v | 4 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 147 | analysis/facts/behavior/service.v | 4 | ✅ | 34/34 (100.0%) | ✅ | 34/34 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 27m11s | fully proven |
| 148 | classic/analysis/apa/interference_bound.v | 4 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 149 | classic/analysis/global/basic/workload_bound.v | 4 | ✅ | 21/21 (100.0%) | ✅ | 19/19 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 7460m14s | fully proven |
| 150 | classic/analysis/global/jitter/workload_bound.v | 4 | ✅ | 21/21 (100.0%) | ✅ | 19/19 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 7484m54s | fully proven |
| 151 | classic/analysis/global/parallel/bertogna_edf_theory.v | 4 | ✅ | 12/12 (100.0%) | ◐ | 0/9 (0.0%) | 9 | — | ✅ | ✅ | ✅ | ✅ | 145m1s |  |
| 152 | classic/analysis/global/parallel/bertogna_fp_theory.v | 4 | ✅ | 12/12 (100.0%) | ◐ | 4/6 (66.7%) | 2 | — | ✅ | ✅ | ✅ | ✅ | 7366m27s |  |
| 153 | classic/analysis/global/parallel/interference_bound.v | 4 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 154 | classic/analysis/global/parallel/interference_bound_edf.v | 4 | ✅ | 28/28 (100.0%) | ◐ | 3/25 (12.0%) | 22 | — | ✅ | ✅ | ✅ | ✅ |  |  |
| 155 | classic/analysis/global/parallel/interference_bound_fp.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 7313m30s | definitions only |
| 156 | classic/analysis/uni/jitter/fp_rta_comp.v | 4 | ✅ | 14/14 (100.0%) | ✅ | 10/10 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m52s | fully proven |
| 157 | classic/analysis/uni/jitter/fp_rta_theory.v | 4 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9125m23s | fully proven |
| 158 | classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_properties.v | 4 | ✅ | 9/9 (100.0%) | ✅ | 9/9 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9278m3s | fully proven |
| 159 | classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_service.v | 4 | ✅ | 34/34 (100.0%) | ✅ | 23/23 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 17910m27s | fully proven |
| 160 | classic/analysis/uni/susp/dynamic/jitter/jitter_taskset_generation.v | 4 | ✅ | 3/3 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 161 | classic/analysis/uni/susp/dynamic/jitter/rta_by_reduction.v | 4 | ✅ | 2/2 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 8690m28s | fully proven |
| 162 | classic/analysis/uni/susp/dynamic/oblivious/reduction.v | 4 | ✅ | 32/29 (110.3%) | ✅ | 23/23 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 92m21s | fully proven |
| 163 | classic/implementation/apa/arrival_sequence.v | 4 | ✅ | 10/10 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m51s | fully proven |
| 164 | classic/implementation/apa/job.v | 4 | ✅ | 3/3 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m55s | fully proven |
| 165 | classic/implementation/global/parallel/bertogna_edf_example.v | 4 | ✅ | 13/13 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m50s | fully proven |
| 166 | classic/implementation/global/parallel/bertogna_fp_example.v | 4 | ✅ | 22/16 (137.5%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 6577m11s | fully proven |
| 167 | classic/implementation/uni/basic/extraction_tdma.v | 4 | ✅ | 13/13 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13m17s | fully proven |
| 168 | classic/implementation/uni/basic/fp_rta_example.v | 4 | ✅ | 22/15 (146.7%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 24m30s | fully proven |
| 169 | classic/implementation/uni/jitter/fp_rta_example.v | 4 | ✅ | 19/19 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 6836m3s | fully proven |
| 170 | classic/model/schedule/apa/interference.v | 4 | ✅ | 11/11 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 37m35s | fully proven |
| 171 | classic/model/schedule/global/basic/interference.v | 4 | ✅ | 9/9 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 46m9s | fully proven |
| 172 | classic/model/schedule/partitioned/schedulability.v | 4 | ✅ | 5/5 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 5695m54s | fully proven |
| 173 | classic/model/schedule/uni/limited/abstract_RTA/abstract_rta.v | 4 | ✅ | 8/8 (100.0%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 57m9s | fully proven |
| 174 | classic/model/schedule/uni/limited/abstract_RTA/sufficient_condition_for_lock_in_service.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 993m50s | fully proven |
| 175 | classic/model/schedule/uni/limited/busy_interval.v | 4 | ✅ | 33/33 (100.0%) | ✅ | 24/24 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13002m12s | fully proven |
| 176 | classic/model/schedule/uni/limited/edf/nonpr_reg/concrete_models/response_time_bound.v | 4 | ✅ | 5/5 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4301m17s | fully proven |
| 177 | classic/model/schedule/uni/limited/edf/nonpr_reg/response_time_bound.v | 4 | ✅ | 8/8 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 5080m2s | fully proven |
| 178 | classic/model/schedule/uni/limited/edf/response_time_bound.v | 4 | ✅ | 9/9 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ⚠ | ✅ | ✅ | 11733m26s | fully proven |
| 179 | classic/model/schedule/uni/limited/fixed_priority/nonpr_reg/concrete_models/response_time_bound.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4377m8s | fully proven |
| 180 | classic/model/schedule/uni/limited/fixed_priority/nonpr_reg/response_time_bound.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2570m39s | fully proven |
| 181 | classic/model/schedule/uni/limited/platform/limited.v | 4 | ✅ | 29/29 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13028m37s | fully proven |
| 182 | classic/model/schedule/uni/limited/platform/nonpreemptive.v | 4 | ✅ | 3/3 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 966m8s | fully proven |
| 183 | classic/model/schedule/uni/limited/platform/preemptive.v | 4 | ✅ | 3/3 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13m8s | fully proven |
| 184 | classic/model/schedule/uni/limited/platform/priority_inversion_is_bounded.v | 4 | ✅ | 9/9 (100.0%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4150m40s | fully proven |
| 185 | classic/model/schedule/uni/limited/rbf.v | 4 | ✅ | 3/3 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 985m5s | fully proven |
| 186 | classic/model/schedule/uni/susp/schedule.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 187 | model/preemption/fully_nonpreemptive.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 188 | model/preemption/fully_preemptive.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 189 | model/preemption/limited_preemptive.v | 4 | ✅ | 6/6 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 190 | model/priority/classes.v | 4 | ✅ | 11/11 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9m29s | fully proven |
| 191 | model/schedule/limited_preemptive.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 192 | model/schedule/preemption_time.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 193 | model/schedule/tdma.v | 4 | ✅ | 16/16 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 194 | model/task/absolute_deadline.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 195 | model/task/arrival/sporadic.v | 4 | ✅ | 5/5 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 196 | model/task/arrivals.v | 4 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 197 | model/task/preemption/parameters.v | 4 | ✅ | 13/13 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 198 | model/task/sequentiality.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 199 | analysis/definitions/carry_in.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 200 | analysis/definitions/progress.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 29m58s | fully proven |
| 201 | analysis/facts/behavior/completion.v | 4 | ✅ | 17/17 (100.0%) | ✅ | 17/17 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 65m23s | fully proven |
| 202 | analysis/facts/model/ideal_schedule.v | 4 | ✅ | 10/10 (100.0%) | ✅ | 10/10 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2635m29s | fully proven |
| 203 | analysis/facts/model/sequential.v | 4 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 8m58s | fully proven |
| 204 | analysis/facts/model/task_arrivals.v | 4 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 8m8s | fully proven |
| 205 | analysis/facts/preemption/job/preemptive.v | 4 | ✅ | 3/3 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 913m34s | fully proven |
| 206 | analysis/facts/tdma.v | 4 | ✅ | 6/6 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4065m49s | fully proven |
| 207 | classic/analysis/apa/interference_bound_fp.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 208 | classic/analysis/global/basic/bertogna_edf_theory.v | 4 | ✅ | 19/19 (100.0%) | ◐ | 3/14 (21.4%) | 11 | — | ✅ | ✅ | ✅ | ✅ | 29m44s |  |
| 209 | classic/analysis/global/basic/bertogna_fp_theory.v | 4 | ✅ | 14/14 (100.0%) | ◐ | 0/10 (0.0%) | 10 | — | ✅ | ✅ | ✅ | ✅ | 890m57s |  |
| 210 | classic/analysis/global/basic/interference_bound.v | 4 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 211 | classic/analysis/global/basic/interference_bound_edf.v | 4 | ✅ | 41/41 (100.0%) | ◐ | 7/38 (18.4%) | 31 | — | ✅ | ✅ | ✅ | ✅ | 21m24s |  |
| 212 | classic/analysis/global/basic/interference_bound_fp.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 213 | classic/analysis/global/jitter/bertogna_edf_theory.v | 4 | ✅ | 14/14 (100.0%) | ◐ | 3/14 (21.4%) | 11 | — | ✅ | ✅ | ✅ | ✅ | 25m5s |  |
| 214 | classic/analysis/global/jitter/bertogna_fp_theory.v | 4 | ✅ | 16/12 (133.3%) | ◐ | 0/10 (0.0%) | 10 | — | ✅ | ✅ | ✅ | ✅ | 4792m33s |  |
| 215 | classic/analysis/global/jitter/interference_bound.v | 4 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 216 | classic/analysis/global/jitter/interference_bound_edf.v | 4 | ✅ | 41/41 (100.0%) | ◐ | 4/38 (10.5%) | 34 | — | ✅ | ✅ | ✅ | ✅ | 828m46s |  |
| 217 | classic/analysis/global/jitter/interference_bound_fp.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 218 | classic/analysis/global/parallel/bertogna_edf_comp.v | 4 | ✅ | 38/38 (100.0%) | ◐ | 15/22 (68.2%) | 7 | — | ✅ | ✅ | ✅ | ✅ | 4575m21s |  |
| 219 | classic/analysis/global/parallel/bertogna_fp_comp.v | 4 | ✅ | 20/20 (100.0%) | ◐ | 0/15 (0.0%) | 15 | — | ✅ | ✅ | ✅ | ✅ | 861m9s |  |
| 220 | classic/analysis/uni/basic/fp_rta_theory.v | 4 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 11443m34s | fully proven |
| 221 | classic/analysis/uni/susp/dynamic/jitter/taskset_rta.v | 4 | ✅ | 2/2 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 848m59s | fully proven |
| 222 | classic/analysis/uni/susp/dynamic/oblivious/fp_rta.v | 4 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 17427m12s | fully proven |
| 223 | classic/analysis/uni/susp/sustainability/allcosts/reduction.v | 4 | ✅ | 10/9 (111.1%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 224 | classic/analysis/uni/susp/sustainability/singlecost/reduction.v | 4 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 225 | classic/implementation/apa/bertogna_edf_example.v | 4 | ✅ | 18/17 (105.9%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 25m12s | fully proven |
| 226 | classic/implementation/apa/bertogna_fp_example.v | 4 | ✅ | 27/21 (128.6%) | ◐ | 5/7 (71.4%) | 2 | — | ✅ | ✅ | ✅ | ✅ | 3129m22s |  |
| 227 | classic/implementation/global/basic/bertogna_edf_example.v | 4 | ✅ | 21/13 (161.5%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2510m12s | fully proven |
| 228 | classic/implementation/global/basic/bertogna_fp_example.v | 4 | ✅ | 22/16 (137.5%) | ◐ | 5/6 (83.3%) | 1 | — | ✅ | ✅ | ✅ | ✅ | 2816m16s |  |
| 229 | classic/implementation/global/jitter/bertogna_edf_example.v | 4 | ✅ | 21/13 (161.5%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4131m33s | fully proven |
| 230 | classic/implementation/global/jitter/bertogna_fp_example.v | 4 | ✅ | 22/16 (137.5%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2955m54s | fully proven |
| 231 | classic/model/schedule/apa/constrained_deadlines.v | 4 | ✅ | 7/6 (116.7%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2502m50s | fully proven |
| 232 | classic/model/schedule/apa/platform.v | 4 | ✅ | 5/5 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 233 | classic/model/schedule/global/jitter/interference.v | 4 | ✅ | 9/9 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 20m0s | fully proven |
| 234 | classic/model/schedule/uni/limited/abstract_RTA/abstract_seq_rta.v | 4 | ✅ | 9/8 (112.5%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 1321m58s | fully proven |
| 235 | classic/model/schedule/uni/limited/fixed_priority/response_time_bound.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3871m3s | fully proven |
| 236 | classic/model/schedule/uni/limited/jlfp_instantiation.v | 4 | ✅ | 12/12 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4081m12s | fully proven |
| 237 | classic/model/schedule/uni/susp/build_suspension_table.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3055m31s | fully proven |
| 238 | classic/model/schedule/uni/susp/platform.v | 4 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 239 | classic/model/schedule/uni/susp/valid_schedule.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 240 | model/aggregate/service_of_jobs.v | 4 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 241 | model/aggregate/workload.v | 4 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 748m0s | definitions only |
| 242 | model/priority/deadline_monotonic.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 19m33s | fully proven |
| 243 | model/priority/edf.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4m9s | fully proven |
| 244 | model/priority/fifo.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 5926m59s | fully proven |
| 245 | model/priority/numeric_fixed_priority.v | 4 | ✅ | 5/5 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 5m42s | fully proven |
| 246 | model/priority/rate_monotonic.v | 4 | ✅ | 4/4 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9m45s | fully proven |
| 247 | model/schedule/priority_driven.v | 4 | ✅ | 1/1 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 248 | model/task/arrival/curves.v | 4 | ✅ | 14/14 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 249 | model/task/arrival/periodic.v | 4 | ✅ | 10/10 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 10m57s | fully proven |
| 250 | model/task/preemption/floating_nonpreemptive.v | 4 | ✅ | 3/3 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 251 | model/task/preemption/fully_nonpreemptive.v | 4 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 252 | model/task/preemption/fully_preemptive.v | 4 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 253 | model/task/preemption/limited_preemptive.v | 4 | ✅ | 9/9 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 254 | analysis/definitions/busy_interval.v | 5 | ✅ | 5/5 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2712m35s | fully proven |
| 255 | analysis/definitions/request_bound_function.v | 5 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 256 | analysis/definitions/schedulability.v | 5 | ✅ | 6/6 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2705m31s | fully proven |
| 257 | analysis/facts/behavior/deadlines.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 14m43s | fully proven |
| 258 | analysis/facts/edf.v | 5 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3m44s | fully proven |
| 259 | analysis/facts/model/service_of_jobs.v | 5 | ✅ | 10/10 (100.0%) | ✅ | 10/10 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9317m23s | fully proven |
| 260 | analysis/facts/model/workload.v | 5 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2704m53s | fully proven |
| 261 | analysis/facts/preemption/task/preemptive.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 20m26s | fully proven |
| 262 | analysis/facts/readiness/basic.v | 5 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 14m32s | fully proven |
| 263 | analysis/facts/transform/replace_at.v | 5 | ✅ | 6/6 (100.0%) | ✅ | 6/6 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 29m42s | fully proven |
| 264 | classic/analysis/apa/bertogna_edf_theory.v | 5 | ✅ | 21/21 (100.0%) | ◐ | 0/16 (0.0%) | 16 | — | ✅ | ✅ | ✅ | ✅ | 25m24s |  |
| 265 | classic/analysis/apa/bertogna_fp_theory.v | 5 | ✅ | 13/13 (100.0%) | ◐ | 2/13 (15.4%) | 11 | — | ✅ | ✅ | ✅ | ✅ | 25m59s |  |
| 266 | classic/analysis/apa/interference_bound_edf.v | 5 | ✅ | 41/41 (100.0%) | ◐ | 7/38 (18.4%) | 31 | — | ✅ | ✅ | ✅ | ✅ |  |  |
| 267 | classic/analysis/global/basic/bertogna_edf_comp.v | 5 | ✅ | 38/38 (100.0%) | ◐ | 6/22 (27.3%) | 16 | — | ✅ | ✅ | ✅ | ✅ | 31m34s |  |
| 268 | classic/analysis/global/basic/bertogna_fp_comp.v | 5 | ✅ | 20/20 (100.0%) | ◐ | 0/15 (0.0%) | 15 | — | ✅ | ✅ | ✅ | ✅ | 71m13s |  |
| 269 | classic/analysis/global/jitter/bertogna_edf_comp.v | 5 | ✅ | 40/40 (100.0%) | ◐ | 14/24 (58.3%) | 10 | — | ✅ | ✅ | ✅ | ✅ | 5201m21s |  |
| 270 | classic/analysis/global/jitter/bertogna_fp_comp.v | 5 | ✅ | 20/20 (100.0%) | ◐ | 7/15 (46.7%) | 8 | — | ✅ | ✅ | ✅ | ✅ | 3581m35s |  |
| 271 | classic/analysis/uni/susp/dynamic/jitter/taskset_membership.v | 5 | ✅ | 9/8 (112.5%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 1288m52s | fully proven |
| 272 | classic/analysis/uni/susp/sustainability/allcosts/main_claim.v | 5 | ✅ | 11/11 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 1237m16s | fully proven |
| 273 | classic/analysis/uni/susp/sustainability/allcosts/reduction_properties.v | 5 | ✅ | 35/33 (106.1%) | ✅ | 22/22 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 17123m26s | fully proven |
| 274 | classic/analysis/uni/susp/sustainability/singlecost/reduction_properties.v | 5 | ✅ | 18/18 (100.0%) | ✅ | 18/18 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9768m56s | fully proven |
| 275 | classic/implementation/uni/susp/schedule.v | 5 | ✅ | 11/11 (100.0%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 71m45s | fully proven |
| 276 | model/readiness/suspension.v | 5 | ✅ | 4/4 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 17m7s | fully proven |
| 277 | analysis/definitions/priority_inversion.v | 5 | ✅ | 4/4 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 278 | analysis/facts/behavior/all.v | 5 | ✅ | — | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 279 | analysis/facts/model/rbf.v | 5 | ✅ | 39/37 (105.4%) | ✅ | 8/8 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 9168m12s | fully proven |
| 280 | analysis/facts/transform/swaps.v | 5 | ✅ | 22/22 (100.0%) | ✅ | 22/22 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4573m49s | fully proven |
| 281 | classic/analysis/apa/bertogna_edf_comp.v | 5 | ✅ | 38/38 (100.0%) | ◐ | 0/22 (0.0%) | 22 | — | ✅ | ✅ | ✅ | ✅ |  |  |
| 282 | classic/analysis/apa/bertogna_fp_comp.v | 5 | ✅ | 20/20 (100.0%) | ◐ | 7/15 (46.7%) | 8 | — | ✅ | ✅ | ✅ | ✅ | 3638m59s |  |
| 283 | classic/implementation/uni/susp/dynamic/oblivious/fp_rta_example.v | 5 | ✅ | 18/18 (100.0%) | ✅ | 5/5 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2545m26s | fully proven |
| 284 | model/task/suspension/dynamic.v | 5 | ✅ | 2/2 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 285 | analysis/facts/busy_interval/busy_interval.v | 5 | ✅ | 14/14 (100.0%) | ✅ | 14/14 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 11043m34s | fully proven |
| 286 | analysis/facts/preemption/job/limited.v | 5 | ✅ | 10/10 (100.0%) | ✅ | 10/10 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 39m4s | fully proven |
| 287 | analysis/facts/preemption/job/nonpreemptive.v | 5 | ✅ | 3/3 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2679m9s | fully proven |
| 288 | analysis/facts/preemption/rtc_threshold/job_preemptable.v | 5 | ✅ | 14/14 (100.0%) | ✅ | 14/14 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 4927m11s | fully proven |
| 289 | analysis/transform/prefix.v | 5 | ✅ | 3/3 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2651m49s | fully proven |
| 290 | analysis/abstract/run_to_completion.v | 5 | ✅ | 4/4 (100.0%) | ✅ | 4/4 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 38m17s | fully proven |
| 291 | analysis/facts/busy_interval/carry_in.v | 5 | ✅ | 9/9 (100.0%) | ✅ | 9/9 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 5041m58s | fully proven |
| 292 | analysis/facts/busy_interval/priority_inversion.v | 5 | ✅ | 24/24 (100.0%) | ✅ | 23/23 (100.0%) | 0 | — | ✅ | ⚠ | ✅ | ✅ | 11135m37s | fully proven |
| 293 | analysis/facts/preemption/rtc_threshold/nonpreemptive.v | 5 | ✅ | 3/3 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2621m1s | fully proven |
| 294 | analysis/facts/preemption/rtc_threshold/preemptive.v | 5 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 31m37s | fully proven |
| 295 | analysis/facts/preemption/task/floating.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 26m9s | fully proven |
| 296 | analysis/facts/preemption/task/limited.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2632m4s | fully proven |
| 297 | analysis/facts/preemption/task/nonpreemptive.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2506m59s | fully proven |
| 298 | analysis/transform/edf_trans.v | 5 | ✅ | 6/6 (100.0%) | — | — | 0 | — | ✅ | ✅ | ✅ | ✅ | 0s | definitions only |
| 299 | analysis/abstract/abstract_rta.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 13/13 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 10943m34s | fully proven |
| 300 | analysis/facts/preemption/rtc_threshold/floating.v | 5 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 15m24s | fully proven |
| 301 | analysis/facts/preemption/rtc_threshold/limited.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12382m2s | fully proven |
| 302 | analysis/facts/transform/edf_opt.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 42/42 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12346m2s | fully proven |
| 303 | analysis/abstract/abstract_seq_rta.v | 5 | ✅ | 18/18 (100.0%) | ✅ | 14/14 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ |  | fully proven |
| 304 | results/edf/optimality.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 2/2 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12359m46s | fully proven |
| 305 | analysis/abstract/ideal_jlfp_rta.v | 5 | ✅ | 18/18 (100.0%) | ✅ | 9/9 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 12333m24s | fully proven |
| 306 | results/edf/rta/bounded_pi.v | 5 | ✅ | 20/17 (117.6%) | ✅ | 15/15 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3434m10s | fully proven |
| 307 | results/fixed_priority/rta/bounded_pi.v | 5 | ✅ | 7/7 (100.0%) | ✅ | 7/7 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 3291m34s | fully proven |
| 308 | results/edf/rta/bounded_nps.v | 5 | ✅ | 4/4 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2866m48s | fully proven |
| 309 | results/fixed_priority/rta/bounded_nps.v | 5 | ✅ | 4/4 (100.0%) | ✅ | 3/3 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2311m35s | fully proven |
| 310 | results/edf/rta/floating_nonpreemptive.v | 5 | ✅ | 2/2 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 1260m46s | fully proven |
| 311 | results/edf/rta/fully_nonpreemptive.v | 5 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 1197m12s | fully proven |
| 312 | results/edf/rta/fully_preemptive.v | 5 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 32m54s | fully proven |
| 313 | results/edf/rta/limited_preemptive.v | 5 | ✅ | 1/1 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2332m51s | fully proven |
| 314 | results/fixed_priority/rta/floating_nonpreemptive.v | 5 | ✅ | 3/3 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 16m25s | fully proven |
| 315 | results/fixed_priority/rta/fully_nonpreemptive.v | 5 | ✅ | 3/3 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 14m4s | fully proven |
| 316 | results/fixed_priority/rta/fully_preemptive.v | 5 | ✅ | 7/7 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 13m32s | fully proven |
| 317 | results/fixed_priority/rta/limited_preemptive.v | 5 | ✅ | 3/3 (100.0%) | ✅ | 1/1 (100.0%) | 0 | — | ✅ | ✅ | ✅ | ✅ | 2358m20s | fully proven |

## Partial (has sorry)

| # | File | Layer | Proofs (ok/total) | Sorry | Notes |
|---|------|-------|-------------------|-------|-------|
| 1 | classic/analysis/global/parallel/bertogna_edf_theory.v | 4 | 0/9 (0.0%) | 9 |  |
| 2 | classic/analysis/global/parallel/bertogna_fp_theory.v | 4 | 4/6 (66.7%) | 2 |  |
| 3 | classic/analysis/global/parallel/interference_bound_edf.v | 4 | 3/25 (12.0%) | 22 |  |
| 4 | classic/analysis/global/basic/bertogna_edf_theory.v | 4 | 3/14 (21.4%) | 11 |  |
| 5 | classic/analysis/global/basic/bertogna_fp_theory.v | 4 | 0/10 (0.0%) | 10 |  |
| 6 | classic/analysis/global/basic/interference_bound_edf.v | 4 | 7/38 (18.4%) | 31 |  |
| 7 | classic/analysis/global/jitter/bertogna_edf_theory.v | 4 | 3/14 (21.4%) | 11 |  |
| 8 | classic/analysis/global/jitter/bertogna_fp_theory.v | 4 | 0/10 (0.0%) | 10 |  |
| 9 | classic/analysis/global/jitter/interference_bound_edf.v | 4 | 4/38 (10.5%) | 34 |  |
| 10 | classic/analysis/global/parallel/bertogna_edf_comp.v | 4 | 15/22 (68.2%) | 7 |  |
| 11 | classic/analysis/global/parallel/bertogna_fp_comp.v | 4 | 0/15 (0.0%) | 15 |  |
| 12 | classic/implementation/apa/bertogna_fp_example.v | 4 | 5/7 (71.4%) | 2 |  |
| 13 | classic/implementation/global/basic/bertogna_fp_example.v | 4 | 5/6 (83.3%) | 1 |  |
| 14 | classic/analysis/apa/bertogna_edf_theory.v | 5 | 0/16 (0.0%) | 16 |  |
| 15 | classic/analysis/apa/bertogna_fp_theory.v | 5 | 2/13 (15.4%) | 11 |  |
| 16 | classic/analysis/apa/interference_bound_edf.v | 5 | 7/38 (18.4%) | 31 |  |
| 17 | classic/analysis/global/basic/bertogna_edf_comp.v | 5 | 6/22 (27.3%) | 16 |  |
| 18 | classic/analysis/global/basic/bertogna_fp_comp.v | 5 | 0/15 (0.0%) | 15 |  |
| 19 | classic/analysis/global/jitter/bertogna_edf_comp.v | 5 | 14/24 (58.3%) | 10 |  |
| 20 | classic/analysis/global/jitter/bertogna_fp_comp.v | 5 | 7/15 (46.7%) | 8 |  |
| 21 | classic/analysis/apa/bertogna_edf_comp.v | 5 | 0/22 (0.0%) | 22 |  |
| 22 | classic/analysis/apa/bertogna_fp_comp.v | 5 | 7/15 (46.7%) | 8 |  |

## Granular Statistics

### Declaration (Statement) Level

| Metric | Count |
|--------|-------|
| Coq declarations (source) | 2933 |
| Lean declarations (target) | 3027 |
| Translation coverage | 103.2% |
| Files with statements done | 317/317 (100.0%) |

### Proof Level (Ground Truth)

| Metric | Count |
|--------|-------|
| Coq proofs (Qed/Defined in source) | 1804 |
| Lean proofs truly proven (#print axioms clean) | 1502 |
| Polluted proofs (depend on sorry'd theorems) | 0 |
| Sorry remaining in .lean files | 302 |
| True proof rate (excludes polluted) | 83.3% |
| .lean files generated | 317 |


## Proof Strategy Distribution

| Strategy | Count |
|----------|-------|
| Auto tactic (omega/simp/aesop) | 31 |
| Reference Coq proof | 86 |
| Free exploration | 0 |

---
*Dashboard auto-generated by scripts/stats.ts — 3-agent pipeline*
