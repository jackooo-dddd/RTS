# Translation-order continuous run (started 2026-09-24 03:56:07 +08:00)

Machine authority is each published `Validation/planning/v06_pipeline/*module_status.json` and paired manifest, not this narrative. The run started from **36/357 accepted files and 317/2439 accepted declarations**. Through Rank 49 `model/processor/ideal_uni_exceed.v`, publication reached **48/357 files and 353/2439 declarations**: **12 newly accepted files, 36 newly accepted declarations**, with zero published translated-but-uncertified declarations.

| Rank | Source file | New accepted declarations | Canonical evidence |
|---:|---|---:|---|
| 38 | `analysis/definitions/finish_time.v` | 5 | [report](../files/analysis/definitions/2026-09-24_035607_finish_time.md) |
| 39 | `analysis/definitions/sbf/average.v` | 2 | [report](../files/analysis/definitions/sbf/2026-09-24_043858_average.md) |
| 40 | `analysis/definitions/sbf/periodic.v` | 2 | [report](../files/analysis/definitions/sbf/2026-09-24_051850_periodic.md) |
| 41 | `analysis/definitions/sbf/pred.v` | 5 | [report](../files/analysis/definitions/sbf/2026-09-24_053710_pred.md) |
| 42 | `analysis/definitions/service.v` | 2 | [report](../files/analysis/definitions/2026-09-24_060952_service.md) |
| 43 | `analysis/definitions/sbf/plain.v` | 3 | [report](../files/analysis/definitions/sbf/2026-09-24_062700_plain.md) |
| 44 | `analysis/definitions/schedule_prefix.v` | 3 | [report](../files/analysis/definitions/2026-09-24_064250_schedule_prefix.md) |
| 45 | `analysis/definitions/job_response_time.v` | 1 | [report](../files/analysis/definitions/2026-09-24_072741_job_response_time.md) |
| 46 | `analysis/transform/swap.v` | 2 | [report](../files/analysis/transform/2026-09-24_075000_swap.md) |
| 47 | `model/job/properties.v` | 2 | [report](../files/model/job/2026-09-24_090700_properties.md) |
| 48 | `model/processor/ideal.v` | 2 | [report](../files/model/processor/2026-09-24_093100_ideal.md) |
| 49 | `model/processor/ideal_uni_exceed.v` | 7 | [report](../files/model/processor/2026-09-24_102300_ideal_uni_exceed.md) |

All listed publications used the official pinned v0.6 source, compiled production Lean artifact, `lean4export`, `rocq-lean-import`, Rocq correspondence certificate, exact-type or applicable interface guard, `Print Assumptions`, and fail-closed content-addressed publication. Certificate-specific trust boundaries and reused bridges are in the canonical per-file reports. The export sizes at Rank 45 (120,402 lines), Rank 46 (111,649 lines), and Rank 47 (6,034 lines) show that transitive artifact size varies with representation/dependencies and is not rank-monotonic. Rank 46's expensive export/import resulted in only one new operation bridge (Nat Boolean equality); `swapped` reused `replace_at` correspondence. Rank 47 reused the certified Bool/List/equality adapter pattern and added minimal `arrives_in`/Nat-order operations.

Rank 48 imported a 119,008-line actual artifact. Its full concrete `ProcessorState`
certificate covers two-sided Option/Unit carriers, scheduled/supply/service
fields, and both law statements; `ideal_is_idle` is separately certified.
Rocq 9.3 needed only a validation-copy patch to the historical `Program`
obligation proof scripts, leaving public source commands and bodies untouched.

Rank 49 imported a 121,417-line actual artifact without statement-only export.
Its seven-declaration certificate preserves the three informative state
constructors, MathComp Boolean equality and informative reflection, all three
processor observations, and both class laws. The proof uses explicit
source/imported state roundtrips and the previously certified Nat/Bool
operation bridges. A separate Rocq 9.3 compatibility-copy patch changes only
the two historical `Program` obligation proof scripts. All seven passed
exact-type and fail-closed assumption gates; five retain the explicit
Prop/SProp interpretation boundary.
