# Report: `classic/model/schedule/global/basic/schedule.v` (rank 27)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/global/basic/schedule.v` |
| sha256 | `c8e5b4b54ac2baa8b5412ff7b6cbaedeef3705a1a51e88ee4c301bd7425a37b3` |
| Lean module | `Prosa/Classic/Model/Schedule/Global/Basic/Schedule.lean` (namespace `Prosa.Classic.Model.Schedule.Global.Basic.Schedule`) |
| Tier / layer | S / 9 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (39 source → Lean, same names)

- `Definition` `Schedule.processor`
- `Definition` `Schedule.schedule`
- `Definition` `Schedule.scheduled_on`
- `Definition` `Schedule.scheduled`
- `Definition` `Schedule.is_idle`
- `Definition` `Schedule.service_at`
- `Definition` `Schedule.service`
- `Definition` `Schedule.service_during`
- `Definition` `Schedule.completed`
- `Definition` `Schedule.pending`
- `Definition` `Schedule.backlogged`
- `Definition` `Schedule.carried_in`
- `Definition` `Schedule.carried_out`
- `Definition` `Schedule.jobs_scheduled_at`
- `Definition` `Schedule.jobs_scheduled_between`
- `Definition` `Schedule.sequential_jobs`
- `Definition` `Schedule.jobs_must_arrive_to_execute`
- `Definition` `Schedule.completed_jobs_dont_execute`
- `Definition` `Schedule.jobs_come_from_arrival_sequence`
- `Lemma` `Schedule.not_scheduled_no_service`
- `Lemma` `Schedule.cumulative_service_implies_service`
- `Lemma` `Schedule.service_implies_cumulative_service`
- `Lemma` `Schedule.service_at_most_one`
- `Lemma` `Schedule.cumulative_service_le_delta`
- `Lemma` `Schedule.completion_monotonic`
- `Lemma` `Schedule.completed_implies_not_scheduled`
- `Lemma` `Schedule.cumulative_service_le_job_cost`
- `Lemma` `Schedule.service_before_job_arrival_zero`
- `Lemma` `Schedule.cumulative_service_before_job_arrival_zero`
- `Lemma` `Schedule.service_before_arrival_eq_service_during`
- `Lemma` `Schedule.scheduled_implies_pending`
- `Lemma` `Schedule.mem_scheduled_jobs_eq_scheduled`
- `Lemma` `Schedule.scheduled_jobs_uniq`
- `Lemma` `Schedule.num_scheduled_jobs_le_num_cpus`
- `Definition` `ScheduleOfSporadicTask.task_scheduled_on`
- `Definition` `ScheduleOfSporadicTask.task_is_scheduled`
- `Definition` `ScheduleOfSporadicTask.jobs_of_task_scheduled_between`
- `Definition` `ScheduleOfSporadicTask.jobs_of_same_task_dont_execute_in_parallel`
- `Lemma` `ScheduleOfSporadicTask.cumulative_service_le_task_cost`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `service_at_eq_zero_iff`, `service_succ`.

## Representation notes

Global multiprocessor schedules (Rocq modules `Schedule` and
`ScheduleOfSporadicTask`).

Representation notes:
* `processor num_cpus := 'I_num_cpus` is `Fin num_cpus`; a schedule is
  `processor num_cpus → time → Option Job` (processor first, as in the source).
* Binder lists follow the Rocq contract: schedule notions take
  `{Job} {num_cpus} sched` (implicit carriers), `completed` adds `job_cost`,
  `pending`/`backlogged`/`carried_in`/`carried_out` add `job_arrival job_cost`;
  each lemma takes exactly the section hypotheses its Rocq proof uses.
* `sched cpu t == Some j` is `decide (sched cpu t = some j)`; the Boolean finite
  quantifier `[exists cpu, P cpu]` over `'I_n` is `(List.finRange n).any P`
  (as in `ord_quantifier`).
* `\sum_(cpu < n | P cpu) 1` is `∑ cpu ∈ Finset.univ.filter (P · = true), 1`;
  `\sum_(t1 <= t < t2) F t` is `∑ t ∈ Finset.Ico t1 t2, F t`.
* `\cat_(cpu < n) F cpu` is the v0.6 helper `bigCatFin F`; `\cat_(t1 <= t < t2)`
  is `bigCat t1 t2`; MathComp `undup` (keeps last occurrences) is
  `List.dedup` (same behaviour, as used throughout the v0.6 translation).
* Boolean statements: `b1 = b2` between Booleans is kept as an equation of
  `Bool`s; `x != 0` in proposition position is `(!decide (x = 0)) = true`; Boolean
  chains `a <= b < c` are `(decide (a ≤ b) && decide (b < c)) = true`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
