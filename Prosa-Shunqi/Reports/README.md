# 翻译与验证报告

## 当前状态

<!-- V06_STATUS_BEGIN -->
截至 2026-09-30，正式 machine state 记录 **328/357 个文件、2106/2439 个 public declarations 已验收**。依据：[最新累计 status](../Validation/planning/v06_pipeline/results_rta_ideal_fp_floating_nonpreemptive_module_status.json)。表中的“是”仅表示已有 `ACCEPTED_V06_FILE`；“否”可能是未开始、进行中或受阻，不能据此推断尚未翻译。零声明文件也只有通过模块接口验收才写“是”。
<!-- V06_STATUS_END -->

<!-- V06_NAV_BEGIN -->
<details open>
<summary><b>📊 Translation Status</b></summary>

| Progress | Latest completed | Quick navigation |
|---|---|---|
| **328/357 files** · **2106/2439 declarations** | **Rank 294** · `results/rta/ideal/fp/floating_nonpreemptive.v` | [🎯 Jump to latest completed](#latest-completed) · [✅ Finished](#finished-files) · [⏳ Unfinished](#unfinished-files) |

</details>
<!-- V06_NAV_END -->


- [Rank 50 `model/processor/overheads.v` 报告](files/model/processor/2026-09-24_111300_overheads.md)：完整 proof-body 导入关闭了原先 11 个 class/proof-field statement-only 依赖。
- [Rank 52 `model/processor/restricted_supply.v` 报告](files/model/processor/2026-09-24_144500_restricted_supply.md)：记录 concrete processor state 的整文件验证。
- [`util/lcmseq.v` 报告](files/util/2026-09-23_073256_lcmseq.md)：原阻塞项；根因为旧 export 配置 `statement_only: ["*"]`，已于 2026-09-29 以完整 proof-body 导出验收（报告末尾追加）。
- [本次连续执行汇总](runs/2026-09-24_035607_translation_order_continuous_run.md)：跨文件进展与运行背景；不替代正式状态。
- [Finish Time 语义验证案例](casestudy/finish_time_case_study.md)：官方 Rocq、production Lean、导入后的完整 `Print`、correspondence 与 assumption gate。

下一个执行文件须依据[文件顺序](../v06_file_translation_order.md)、最新 status/manifest 和文件依赖图重新判定；本页不固定其 READY 状态。

## 逐文件验证状态

按正式执行顺序列出 pinned v0.6 的全部 357 个 source file；声明数来自 `Validation/planning/v06_dependency/declaration_inventory.csv`，完成状态来自最新有效的逐文件 status，并与累计 machine state 核对。此表是报告快照，不代替 artifact/hash/assumption 的正式验收门槛。

完成记录时间按香港本地时间（UTC+08:00）的“月:日:时:分”显示，优先取 manifest 的 `published_at` 或 canonical report 明确记载的整文件验收事件；其余旧记录使用首次 `ACCEPTED_V06_FILE` status 文件写入时间作为近似机器记录时间，不能将它理解为独立核验的精确完成时刻。[逐文件时间依据](../Validation/planning/v06_pipeline/reports_readme_completion_evidence.json)保存了来源和哈希；报告文件名中的时间是首次写报告的时间，不是验收时间。

<a id="file-validation-table"></a>

<!-- V06_FILE_TABLE_BEGIN -->
<details open>
<summary><b>✅ Finished — 328 files</b></summary>

<a id="finished-files"></a>

| Rank | Layer | v0.6 source file | Public declarations | 验证完成 | 完成记录时间（月:日:时:分） |
| ---: | ---: | --- | ---: | :---: | :---: |
| 1 | 0 | [`behavior/time.v`](files/behavior/2026-09-20_210930_time.md) | 2 | ✅ 是 | 09:20:21:17 |
| 2 | 0 | [`util/tactics.v`](files/util/2026-09-20_214230_tactics.md) | 2 | ✅ 是 | 09:20:23:48 |
| 3 | 0 | [`util/notation.v`](files/util/2026-09-20_214230_notation.md) | 1 | ✅ 是 | 09:20:23:48 |
| 4 | 0 | [`util/rel.v`](files/util/2026-09-20_214230_rel.md) | 3 | ✅ 是 | 09:20:23:48 |
| 5 | 0 | [`util/seqset.v`](files/util/2026-09-20_214230_seqset.md) | 3 | ✅ 是 | 09:20:23:48 |
| 6 | 0 | [`util/subadditivity.v`](files/util/2026-09-20_214230_subadditivity.md) | 6 | ✅ 是 | 09:20:23:48 |
| 7 | 0 | [`util/supremum.v`](files/util/2026-09-20_214230_supremum.md) | 7 | ✅ 是 | 09:20:23:48 |
| 8 | 1 | [`util/nat.v`](files/util/2026-09-21_082258_nat.md) | 2 | ✅ 是 | 09:21:09:42 |
| 9 | 1 | [`util/unit_growth.v`](files/util/2026-09-21_082258_unit_growth.md) | 12 | ✅ 是 | 09:21:11:35 |
| 10 | 1 | [`util/search_arg.v`](files/util/2026-09-21_082258_search_arg.md) | 8 | ✅ 是 | 09:21:13:21 |
| 11 | 1 | [`util/list.v`](files/util/2026-09-21_082258_list.md) | 57 | ✅ 是 | 09:21:23:27 |
| 12 | 2 | [`util/sum.v`](files/util/2026-09-21_082258_sum.md) | 25 | ✅ 是 | 09:22:03:37 |
| 13 | 0 | [`util/epsilon.v`](files/util/2026-09-22_034433_epsilon.md) | 0 | ✅ 是 | 09:22:03:44 |
| 14 | 0 | [`util/bigop.v`](files/util/2026-09-22_034433_bigop.md) | 1 | ✅ 是 | 09:22:04:22 |
| 15 | 0 | [`util/setoid.v`](files/util/2026-09-22_042247_setoid.md) | 3 | ✅ 是 | 09:22:04:48 |
| 16 | 2 | [`util/poet.v`](files/util/2026-09-22_044913_poet.md) | 1 | ✅ 是 | 09:22:05:24 |
| 17 | 2 | [`util/bigcat.v`](files/util/2026-09-22_053020_bigcat.md) | 13 | ✅ 是 | 09:22:08:23 |
| 18 | 2 | [`util/minmax.v`](files/util/2026-09-22_082537_minmax.md) | 10 | ✅ 是 | 09:22:10:35 |
| 19 | 2 | [`util/div_mod.v`](files/util/2026-09-22_103919_div_mod.md) | 15 | ✅ 是 | 09:22:13:25 |
| 20 | 2 | [`util/nondecreasing.v`](files/util/2026-09-22_133028_nondecreasing.md) | 33 | ✅ 是 | 09:22:20:31 |
| 21 | 3 | [`util/all.v`](files/util/2026-09-22_203705_all.md) | 0 | ✅ 是 | 09:22:21:03 |
| 22 | 4 | [`behavior/job.v`](files/behavior/2026-09-22_210645_job.md) | 5 | ✅ 是 | 09:22:22:26 |
| 23 | 5 | [`behavior/arrival_sequence.v`](files/behavior/2026-09-22_222929_arrival_sequence.md) | 14 | ✅ 是 | 09:23:00:23 |
| 24 | 6 | [`behavior/schedule.v`](files/behavior/2026-09-23_002720_schedule.md) | 5 | ✅ 是 | 09:23:09:56 |
| 25 | 7 | [`behavior/service.v`](files/behavior/2026-09-23_023952_service.md) | 12 | ✅ 是 | 09:23:10:06 |
| 26 | 8 | [`behavior/ready.v`](files/behavior/2026-09-23_042533_ready.md) | 7 | ✅ 是 | 09:23:05:38 |
| 27 | 9 | [`behavior/all.v`](files/behavior/2026-09-23_054506_all.md) | 0 | ✅ 是 | 09:23:05:55 |
| 28 | 7 | [`model/processor/supply.v`](files/model/processor/2026-09-23_055700_supply.md) | 5 | ✅ 是 | 09:23:14:32 |
| 29 | 0 | [`util/int.v`](files/util/2026-09-23_072030_int.md) | 0 | ✅ 是 | 09:23:14:35 |
| 30 | 1 | [`util/lcmseq.v`](files/util/2026-09-23_073256_lcmseq.md) | 5 | ✅ 是 | 09:29:21:09 |
| 31 | 3 | [`util/fixpoint.v`](files/util/2026-09-23_150425_fixpoint.md) | 17 | ✅ 是 | 09:23:18:54 |
| 32 | 2 | [`util/superadditivity.v`](files/util/2026-09-23_160337_superadditivity.md) | 12 | ✅ 是 | 09:23:21:08 |
| 33 | 4 | [`implementation/definitions/extrapolated_arrival_curve.v`](files/implementation/definitions/2026-09-23_211129_extrapolated_arrival_curve.md) | 21 | ✅ 是 | 09:24:00:47 |
| 34 | 5 | [`analysis/definitions/sbf/sbf.v`](files/analysis/definitions/sbf/2026-09-24_005022_sbf.md) | 1 | ✅ 是 | 09:24:01:06 |
| 35 | 5 | [`implementation/definitions/arrival_bound.v`](files/implementation/definitions/2026-09-24_010800_arrival_bound.md) | 3 | ✅ 是 | 09:24:01:42 |
| 36 | 5 | [`implementation/facts/extrapolated_arrival_curve.v`](files/implementation/facts/2026-09-24_014411_extrapolated_arrival_curve.md) | 10 | ✅ 是 | 09:24:03:08 |
| 37 | 8 | [`analysis/definitions/completion_sequence.v`](files/analysis/definitions/2026-09-24_031052_completion_sequence.md) | 1 | ✅ 是 | 09:24:03:53 |
| 38 | 8 | [`analysis/definitions/finish_time.v`](files/analysis/definitions/2026-09-24_035607_finish_time.md) | 5 | ✅ 是 | 09:24:04:37 |
| 39 | 8 | [`analysis/definitions/sbf/average.v`](files/analysis/definitions/sbf/2026-09-24_043858_average.md) | 2 | ✅ 是 | 09:24:05:16 |
| 40 | 8 | [`analysis/definitions/sbf/periodic.v`](files/analysis/definitions/sbf/2026-09-24_051850_periodic.md) | 2 | ✅ 是 | 09:24:05:36 |
| 41 | 8 | [`analysis/definitions/sbf/pred.v`](files/analysis/definitions/sbf/2026-09-24_053710_pred.md) | 5 | ✅ 是 | 09:24:06:07 |
| 42 | 8 | [`analysis/definitions/service.v`](files/analysis/definitions/2026-09-24_060952_service.md) | 2 | ✅ 是 | 09:24:06:26 |
| 43 | 9 | [`analysis/definitions/sbf/plain.v`](files/analysis/definitions/sbf/2026-09-24_062700_plain.md) | 3 | ✅ 是 | 09:24:06:41 |
| 44 | 9 | [`analysis/definitions/schedule_prefix.v`](files/analysis/definitions/2026-09-24_064250_schedule_prefix.md) | 3 | ✅ 是 | 09:24:07:25 |
| 45 | 10 | [`analysis/definitions/job_response_time.v`](files/analysis/definitions/2026-09-24_072741_job_response_time.md) | 1 | ✅ 是 | 09:24:07:48 |
| 46 | 10 | [`analysis/transform/swap.v`](files/analysis/transform/2026-09-24_075000_swap.md) | 2 | ✅ 是 | 09:24:09:06 |
| 47 | 10 | [`model/job/properties.v`](files/model/job/2026-09-24_090700_properties.md) | 2 | ✅ 是 | 09:24:09:29 |
| 48 | 10 | [`model/processor/ideal.v`](files/model/processor/2026-09-24_093100_ideal.md) | 2 | ✅ 是 | 09:24:10:19 |
| 49 | 10 | [`model/processor/ideal_uni_exceed.v`](files/model/processor/2026-09-24_102300_ideal_uni_exceed.md) | 7 | ✅ 是 | 09:24:11:11 |
| 50 | 10 | [`model/processor/overheads.v`](files/model/processor/2026-09-24_111300_overheads.md) | 13 | ✅ 是 | 09:24:17:04 |
| 51 | 10 | [`model/processor/platform_properties.v`](files/model/processor/2026-09-24_134231_platform_properties.md) | 6 | ✅ 是 | 09:24:14:40 |
| 52 | 10 | [`model/processor/restricted_supply.v`](files/model/processor/2026-09-24_144500_restricted_supply.md) | 5 | ✅ 是 | 09:24:15:24 |
| 53 | 10 | [`model/processor/spin.v`](files/model/processor/2026-09-24_233051_spin.md) | 5 | ✅ 是 | 09:25:00:10 |
| 54 | 10 | [`model/processor/varspeed.v`](files/model/processor/2026-09-24_233051_varspeed.md) | 5 | ✅ 是 | 09:25:00:26 |
| 55 | 10 | [`model/readiness/basic.v`](files/model/readiness/2026-09-25_003818_basic.md) | 0 | ✅ 是 | 09:25:12:43 |
| 56 | 10 | [`model/readiness/jitter.v`](files/model/readiness/2026-09-25_005643_jitter.md) | 2 | ✅ 是 | 09:25:20:56 |
| 57 | 10 | [`model/schedule/edf.v`](files/model/schedule/2026-09-25_003300_edf.md) | 2 | ✅ 是 | 09:25:01:27 |
| 58 | 10 | [`model/schedule/nonpreemptive.v`](files/model/schedule/2026-09-25_010632_nonpreemptive.md) | 1 | ✅ 是 | 09:25:01:46 |
| 59 | 10 | [`model/schedule/scheduled.v`](files/model/schedule/2026-09-25_020323_scheduled.md) | 3 | ✅ 是 | 09:25:02:03 |
| 60 | 10 | [`model/schedule/work_conserving.v`](files/model/schedule/2026-09-25_020627_work_conserving.md) | 2 | ✅ 是 | 09:25:02:06 |
| 61 | 10 | [`model/task/concept.v`](files/model/task/2026-09-25_024332_concept.md) | 19 | ✅ 是 | 09:25:02:43 |
| 62 | 11 | [`analysis/abstract/definitions.v`](files/analysis/abstract/2026-09-25_025723_definitions.md) | 15 | ✅ 是 | 09:25:07:30 |
| 63 | 11 | [`analysis/abstract/search_space.v`](files/analysis/abstract/2026-09-25_035747_search_space.md) | 6 | ✅ 是 | 09:25:05:33 |
| 64 | 11 | [`analysis/definitions/overheads/schedule_change.v`](files/analysis/definitions/overheads/2026-09-25_025541_schedule_change.md) | 4 | ✅ 是 | 09:25:02:55 |
| 65 | 11 | [`analysis/definitions/task_schedule.v`](files/analysis/definitions/2026-09-25_040200_task_schedule.md) | 7 | ✅ 是 | 09:25:05:14 |
| 66 | 11 | [`analysis/facts/behavior/supply.v`](files/analysis/facts/behavior/2026-09-25_030754_supply.md) | 16 | ✅ 是 | 09:25:04:44 |
| 67 | 11 | [`analysis/facts/model/ideal_uni_exceed.v`](files/analysis/facts/model/2026-09-25_030249_ideal_uni_exceed.md) | 7 | ✅ 是 | 09:25:04:17 |
| 68 | 11 | [`analysis/facts/model/restricted_supply/schedule.v`](files/analysis/facts/model/restricted_supply/2026-09-25_045915_schedule.md) | 3 | ✅ 是 | 09:25:05:48 |
| 69 | 11 | [`analysis/facts/model/task_cost.v`](files/analysis/facts/model/2026-09-25_061700_task_cost.md) | 2 | ✅ 是 | 09:25:06:17 |
| 70 | 11 | [`analysis/facts/model/uniprocessor.v`](files/analysis/facts/model/2026-09-25_062000_uniprocessor.md) | 1 | ✅ 是 | 09:25:21:12 |
| 71 | 11 | [`implementation/definitions/generic_scheduler.v`](files/implementation/definitions/2026-09-25_060400_generic_scheduler.md) | 4 | ✅ 是 | 09:25:06:53 |
| 72 | 11 | [`model/priority/definitions.v`](files/model/priority/2026-09-25_072012_definitions.md) | 20 | ✅ 是 | 09:25:21:20 |
| 73 | 11 | [`model/schedule/tdma.v`](files/model/schedule/2026-09-25_131026_tdma.md) | 15 | ✅ 是 | 09:25:20:34 |
| 74 | 11 | [`model/task/absolute_deadline.v`](files/model/task/2026-09-25_075700_absolute_deadline.md) | 1 | ✅ 是 | 09:25:08:00 |
| 75 | 11 | [`model/task/arrival/sporadic.v`](files/model/task/arrival/2026-09-25_155702_sporadic.md) | 5 | ✅ 是 | 09:25:15:57 |
| 76 | 11 | [`model/task/arrivals.v`](files/model/task/2026-09-25_160500_arrivals.md) | 13 | ✅ 是 | 09:25:21:39 |
| 77 | 11 | [`model/task/jitter.v`](files/model/task/2026-09-25_214925_jitter.md) | 3 | ✅ 是 | 09:25:21:49 |
| 78 | 12 | [`analysis/abstract/restricted_supply/busy_sbf.v`](files/analysis/abstract/restricted_supply/2026-09-25_171435_busy_sbf.md) | 2 | ✅ 是 | 09:25:22:09 |
| 79 | 12 | [`analysis/definitions/infinite_jobs.v`](files/analysis/definitions/2026-09-25_222426_infinite_jobs.md) | 1 | ✅ 是 | 09:25:22:24 |
| 80 | 12 | [`analysis/definitions/readiness_interference.v`](files/analysis/definitions/2026-09-25_224646_readiness_interference.md) | 3 | ✅ 是 | 09:25:22:46 |
| 81 | 12 | [`analysis/facts/SBF.v`](files/analysis/facts/2026-09-25_225344_SBF.md) | 3 | ✅ 是 | 09:25:23:11 |
| 82 | 12 | [`analysis/facts/behavior/arrivals.v`](files/analysis/facts/behavior/2026-09-25_232639_arrivals.md) | 45 | ✅ 是 | 09:26:00:14 |
| 83 | 12 | [`analysis/facts/tdma.v`](files/analysis/facts/2026-09-26_003457_tdma.md) | 6 | ✅ 是 | 09:26:00:34 |
| 84 | 12 | [`model/priority/coercion.v`](files/model/priority/2026-09-26_004921_coercion.md) | 10 | ✅ 是 | 09:26:00:49 |
| 85 | 12 | [`model/task/arrival/curves.v`](files/model/task/arrival/2026-09-26_010350_curves.md) | 14 | ✅ 是 | 09:26:01:03 |
| 86 | 12 | [`model/task/arrival/request_bound_functions.v`](files/model/task/arrival/2026-09-26_011446_request_bound_functions.md) | 8 | ✅ 是 | 09:26:01:14 |
| 87 | 12 | [`model/task/arrival/task_max_inter_arrival.v`](files/model/task/arrival/2026-09-26_012716_task_max_inter_arrival.md) | 5 | ✅ 是 | 09:26:01:26 |
| 88 | 12 | [`model/task/sequentiality.v`](files/model/task/2026-09-26_014301_sequentiality.md) | 2 | ✅ 是 | 09:26:01:42 |
| 89 | 13 | [`analysis/definitions/delay_propagation.v`](files/analysis/definitions/2026-09-26_021113_delay_propagation.md) | 7 | ✅ 是 | 09:26:02:10 |
| 90 | 13 | [`analysis/facts/model/scheduled.v`](files/analysis/facts/model/2026-09-26_023742_scheduled.md) | 14 | ✅ 是 | 09:26:02:37 |
| 91 | 13 | [`analysis/facts/model/task_arrivals.v`](files/analysis/facts/model/2026-09-26_025957_task_arrivals.md) | 23 | ✅ 是 | 09:26:02:59 |
| 92 | 13 | [`implementation/definitions/maximal_arrival_sequence.v`](files/implementation/definitions/2026-09-26_032005_maximal_arrival_sequence.md) | 7 | ✅ 是 | 09:26:03:19 |
| 93 | 13 | [`model/composite/valid_task_arrival_sequence.v`](files/model/composite/2026-09-26_033229_valid_task_arrival_sequence.md) | 6 | ✅ 是 | 09:26:03:32 |
| 94 | 13 | [`model/priority/classes.v`](files/model/priority/2026-09-26_120000_classes.md) | 0 | ✅ 是 | 09:26:03:39 |
| 95 | 13 | [`model/readiness/sequential.v`](files/model/readiness/2026-09-26_123000_sequential.md) | 0 | ✅ 是 | 09:26:03:58 |
| 96 | 13 | [`model/task/arrival/curve_as_rbf.v`](files/model/task/arrival/2026-09-26_140000_curve_as_rbf.md) | 12 | ✅ 是 | 09:26:04:19 |
| 97 | 14 | [`analysis/definitions/always_higher_priority.v`](files/analysis/definitions/2026-09-26_150000_always_higher_priority.md) | 2 | ✅ 是 | 09:26:04:22 |
| 98 | 14 | [`analysis/definitions/carry_in.v`](files/analysis/definitions/2026-09-26_153000_carry_in.md) | 1 | ✅ 是 | 09:26:04:40 |
| 99 | 14 | [`analysis/definitions/overheads/priority_bump.v`](files/analysis/definitions/overheads/2026-09-26_153500_priority_bump.md) | 1 | ✅ 是 | 09:26:04:41 |
| 100 | 14 | [`analysis/definitions/priority/classes.v`](files/analysis/definitions/priority/2026-09-26_154000_classes.md) | 1 | ✅ 是 | 09:26:04:41 |
| 101 | 14 | [`analysis/definitions/work_bearing_readiness.v`](files/analysis/definitions/2026-09-26_160000_work_bearing_readiness.md) | 1 | ✅ 是 | 09:26:04:51 |
| 102 | 14 | [`analysis/facts/behavior/service.v`](files/analysis/facts/behavior/2026-09-26_170000_service.md) | 57 | ✅ 是 | 09:26:05:17 |
| 103 | 14 | [`analysis/facts/delay_propagation.v`](files/analysis/facts/2026-09-26_190000_delay_propagation.md) | 12 | ✅ 是 | 09:26:05:43 |
| 104 | 14 | [`analysis/facts/job_index.v`](files/analysis/facts/2026-09-26_193000_job_index.md) | 21 | ✅ 是 | 09:26:05:44 |
| 105 | 14 | [`analysis/facts/model/arrival_curves.v`](files/analysis/facts/model/2026-09-26_200000_arrival_curves.md) | 3 | ✅ 是 | 09:26:05:53 |
| 106 | 14 | [`analysis/facts/model/sbf/average.v`](files/analysis/facts/model/sbf/2026-09-26_230000_average.md) | 3 | ✅ 是 | 09:26:06:29 |
| 107 | 14 | [`analysis/facts/model/sbf/periodic.v`](files/analysis/facts/model/sbf/2026-09-27_010000_periodic.md) | 9 | ✅ 是 | 09:26:07:00 |
| 108 | 14 | [`analysis/facts/sporadic/arrival_bound.v`](files/analysis/facts/sporadic/2026-09-27_030000_arrival_bound.md) | 4 | ✅ 是 | 09:26:07:13 |
| 109 | 14 | [`implementation/facts/maximal_arrival_sequence.v`](files/implementation/facts/2026-09-27_050000_maximal_arrival_sequence.md) | 14 | ✅ 是 | 09:26:07:30 |
| 110 | 14 | [`model/aggregate/service_of_jobs.v`](files/model/aggregate/2026-09-27_070000_service_of_jobs.md) | 8 | ✅ 是 | 09:26:07:49 |
| 111 | 14 | [`model/aggregate/workload.v`](files/model/aggregate/2026-09-27_080000_workload.md) | 8 | ✅ 是 | 09:26:07:57 |
| 112 | 14 | [`model/preemption/parameter.v`](files/model/preemption/2026-09-27_100000_parameter.md) | 14 | ✅ 是 | 09:26:08:35 |
| 113 | 14 | [`model/priority/deadline_monotonic.v`](files/model/priority/2026-09-27_103000_deadline_monotonic.md) | 4 | ✅ 是 | 09:26:08:35 |
| 114 | 14 | [`model/priority/edf.v`](files/model/priority/2026-09-27_103100_edf.md) | 4 | ✅ 是 | 09:26:08:35 |
| 115 | 14 | [`model/priority/fifo.v`](files/model/priority/2026-09-27_103200_fifo.md) | 4 | ✅ 是 | 09:26:08:35 |
| 116 | 14 | [`model/priority/gel.v`](files/model/priority/2026-09-27_120000_gel.md) | 7 | ✅ 是 | 09:26:09:06 |
| 117 | 14 | [`model/priority/numeric_fixed_priority.v`](files/model/priority/2026-09-27_130000_numeric_fixed_priority.md) | 7 | ✅ 是 | 09:26:09:13 |
| 118 | 14 | [`model/priority/rate_monotonic.v`](files/model/priority/2026-09-27_130100_rate_monotonic.md) | 4 | ✅ 是 | 09:26:09:13 |
| 119 | 15 | [`analysis/definitions/interference.v`](files/analysis/definitions/2026-09-27_140000_interference.md) | 15 | ✅ 是 | 09:26:09:14 |
| 120 | 15 | [`analysis/definitions/progress.v`](files/analysis/definitions/2026-09-27_150000_progress.md) | 4 | ✅ 是 | 09:26:09:28 |
| 121 | 15 | [`analysis/definitions/readiness.v`](files/analysis/definitions/2026-09-27_170000_readiness.md) | 3 | ✅ 是 | 09:26:09:48 |
| 122 | 15 | [`analysis/facts/behavior/completion.v`](files/analysis/facts/behavior/2026-09-27_180000_completion.md) | 30 | ✅ 是 | 09:26:10:09 |
| 123 | 15 | [`analysis/facts/model/ideal/schedule.v`](files/analysis/facts/model/ideal/2026-09-27_190000_schedule.md) | 19 | ✅ 是 | 09:26:11:39 |
| 124 | 15 | [`analysis/facts/model/ideal/service_of_jobs.v`](files/analysis/facts/model/ideal/2026-09-27_200000_service_of_jobs.md) | 2 | ✅ 是 | 09:26:12:55 |
| 125 | 15 | [`analysis/facts/model/task_schedule.v`](files/analysis/facts/model/2026-09-27_210000_task_schedule.md) | 10 | ✅ 是 | 09:26:13:26 |
| 126 | 15 | [`analysis/facts/model/workload.v`](files/analysis/facts/model/2026-09-27_220000_workload.md) | 17 | ✅ 是 | 09:26:13:51 |
| 127 | 15 | [`analysis/facts/priority/classes.v`](files/analysis/facts/priority/2026-09-27_230000_classes.md) | 22 | ✅ 是 | 09:26:14:07 |
| 128 | 15 | [`analysis/facts/sporadic/arrival_times.v`](files/analysis/facts/sporadic/2026-09-28_000000_arrival_times.md) | 3 | ✅ 是 | 09:26:14:21 |
| 129 | 15 | [`implementation/definitions/task.v`](files/implementation/definitions/2026-10-05_080000_task.md) | 15 | ✅ 是 | 09:29:20:52 |
| 130 | 15 | [`model/preemption/fully_nonpreemptive.v`](files/model/preemption/2026-09-28_010000_fully_nonpreemptive.md) | 0 | ✅ 是 | 09:26:14:28 |
| 131 | 15 | [`model/preemption/fully_preemptive.v`](files/model/preemption/2026-09-28_020000_fully_preemptive.md) | 0 | ✅ 是 | 09:26:14:30 |
| 132 | 15 | [`model/preemption/limited_preemptive.v`](files/model/preemption/2026-09-28_030000_limited_preemptive.md) | 5 | ✅ 是 | 09:26:15:02 |
| 133 | 15 | [`model/priority/elf.v`](files/model/priority/2026-09-28_040000_elf.md) | 1 | ✅ 是 | 09:26:15:03 |
| 134 | 15 | [`model/processor/multiprocessor.v`](files/model/processor/2026-10-05_180000_multiprocessor.md) | 6 | ✅ 是 | 09:30:08:23 |
| 135 | 15 | [`model/schedule/limited_preemptive.v`](files/model/schedule/2026-09-28_050000_limited_preemptive.md) | 1 | ✅ 是 | 09:26:15:16 |
| 136 | 15 | [`model/schedule/preemption_time.v`](files/model/schedule/2026-09-28_060000_preemption_time.md) | 1 | ✅ 是 | 09:26:15:29 |
| 137 | 15 | [`model/task/arrival/sporadic_as_curve.v`](files/model/task/arrival/2026-09-28_070000_sporadic_as_curve.md) | 5 | ✅ 是 | 09:26:15:47 |
| 138 | 15 | [`model/task/preemption/parameters.v`](files/model/task/preemption/2026-09-28_080000_parameters.md) | 13 | ✅ 是 | 09:26:15:47 |
| 139 | 16 | [`analysis/definitions/blocking_bound/edf.v`](files/analysis/definitions/blocking_bound/2026-09-28_090000_edf.md) | 2 | ✅ 是 | 09:26:16:19 |
| 140 | 16 | [`analysis/definitions/blocking_bound/elf.v`](files/analysis/definitions/blocking_bound/2026-10-02_120000_elf.md) | 1 | ✅ 是 | 09:28:06:33 |
| 141 | 16 | [`analysis/definitions/blocking_bound/fp.v`](files/analysis/definitions/blocking_bound/2026-09-28_100000_fp.md) | 1 | ✅ 是 | 09:26:16:34 |
| 142 | 16 | [`analysis/definitions/busy_interval/classical.v`](files/analysis/definitions/busy_interval/2026-09-28_110000_classical.md) | 5 | ✅ 是 | 09:26:16:36 |
| 143 | 16 | [`analysis/definitions/request_bound_function.v`](files/analysis/definitions/2026-09-28_120000_request_bound_function.md) | 6 | ✅ 是 | 09:26:16:51 |
| 144 | 16 | [`analysis/definitions/schedulability.v`](files/analysis/definitions/2026-09-28_130000_schedulability.md) | 6 | ✅ 是 | 09:26:17:09 |
| 145 | 16 | [`analysis/definitions/service_inversion/pred.v`](files/analysis/definitions/service_inversion/2026-09-28_140000_pred.md) | 4 | ✅ 是 | 09:26:17:27 |
| 146 | 16 | [`analysis/facts/behavior/deadlines.v`](files/analysis/facts/behavior/2026-09-28_150000_deadlines.md) | 4 | ✅ 是 | 09:26:17:39 |
| 147 | 16 | [`analysis/facts/preemption/job/preemptive.v`](files/analysis/facts/preemption/job/2026-09-28_160000_preemptive.md) | 3 | ✅ 是 | 09:26:17:56 |
| 148 | 16 | [`analysis/facts/priority/jlfp_with_fp.v`](files/analysis/facts/priority/2026-09-28_170000_jlfp_with_fp.md) | 8 | ✅ 是 | 09:26:18:02 |
| 149 | 16 | [`analysis/facts/readiness/backlogged.v`](files/analysis/facts/readiness/2026-09-28_230000_backlogged.md) | 5 | ✅ 是 | 09:26:19:05 |
| 150 | 16 | [`analysis/facts/readiness/basic.v`](files/analysis/facts/readiness/2026-09-29_000000_basic.md) | 3 | ✅ 是 | 09:26:19:14 |
| 151 | 16 | [`analysis/facts/readiness/sequential.v`](files/analysis/facts/readiness/2026-09-29_010000_sequential.md) | 4 | ✅ 是 | 09:26:19:39 |
| 152 | 16 | [`analysis/facts/sporadic/arrival_sequence.v`](files/analysis/facts/sporadic/2026-09-29_020000_arrival_sequence.md) | 7 | ✅ 是 | 09:26:19:53 |
| 153 | 16 | [`analysis/facts/transform/replace_at.v`](files/analysis/facts/transform/2026-09-29_030000_replace_at.md) | 7 | ✅ 是 | 09:26:20:18 |
| 154 | 16 | [`implementation/definitions/job_constructor.v`](files/implementation/definitions/2026-10-05_090000_job_constructor.md) | 4 | ✅ 是 | 09:29:21:01 |
| 155 | 16 | [`model/readiness/suspension.v`](files/model/readiness/2026-10-05_060000_suspension.md) | 4 | ✅ 是 | 09:29:20:14 |
| 156 | 16 | [`model/schedule/priority_driven.v`](files/model/schedule/2026-09-28_220000_priority_driven.md) | 3 | ✅ 是 | 09:26:19:00 |
| 157 | 16 | [`model/task/preemption/floating_nonpreemptive.v`](files/model/task/preemption/2026-09-28_210000_floating_nonpreemptive.md) | 2 | ✅ 是 | 09:26:18:46 |
| 158 | 16 | [`model/task/preemption/fully_nonpreemptive.v`](files/model/task/preemption/2026-09-28_180000_fully_nonpreemptive.md) | 1 | ✅ 是 | 09:26:18:20 |
| 159 | 16 | [`model/task/preemption/fully_preemptive.v`](files/model/task/preemption/2026-09-28_190000_fully_preemptive.md) | 1 | ✅ 是 | 09:26:18:21 |
| 160 | 16 | [`model/task/preemption/limited_preemptive.v`](files/model/task/preemption/2026-09-28_200000_limited_preemptive.md) | 8 | ✅ 是 | 09:26:18:33 |
| 161 | 17 | [`analysis/abstract/restricted_supply/busy_prefix.v`](files/analysis/abstract/restricted_supply/2026-09-30_220000_busy_prefix.md) | 2 | ✅ 是 | 09:27:07:55 |
| 162 | 17 | [`analysis/definitions/busy_interval/edf_pi_bound.v`](files/analysis/definitions/busy_interval/2026-09-29_110000_edf_pi_bound.md) | 1 | ✅ 是 | 09:26:22:03 |
| 163 | 17 | [`analysis/definitions/demand_bound_function.v`](files/analysis/definitions/2026-09-29_040000_demand_bound_function.md) | 2 | ✅ 是 | 09:26:20:27 |
| 164 | 17 | [`analysis/definitions/priority_inversion.v`](files/analysis/definitions/2026-09-29_060000_priority_inversion.md) | 8 | ✅ 是 | 09:26:20:58 |
| 165 | 17 | [`analysis/definitions/sbf/busy.v`](files/analysis/definitions/sbf/2026-09-30_210000_busy.md) | 2 | ✅ 是 | 09:27:07:36 |
| 166 | 17 | [`analysis/definitions/service_inversion/busy_prefix.v`](files/analysis/definitions/service_inversion/2026-09-29_100000_busy_prefix.md) | 2 | ✅ 是 | 09:26:21:40 |
| 167 | 17 | [`analysis/definitions/service_inversion/readiness_aware.v`](files/analysis/definitions/service_inversion/2026-10-05_140000_readiness_aware.md) | 3 | ✅ 是 | 09:29:23:30 |
| 168 | 17 | [`analysis/definitions/tardiness.v`](files/analysis/definitions/2026-09-29_050000_tardiness.md) | 1 | ✅ 是 | 09:26:20:57 |
| 169 | 17 | [`analysis/definitions/workload/bounded.v`](files/analysis/definitions/workload/2026-09-29_090000_bounded.md) | 1 | ✅ 是 | 09:26:21:24 |
| 170 | 17 | [`analysis/definitions/workload/edf_athep_bound.v`](files/analysis/definitions/workload/2026-09-29_080000_edf_athep_bound.md) | 1 | ✅ 是 | 09:26:21:22 |
| 171 | 17 | [`analysis/definitions/workload/elf_athep_bound.v`](files/analysis/definitions/workload/2026-10-02_140000_elf_athep_bound.md) | 4 | ✅ 是 | 09:28:07:54 |
| 172 | 17 | [`analysis/facts/behavior/all.v`](files/analysis/facts/behavior/2026-09-29_070000_all.md) | 0 | ✅ 是 | 09:26:21:14 |
| 173 | 17 | [`analysis/facts/busy_interval/quiet_time.v`](files/analysis/facts/busy_interval/2026-09-29_130000_quiet_time.md) | 4 | ✅ 是 | 09:26:22:06 |
| 174 | 17 | [`analysis/facts/edf_definitions.v`](files/analysis/facts/2026-09-30_200000_edf_definitions.md) | 3 | ✅ 是 | 09:27:07:07 |
| 175 | 17 | [`analysis/facts/jitter.v`](files/analysis/facts/2026-10-02_070000_jitter.md) | 14 | ✅ 是 | 09:28:04:12 |
| 176 | 17 | [`analysis/facts/model/preemption.v`](files/analysis/facts/model/2026-10-01_060000_preemption.md) | 14 | ✅ 是 | 09:27:12:19 |
| 177 | 17 | [`analysis/facts/preemption/task/preemptive.v`](files/analysis/facts/preemption/task/2026-09-29_120000_preemptive.md) | 2 | ✅ 是 | 09:26:22:04 |
| 178 | 17 | [`analysis/facts/suspension.v`](files/analysis/facts/2026-10-05_120000_suspension.md) | 11 | ✅ 是 | 09:29:22:45 |
| 179 | 17 | [`analysis/facts/transform/swaps.v`](files/analysis/facts/transform/2026-09-30_040000_swaps.md) | 22 | ✅ 是 | 09:27:01:35 |
| 180 | 17 | [`implementation/definitions/ideal_uni_scheduler.v`](files/implementation/definitions/2026-09-30_160000_ideal_uni_scheduler.md) | 5 | ✅ 是 | 09:27:05:23 |
| 181 | 17 | [`implementation/facts/generic_schedule.v`](files/implementation/facts/2026-09-30_150000_generic_schedule.md) | 6 | ✅ 是 | 09:27:04:56 |
| 183 | 17 | [`model/task/suspension/dynamic.v`](files/model/task/suspension/2026-10-05_070000_dynamic.md) | 2 | ✅ 是 | 09:29:20:21 |
| 184 | 18 | [`analysis/facts/completes_at.v`](files/analysis/facts/2026-10-01_080000_completes_at.md) | 5 | ✅ 是 | 09:27:13:04 |
| 185 | 18 | [`analysis/facts/model/dynamic_suspension.v`](files/analysis/facts/model/2026-10-05_130000_dynamic_suspension.md) | 2 | ✅ 是 | 09:29:23:10 |
| 186 | 18 | [`analysis/facts/model/exceedance/SBF.v`](files/analysis/facts/model/exceedance/2026-10-05_040000_SBF.md) | 4 | ✅ 是 | 09:29:18:34 |
| 187 | 18 | [`analysis/facts/model/rbf.v`](files/analysis/facts/model/2026-09-30_030000_rbf.md) | 27 | ✅ 是 | 09:27:01:34 |
| 188 | 18 | [`analysis/facts/model/sequential.v`](files/analysis/facts/model/2026-10-01_200000_sequential.md) | 3 | ✅ 是 | 09:27:21:34 |
| 189 | 18 | [`analysis/facts/model/service_of_jobs.v`](files/analysis/facts/model/2026-09-29_230000_service_of_jobs.md) | 22 | ✅ 是 | 09:27:00:28 |
| 190 | 18 | [`analysis/facts/preemption/job/nonpreemptive.v`](files/analysis/facts/preemption/job/2026-09-29_140000_nonpreemptive.md) | 4 | ✅ 是 | 09:26:22:23 |
| 191 | 18 | [`analysis/facts/preemption/rtc_threshold/job_preemptable.v`](files/analysis/facts/preemption/rtc_threshold/2026-09-29_180000_job_preemptable.md) | 14 | ✅ 是 | 09:26:23:41 |
| 192 | 18 | [`analysis/facts/priority/inversion.v`](files/analysis/facts/priority/2026-09-29_170000_inversion.md) | 7 | ✅ 是 | 09:26:22:53 |
| 193 | 18 | [`analysis/facts/priority/sequential.v`](files/analysis/facts/priority/2026-10-01_070000_sequential.md) | 1 | ✅ 是 | 09:27:12:41 |
| 194 | 18 | [`analysis/transform/prefix.v`](files/analysis/transform/2026-09-29_160000_prefix.md) | 3 | ✅ 是 | 09:26:22:38 |
| 195 | 18 | [`implementation/facts/ideal_uni/preemption_aware.v`](files/implementation/facts/ideal_uni/2026-09-30_170000_preemption_aware.md) | 10 | ✅ 是 | 09:27:05:59 |
| 196 | 18 | [`model/task/offset.v`](files/model/task/2026-09-29_150000_offset.md) | 7 | ✅ 是 | 09:26:22:36 |
| 197 | 19 | [`analysis/abstract/iw_auxiliary.v`](files/analysis/abstract/2026-09-30_230000_iw_auxiliary.md) | 6 | ✅ 是 | 09:27:08:10 |
| 198 | 19 | [`analysis/abstract/restricted_supply/search_space/fp.v`](files/analysis/abstract/restricted_supply/search_space/2026-09-30_060000_fp.md) | 2 | ✅ 是 | 09:27:02:22 |
| 199 | 19 | [`analysis/facts/busy_interval/existence.v`](files/analysis/facts/busy_interval/2026-10-01_090000_existence.md) | 14 | ✅ 是 | 09:27:16:51 |
| 200 | 19 | [`analysis/facts/interference.v`](files/analysis/facts/2026-09-30_020000_interference.md) | 17 | ✅ 是 | 09:27:01:30 |
| 201 | 19 | [`analysis/facts/model/dbf.v`](files/analysis/facts/model/2026-09-30_120000_dbf.md) | 8 | ✅ 是 | 09:27:03:57 |
| 202 | 19 | [`analysis/facts/model/ideal/priority_inversion.v`](files/analysis/facts/model/ideal/2026-09-30_190000_priority_inversion.md) | 4 | ✅ 是 | 09:27:06:34 |
| 203 | 19 | [`analysis/facts/model/offset.v`](files/analysis/facts/model/2026-09-29_210000_offset.md) | 2 | ✅ 是 | 09:27:00:18 |
| 204 | 19 | [`analysis/facts/preemption/job/limited.v`](files/analysis/facts/preemption/job/2026-10-01_210000_limited.md) | 10 | ✅ 是 | 09:27:21:58 |
| 205 | 19 | [`analysis/facts/preemption/rtc_threshold/nonpreemptive.v`](files/analysis/facts/preemption/rtc_threshold/2026-09-29_200000_nonpreemptive.md) | 3 | ✅ 是 | 09:27:00:17 |
| 206 | 19 | [`analysis/facts/preemption/rtc_threshold/preemptive.v`](files/analysis/facts/preemption/rtc_threshold/2026-09-30_000000_preemptive.md) | 1 | ✅ 是 | 09:27:00:30 |
| 207 | 19 | [`analysis/facts/preemption/task/nonpreemptive.v`](files/analysis/facts/preemption/task/2026-09-29_190000_nonpreemptive.md) | 2 | ✅ 是 | 09:26:23:43 |
| 208 | 19 | [`analysis/facts/priority/edf.v`](files/analysis/facts/priority/2026-10-01_220000_edf.md) | 5 | ✅ 是 | 09:27:22:03 |
| 209 | 19 | [`analysis/facts/priority/gel.v`](files/analysis/facts/priority/2026-10-02_080000_gel.md) | 6 | ✅ 是 | 09:28:04:39 |
| 210 | 19 | [`analysis/facts/workload/edf_athep_bound.v`](files/analysis/facts/workload/2026-09-30_050000_edf_athep_bound.md) | 4 | ✅ 是 | 09:27:02:02 |
| 211 | 19 | [`analysis/facts/workload/elf_athep_bound.v`](files/analysis/facts/workload/2026-10-02_150000_elf_athep_bound.md) | 6 | ✅ 是 | 09:28:09:17 |
| 212 | 19 | [`analysis/transform/edf_trans.v`](files/analysis/transform/2026-09-30_130000_edf_trans.md) | 6 | ✅ 是 | 09:27:04:21 |
| 213 | 19 | [`analysis/transform/wc_trans.v`](files/analysis/transform/2026-09-30_140000_wc_trans.md) | 6 | ✅ 是 | 09:27:04:40 |
| 214 | 19 | [`implementation/facts/ideal_uni/prio_aware.v`](files/implementation/facts/ideal_uni/2026-09-30_180000_prio_aware.md) | 5 | ✅ 是 | 09:27:06:18 |
| 215 | 19 | [`model/task/arrival/periodic.v`](files/model/task/arrival/2026-09-29_220000_periodic.md) | 5 | ✅ 是 | 09:27:00:19 |
| 216 | 19 | [`results/transfer_schedulability/criterion.v`](files/results/transfer_schedulability/2026-10-02_020000_criterion.md) | 40 | ✅ 是 | 09:28:00:38 |
| 217 | 20 | [`analysis/abstract/busy_interval.v`](files/analysis/abstract/2026-10-01_000000_busy_interval.md) | 15 | ✅ 是 | 09:27:09:08 |
| 218 | 20 | [`analysis/abstract/restricted_supply/search_space/edf.v`](files/analysis/abstract/restricted_supply/search_space/2026-09-30_080000_edf.md) | 2 | ✅ 是 | 09:27:02:53 |
| 219 | 20 | [`analysis/abstract/restricted_supply/search_space/elf.v`](files/analysis/abstract/restricted_supply/search_space/2026-10-02_180000_elf.md) | 2 | ✅ 是 | 09:28:15:23 |
| 220 | 20 | [`analysis/definitions/hyperperiod.v`](files/analysis/definitions/2026-10-05_110000_hyperperiod.md) | 7 | ✅ 是 | 09:29:22:11 |
| 221 | 20 | [`analysis/facts/busy_interval/carry_in.v`](files/analysis/facts/busy_interval/2026-10-01_110000_carry_in.md) | 9 | ✅ 是 | 09:27:18:09 |
| 222 | 20 | [`analysis/facts/busy_interval/hep_at_pt.v`](files/analysis/facts/busy_interval/2026-10-01_100000_hep_at_pt.md) | 8 | ✅ 是 | 09:27:17:40 |
| 223 | 20 | [`analysis/facts/preemption/task/floating.v`](files/analysis/facts/preemption/task/2026-10-01_233000_floating.md) | 2 | ✅ 是 | 09:27:22:35 |
| 224 | 20 | [`analysis/facts/preemption/task/limited.v`](files/analysis/facts/preemption/task/2026-10-01_230000_limited.md) | 2 | ✅ 是 | 09:27:22:33 |
| 225 | 20 | [`analysis/facts/priority/elf.v`](files/analysis/facts/priority/2026-10-02_090000_elf.md) | 8 | ✅ 是 | 09:28:05:11 |
| 226 | 20 | [`analysis/facts/readiness_interference.v`](files/analysis/facts/2026-10-05_150000_readiness_interference.md) | 2 | ✅ 是 | 09:29:23:44 |
| 227 | 20 | [`analysis/facts/transform/edf_opt.v`](files/analysis/facts/transform/2026-10-05_230000_edf_opt.md) | 43 | ✅ 是 | 09:30:10:36 |
| 228 | 20 | [`analysis/facts/transform/wc_correctness.v`](files/analysis/facts/transform/2026-10-06_000000_wc_correctness.md) | 33 | ✅ 是 | 09:30:11:06 |
| 229 | 20 | [`model/task/arrival/periodic_as_sporadic.v`](files/model/task/arrival/2026-09-30_010000_periodic_as_sporadic.md) | 5 | ✅ 是 | 09:27:00:56 |
| 231 | 21 | [`analysis/abstract/lower_bound_on_service.v`](files/analysis/abstract/2026-10-01_010000_lower_bound_on_service.md) | 3 | ✅ 是 | 09:27:09:32 |
| 232 | 21 | [`analysis/facts/busy_interval/arrival.v`](files/analysis/facts/busy_interval/2026-10-01_120000_arrival.md) | 3 | ✅ 是 | 09:27:18:56 |
| 233 | 21 | [`analysis/facts/busy_interval/pi.v`](files/analysis/facts/busy_interval/2026-10-01_130000_pi.md) | 24 | ✅ 是 | 09:27:19:16 |
| 234 | 21 | [`analysis/facts/periodic/arrival_separation.v`](files/analysis/facts/periodic/2026-09-30_070000_arrival_separation.md) | 3 | ✅ 是 | 09:27:02:30 |
| 235 | 21 | [`analysis/facts/preemption/rtc_threshold/floating.v`](files/analysis/facts/preemption/rtc_threshold/2026-10-02_003000_floating.md) | 1 | ✅ 是 | 09:27:23:17 |
| 236 | 21 | [`analysis/facts/preemption/rtc_threshold/limited.v`](files/analysis/facts/preemption/rtc_threshold/2026-10-02_000000_limited.md) | 3 | ✅ 是 | 09:27:23:16 |
| 237 | 21 | [`analysis/facts/transform/edf_wc.v`](files/analysis/facts/transform/2026-10-06_010000_edf_wc.md) | 11 | ✅ 是 | 09:30:11:34 |
| 239 | 21 | [`results/generality/elf.v`](files/results/generality/2026-10-02_100000_elf.md) | 3 | ✅ 是 | 09:28:05:36 |
| 240 | 22 | [`analysis/abstract/abstract_rta.v`](files/analysis/abstract/2026-10-01_020000_abstract_rta.md) | 14 | ✅ 是 | 09:27:10:04 |
| 241 | 22 | [`analysis/facts/blocking_bound/edf.v`](files/analysis/facts/blocking_bound/2026-10-01_180000_edf.md) | 1 | ✅ 是 | 09:27:20:31 |
| 242 | 22 | [`analysis/facts/blocking_bound/elf.v`](files/analysis/facts/blocking_bound/2026-10-02_130000_elf.md) | 1 | ✅ 是 | 09:28:07:44 |
| 243 | 22 | [`analysis/facts/blocking_bound/fp.v`](files/analysis/facts/blocking_bound/2026-10-01_160000_fp.md) | 1 | ✅ 是 | 09:27:20:00 |
| 244 | 22 | [`analysis/facts/busy_interval/pi_bound.v`](files/analysis/facts/busy_interval/2026-10-01_150000_pi_bound.md) | 1 | ✅ 是 | 09:27:19:56 |
| 245 | 22 | [`analysis/facts/busy_interval/pi_cond.v`](files/analysis/facts/busy_interval/2026-10-01_140000_pi_cond.md) | 1 | ✅ 是 | 09:27:19:51 |
| 246 | 22 | [`analysis/facts/busy_interval/service_inversion.v`](files/analysis/facts/busy_interval/2026-10-01_190000_service_inversion.md) | 12 | ✅ 是 | 09:27:21:32 |
| 247 | 22 | [`analysis/facts/model/overheads/schedule.v`](files/analysis/facts/model/overheads/2026-10-04_100000_schedule.md) | 6 | ✅ 是 | 09:29:03:49 |
| 248 | 22 | [`analysis/facts/periodic/max_inter_arrival.v`](files/analysis/facts/periodic/2026-09-30_090000_max_inter_arrival.md) | 3 | ✅ 是 | 09:27:03:05 |
| 249 | 22 | [`results/optimality/edf.v`](files/results/optimality/2026-10-06_020000_edf.md) | 4 | ✅ 是 | 09:30:11:51 |
| 250 | 23 | [`analysis/abstract/IBF/supply.v`](files/analysis/abstract/IBF/2026-10-01_030000_supply.md) | 3 | ✅ 是 | 09:27:10:24 |
| 251 | 23 | [`analysis/abstract/IBF/task.v`](files/analysis/abstract/IBF/2026-10-02_010000_task.md) | 18 | ✅ 是 | 09:27:23:55 |
| 252 | 23 | [`analysis/abstract/ideal/abstract_rta.v`](files/analysis/abstract/ideal/2026-10-01_040000_abstract_rta.md) | 2 | ✅ 是 | 09:27:10:51 |
| 253 | 23 | [`analysis/facts/busy_interval/all.v`](files/analysis/facts/busy_interval/2026-10-01_170000_all.md) | 0 | ✅ 是 | 09:27:20:16 |
| 254 | 23 | [`analysis/facts/model/overheads/priority_bump.v`](files/analysis/facts/model/overheads/2026-10-04_130000_priority_bump.md) | 3 | ✅ 是 | 09:29:08:53 |
| 255 | 23 | [`analysis/facts/model/overheads/schedule_change.v`](files/analysis/facts/model/overheads/2026-10-04_110000_schedule_change.md) | 6 | ✅ 是 | 09:29:04:33 |
| 256 | 23 | [`analysis/facts/periodic/arrival_times.v`](files/analysis/facts/periodic/2026-09-30_100000_arrival_times.md) | 3 | ✅ 是 | 09:27:03:19 |
| 257 | 24 | [`analysis/abstract/IBF/supply_task.v`](files/analysis/abstract/IBF/2026-10-02_030000_supply_task.md) | 3 | ✅ 是 | 09:28:01:23 |
| 258 | 24 | [`analysis/abstract/ideal/abstract_seq_rta.v`](files/analysis/abstract/ideal/2026-10-02_040000_abstract_seq_rta.md) | 2 | ✅ 是 | 09:28:01:30 |
| 259 | 24 | [`analysis/abstract/ideal/iw_instantiation.v`](files/analysis/abstract/ideal/2026-10-06_030000_iw_instantiation.md) | 20 | ✅ 是 | 09:30:12:16 |
| 260 | 24 | [`analysis/abstract/restricted_supply/abstract_rta.v`](files/analysis/abstract/restricted_supply/2026-10-01_050000_abstract_rta.md) | 10 | ✅ 是 | 09:27:11:28 |
| 261 | 24 | [`analysis/facts/model/overheads/schedule_change_bound.v`](files/analysis/facts/model/overheads/2026-10-04_150000_schedule_change_bound.md) | 3 | ✅ 是 | 09:29:11:08 |
| 262 | 24 | [`analysis/facts/periodic/task_arrivals_size.v`](files/analysis/facts/periodic/2026-09-30_110000_task_arrivals_size.md) | 8 | ✅ 是 | 09:27:03:36 |
| 263 | 24 | [`analysis/facts/priority/fifo.v`](files/analysis/facts/priority/2026-10-02_110000_fifo.md) | 12 | ✅ 是 | 09:28:06:13 |
| 264 | 24 | [`model/processor/overhead_resource_model.v`](files/model/processor/2026-10-04_120000_overhead_resource_model.md) | 10 | ✅ 是 | 09:29:08:06 |
| 265 | 25 | [`analysis/abstract/ideal/cumulative_bounds.v`](files/analysis/abstract/ideal/2026-10-06_040000_cumulative_bounds.md) | 2 | ✅ 是 | 09:30:12:39 |
| 266 | 25 | [`analysis/abstract/restricted_supply/abstract_seq_rta.v`](files/analysis/abstract/restricted_supply/2026-10-02_050000_abstract_seq_rta.md) | 3 | ✅ 是 | 09:28:02:25 |
| 267 | 25 | [`analysis/abstract/restricted_supply/iw_instantiation.v`](files/analysis/abstract/restricted_supply/2026-10-02_060000_iw_instantiation.md) | 17 | ✅ 是 | 09:28:03:44 |
| 268 | 25 | [`analysis/abstract/restricted_supply/iw_readiness.v`](files/analysis/abstract/restricted_supply/2026-10-05_210000_iw_readiness.md) | 18 | ✅ 是 | 09:30:09:25 |
| 269 | 25 | [`analysis/abstract/restricted_supply/search_space/fifo.v`](files/analysis/abstract/restricted_supply/search_space/2026-10-02_190000_fifo.md) | 2 | ✅ 是 | 09:28:17:22 |
| 270 | 25 | [`analysis/facts/hyperperiod.v`](files/analysis/facts/2026-10-05_190000_hyperperiod.md) | 10 | ✅ 是 | 09:30:08:43 |
| 271 | 25 | [`analysis/facts/model/overheads/blackout_bound.v`](files/analysis/facts/model/overheads/2026-10-04_140000_blackout_bound.md) | 11 | ✅ 是 | 09:29:09:34 |
| 272 | 25 | [`analysis/facts/priority/fifo_ahep_bound.v`](files/analysis/facts/priority/2026-10-02_220000_fifo_ahep_bound.md) | 1 | ✅ 是 | 09:28:19:18 |
| 273 | 25 | [`results/generality/gel.v`](files/results/generality/2026-10-02_210000_gel.md) | 5 | ✅ 是 | 09:28:18:56 |
| 274 | 25 | [`results/rta/ideal/fp/bounded_pi.v`](files/results/rta/ideal/fp/2026-10-06_050000_bounded_pi.md) | 6 | ✅ 是 | 09:30:13:25 |
| 275 | 26 | [`analysis/abstract/restricted_supply/bounded_bi/aux.v`](files/analysis/abstract/restricted_supply/bounded_bi/2026-10-02_160000_aux.md) | 3 | ✅ 是 | 09:28:11:51 |
| 276 | 26 | [`analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v`](files/analysis/abstract/restricted_supply/search_space/2026-10-03_000000_fifo_fixpoint.md) | 1 | ✅ 是 | 09:28:20:44 |
| 277 | 26 | [`analysis/abstract/restricted_supply/task_ibf_readiness.v`](files/analysis/abstract/restricted_supply/2026-10-05_220000_task_ibf_readiness.md) | 2 | ✅ 是 | 09:30:09:49 |
| 278 | 26 | [`analysis/abstract/restricted_supply/task_intra_interference_bound.v`](files/analysis/abstract/restricted_supply/2026-10-02_170000_task_intra_interference_bound.md) | 2 | ✅ 是 | 09:28:13:49 |
| 279 | 26 | [`analysis/facts/model/overheads/sbf/fifo.v`](files/analysis/facts/model/overheads/sbf/2026-10-04_160000_fifo.md) | 6 | ✅ 是 | 09:29:12:12 |
| 280 | 26 | [`analysis/facts/model/overheads/sbf/fp.v`](files/analysis/facts/model/overheads/sbf/2026-10-04_170000_fp.md) | 6 | ✅ 是 | 09:29:12:40 |
| 281 | 26 | [`analysis/facts/model/overheads/sbf/jlfp.v`](files/analysis/facts/model/overheads/sbf/2026-10-04_180000_jlfp.md) | 6 | ✅ 是 | 09:29:13:11 |
| 282 | 26 | [`analysis/facts/shifted_job_costs.v`](files/analysis/facts/2026-10-05_200000_shifted_job_costs.md) | 3 | ✅ 是 | 09:30:08:55 |
| 286 | 26 | [`results/rta/ideal/fp/bounded_nps.v`](files/results/rta/ideal/fp/2026-10-06_060000_bounded_nps.md) | 3 | ✅ 是 | 09:30:14:51 |
| 289 | 27 | [`analysis/abstract/restricted_supply/bounded_bi/edf.v`](files/analysis/abstract/restricted_supply/bounded_bi/2026-10-03_010000_edf.md) | 2 | ✅ 是 | 09:28:22:39 |
| 290 | 27 | [`analysis/abstract/restricted_supply/bounded_bi/elf.v`](files/analysis/abstract/restricted_supply/bounded_bi/2026-10-03_020000_elf.md) | 1 | ✅ 是 | 09:28:22:49 |
| 291 | 27 | [`analysis/abstract/restricted_supply/bounded_bi/fp.v`](files/analysis/abstract/restricted_supply/bounded_bi/2026-10-02_230000_fp.md) | 1 | ✅ 是 | 09:28:20:30 |
| 292 | 27 | [`analysis/abstract/restricted_supply/bounded_bi/jlfp.v`](files/analysis/abstract/restricted_supply/bounded_bi/2026-10-02_200000_jlfp.md) | 1 | ✅ 是 | 09:28:18:17 |
| 294 | 27 | <a id="latest-completed"></a>[`results/rta/ideal/fp/floating_nonpreemptive.v`](files/results/rta/ideal/fp/2026-10-06_090000_floating_nonpreemptive.md) | 1 | ✅ 是 | 09:30:17:00 |
| 295 | 27 | [`results/rta/ideal/fp/fully_nonpreemptive.v`](files/results/rta/ideal/fp/2026-10-06_080000_fully_nonpreemptive.md) | 1 | ✅ 是 | 09:30:16:12 |
| 296 | 27 | [`results/rta/ideal/fp/fully_preemptive.v`](files/results/rta/ideal/fp/2026-10-06_070000_fully_preemptive.md) | 1 | ✅ 是 | 09:30:15:29 |
| 298 | 28 | [`results/rta/arm/edf/floating_nonpreemptive.v`](files/results/rta/arm/edf/2026-10-03_230000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:29:02:09 |
| 299 | 28 | [`results/rta/arm/edf/fully_nonpreemptive.v`](files/results/rta/arm/edf/2026-10-03_210000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:29:01:55 |
| 300 | 28 | [`results/rta/arm/edf/fully_preemptive.v`](files/results/rta/arm/edf/2026-10-03_200000_fully_preemptive.md) | 3 | ✅ 是 | 09:29:01:50 |
| 301 | 28 | [`results/rta/arm/edf/limited_preemptive.v`](files/results/rta/arm/edf/2026-10-03_220000_limited_preemptive.md) | 3 | ✅ 是 | 09:29:02:02 |
| 302 | 28 | [`results/rta/arm/fifo/bounded_nps.v`](files/results/rta/arm/fifo/2026-10-04_000000_bounded_nps.md) | 3 | ✅ 是 | 09:29:02:17 |
| 303 | 28 | [`results/rta/arm/fp/floating_nonpreemptive.v`](files/results/rta/arm/fp/2026-10-03_190000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:29:01:44 |
| 304 | 28 | [`results/rta/arm/fp/fully_nonpreemptive.v`](files/results/rta/arm/fp/2026-10-03_170000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:29:01:31 |
| 305 | 28 | [`results/rta/arm/fp/fully_preemptive.v`](files/results/rta/arm/fp/2026-10-03_120000_fully_preemptive.md) | 3 | ✅ 是 | 09:29:00:34 |
| 306 | 28 | [`results/rta/arm/fp/limited_preemptive.v`](files/results/rta/arm/fp/2026-10-03_180000_limited_preemptive.md) | 3 | ✅ 是 | 09:29:01:37 |
| 307 | 28 | [`results/rta/exc/fp/fully_nonpreemptive.v`](files/results/rta/exc/fp/2026-10-05_050000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:29:19:46 |
| 313 | 28 | [`results/rta/ovh/edf/floating_nonpreemptive.v`](files/results/rta/ovh/edf/2026-10-05_010000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:29:16:31 |
| 314 | 28 | [`results/rta/ovh/edf/fully_nonpreemptive.v`](files/results/rta/ovh/edf/2026-10-04_220000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:29:15:27 |
| 315 | 28 | [`results/rta/ovh/edf/fully_preemptive.v`](files/results/rta/ovh/edf/2026-10-04_200000_fully_preemptive.md) | 3 | ✅ 是 | 09:29:14:47 |
| 316 | 28 | [`results/rta/ovh/edf/limited_preemptive.v`](files/results/rta/ovh/edf/2026-10-05_000000_limited_preemptive.md) | 3 | ✅ 是 | 09:29:16:17 |
| 317 | 28 | [`results/rta/ovh/fifo/bounded_nps.v`](files/results/rta/ovh/fifo/2026-10-04_190000_bounded_nps.md) | 3 | ✅ 是 | 09:29:13:43 |
| 318 | 28 | [`results/rta/ovh/fp/floating_nonpreemptive.v`](files/results/rta/ovh/fp/2026-10-05_030000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:29:16:59 |
| 319 | 28 | [`results/rta/ovh/fp/fully_nonpreemptive.v`](files/results/rta/ovh/fp/2026-10-04_230000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:29:15:46 |
| 320 | 28 | [`results/rta/ovh/fp/fully_preemptive.v`](files/results/rta/ovh/fp/2026-10-04_210000_fully_preemptive.md) | 3 | ✅ 是 | 09:29:15:06 |
| 321 | 28 | [`results/rta/ovh/fp/limited_preemptive.v`](files/results/rta/ovh/fp/2026-10-05_020000_limited_preemptive.md) | 3 | ✅ 是 | 09:29:16:44 |
| 322 | 28 | [`results/rta/prm/edf/floating_nonpreemptive.v`](files/results/rta/prm/edf/2026-10-04_080000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:29:03:11 |
| 323 | 28 | [`results/rta/prm/edf/fully_nonpreemptive.v`](files/results/rta/prm/edf/2026-10-04_060000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:29:02:58 |
| 324 | 28 | [`results/rta/prm/edf/fully_preemptive.v`](files/results/rta/prm/edf/2026-10-04_050000_fully_preemptive.md) | 3 | ✅ 是 | 09:29:02:52 |
| 325 | 28 | [`results/rta/prm/edf/limited_preemptive.v`](files/results/rta/prm/edf/2026-10-04_070000_limited_preemptive.md) | 3 | ✅ 是 | 09:29:03:05 |
| 326 | 28 | [`results/rta/prm/fifo/bounded_nps.v`](files/results/rta/prm/fifo/2026-10-04_090000_bounded_nps.md) | 3 | ✅ 是 | 09:29:03:16 |
| 327 | 28 | [`results/rta/prm/fp/floating_nonpreemptive.v`](files/results/rta/prm/fp/2026-10-04_040000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:29:02:46 |
| 328 | 28 | [`results/rta/prm/fp/fully_nonpreemptive.v`](files/results/rta/prm/fp/2026-10-04_020000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:29:02:32 |
| 329 | 28 | [`results/rta/prm/fp/fully_preemptive.v`](files/results/rta/prm/fp/2026-10-04_010000_fully_preemptive.md) | 3 | ✅ 是 | 09:29:02:24 |
| 330 | 28 | [`results/rta/prm/fp/limited_preemptive.v`](files/results/rta/prm/fp/2026-10-04_030000_limited_preemptive.md) | 3 | ✅ 是 | 09:29:02:39 |
| 331 | 28 | [`results/rta/rs/edf/floating_nonpreemptive.v`](files/results/rta/rs/edf/2026-10-03_100000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:29:00:13 |
| 332 | 28 | [`results/rta/rs/edf/fully_nonpreemptive.v`](files/results/rta/rs/edf/2026-10-03_080000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:28:23:57 |
| 333 | 28 | [`results/rta/rs/edf/fully_preemptive.v`](files/results/rta/rs/edf/2026-10-03_070000_fully_preemptive.md) | 3 | ✅ 是 | 09:28:23:51 |
| 334 | 28 | [`results/rta/rs/edf/limited_preemptive.v`](files/results/rta/rs/edf/2026-10-03_090000_limited_preemptive.md) | 3 | ✅ 是 | 09:29:00:05 |
| 335 | 28 | [`results/rta/rs/elf/floating_nonpreemptive.v`](files/results/rta/rs/elf/2026-10-03_160000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:29:01:22 |
| 336 | 28 | [`results/rta/rs/elf/fully_nonpreemptive.v`](files/results/rta/rs/elf/2026-10-03_140000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:29:01:04 |
| 337 | 28 | [`results/rta/rs/elf/fully_preemptive.v`](files/results/rta/rs/elf/2026-10-03_130000_fully_preemptive.md) | 3 | ✅ 是 | 09:29:00:55 |
| 338 | 28 | [`results/rta/rs/elf/limited_preemptive.v`](files/results/rta/rs/elf/2026-10-03_150000_limited_preemptive.md) | 3 | ✅ 是 | 09:29:01:13 |
| 339 | 28 | [`results/rta/rs/fifo/bounded_nps.v`](files/results/rta/rs/fifo/2026-10-03_110000_bounded_nps.md) | 3 | ✅ 是 | 09:29:00:23 |
| 340 | 28 | [`results/rta/rs/fp/floating_nonpreemptive.v`](files/results/rta/rs/fp/2026-10-03_060000_floating_nonpreemptive.md) | 3 | ✅ 是 | 09:28:23:39 |
| 341 | 28 | [`results/rta/rs/fp/fully_nonpreemptive.v`](files/results/rta/rs/fp/2026-10-03_040000_fully_nonpreemptive.md) | 3 | ✅ 是 | 09:28:23:09 |
| 342 | 28 | [`results/rta/rs/fp/fully_preemptive.v`](files/results/rta/rs/fp/2026-10-03_030000_fully_preemptive.md) | 3 | ✅ 是 | 09:28:22:52 |
| 343 | 28 | [`results/rta/rs/fp/limited_preemptive.v`](files/results/rta/rs/fp/2026-10-03_050000_limited_preemptive.md) | 3 | ✅ 是 | 09:28:23:30 |

</details>

<details open>
<summary><b>⏳ Unfinished — 29 files</b></summary>

<a id="unfinished-files"></a>

| Rank | Layer | v0.6 source file | Public declarations | 验证完成 |
| ---: | ---: | --- | ---: | :---: |
| 182 | 17 | [`implementation/facts/job_constructor.v`](files/implementation/facts/2026-10-05_170000_job_constructor.md) | 6 | ○ 否 |
| 230 | 20 | `results/transfer_schedulability/paper_model.v` | 19 | ○ 否 |
| 238 | 21 | [`model/task/arrival/example.v`](files/model/task/arrival/2026-10-05_160000_example.md) | 0 | ○ 否 |
| 283 | 26 | `results/rta/ideal/edf/bounded_pi.v` | 8 | ○ 否 |
| 284 | 26 | `results/rta/ideal/elf/bounded_pi.v` | 22 | ○ 否 |
| 285 | 26 | `results/rta/ideal/fifo/bounded_nps.v` | 8 | ○ 否 |
| 287 | 26 | `results/rta/ideal/fp/nonseq/bounded_pi.v` | 10 | ○ 否 |
| 288 | 26 | `results/rta/ideal/gel/bounded_pi.v` | 10 | ○ 否 |
| 293 | 27 | `results/rta/ideal/edf/bounded_nps.v` | 5 | ○ 否 |
| 297 | 27 | `results/rta/ideal/fp/limited_preemptive.v` | 1 | ○ 否 |
| 308 | 28 | `results/rta/ideal/edf/floating_nonpreemptive.v` | 1 | ○ 否 |
| 309 | 28 | `results/rta/ideal/edf/fully_nonpreemptive.v` | 1 | ○ 否 |
| 310 | 28 | `results/rta/ideal/edf/fully_preemptive.v` | 1 | ○ 否 |
| 311 | 28 | `results/rta/ideal/edf/limited_preemptive.v` | 1 | ○ 否 |
| 312 | 28 | `results/rta/ideal/fp/comp/fully_preemptive.v` | 1 | ○ 否 |
| 344 | 16 | `implementation/refinements/refinements.v` | 42 | ⏸ 否（外部边界） |
| 345 | 17 | `implementation/refinements/arrival_bound.v` | 36 | ⏸ 否（外部边界） |
| 346 | 18 | `implementation/refinements/task.v` | 24 | ⏸ 否（外部边界） |
| 347 | 19 | `implementation/refinements/arrival_curve.v` | 20 | ⏸ 否（外部边界） |
| 348 | 20 | `implementation/refinements/EDF/nonpreemptive_sched.v` | 9 | ⏸ 否（外部边界） |
| 349 | 20 | `implementation/refinements/EDF/preemptive_sched.v` | 6 | ⏸ 否（外部边界） |
| 350 | 20 | `implementation/refinements/FP/nonpreemptive_sched.v` | 9 | ⏸ 否（外部边界） |
| 351 | 20 | `implementation/refinements/FP/preemptive_sched.v` | 6 | ⏸ 否（外部边界） |
| 352 | 20 | `implementation/refinements/arrival_curve_prefix.v` | 4 | ⏸ 否（外部边界） |
| 353 | 21 | `implementation/refinements/fast_search_space_computation.v` | 8 | ⏸ 否（外部边界） |
| 354 | 27 | `implementation/refinements/FP/fast_search_space.v` | 10 | ⏸ 否（外部边界） |
| 355 | 28 | `implementation/refinements/EDF/fast_search_space.v` | 14 | ⏸ 否（外部边界） |
| 356 | 28 | `implementation/refinements/FP/refinements.v` | 28 | ⏸ 否（外部边界） |
| 357 | 29 | `implementation/refinements/EDF/refinements.v` | 23 | ⏸ 否（外部边界） |

</details>
<!-- V06_FILE_TABLE_END -->

## 设计决策（2026-09-30 用户授权）

以下决策由用户于 2026-09-30 明确给出，适用于后续所有工作；任何一项都**不允许**弱化验收门（actual-artifact、exact-type、source/target self-dependency、assumption audit、publication），也不允许把延期文件计为已完成。执行结果记录在各文件报告中，本节只维护决策与当前结论。

1. **`model/processor/multiprocessor.v` —— 仅授权窄范围的 Fin-sum projection 实验，不重写 exporter。**
   - 先在最小例子上复现确切的 import 瓶颈；在改动 exporter 代码之前，先检查现有 guarded-projection / equation 机制能否处理。
   - 任何替换都必须绑定到实际编译出的表达式；不得弱化 `rfl` guard、不得省略 proof field、不得引入 statement-only 假设。非定义等式必须走经检查的 equation/transport 路径，不得当作定义等式。
   - 覆盖一般 `n`，包括 `n = 0` 与单元素情形；测试实际的 export/import closure，完成 multiprocessor 语义验证，并回归现有 interval-sum（`Finset.Ico`）路径。
   - 只保留安全、经验证且有用的改动；否则回退实验性 tooling，保留精确的阻塞原因和已有的有效工作。
2. **`implementation/facts/job_constructor.v` —— 暂不开始大规模证书重做。** 先确定它所需的最小 concrete task/job adapter；更大的改动延期。
3. **CoqEAL refinements（`implementation/refinements/*`）继续延期**（外部边界）；不改变 pinned 工作环境（Lean 4.33.1、`rocq93rc1`）。
4. **`model/task/arrival/example.v`** —— 在其报告中记录确切的剩余阻塞原因，而不是“同前”。
5. **执行方式：** 保持单 agent；保留正在运行的任务与有效产物；继续推进独立的 READY 文件。

### 当前结论（2026-09-30）

| 决策 | 结论 | 证据 |
|---|---|---|
| 1. Fin-sum 实验 | **已验收**（313/1948）。最小复现表明瓶颈不是 `Fin` 求和：仅导出 `Fin.fintype` 求和 42 s 即导入完成；仅导出 `Finset.sum_range_succ` 1500 s 后仍卡在 `Nat.Internal.Linear.ExprCnstr.denote_toNormPoly`。真正来源是验证专用等式 `production_fin_sum` 的旧证明路径。只重写了该等式的证明（语句不变，经 `List.finRange` 逐元素证明），**未改 exporter、未加 projection/guard、未省略 proof field**；exporter 二进制与已验收 `Finset.Ico` 路径相同。此外去掉了 Lean 中 `multiprocessor_state : Type` 的宇宙注解，使逐核操作以通用常量导入。源码采用管线已有的 `patched` 模式（首次使用；3 行被删行已在 spec 中审计）。 | [multiprocessor 报告](files/model/processor/2026-10-05_180000_multiprocessor.md)；`Validation/logs/design_decisions_2026-09-30/finsum/` |
| 2. `implementation/facts/job_constructor.v` | **延期，未开始证书重做。** 已用 scratch 语句探针确定最小适配器：witness fixture + MAS 定义证书的载体关系化重放（`ItTaskRel`/`ItJobRel`）+ `_inst1` 到达序列关系 + concrete job 列表关系 + 类投影。 | [job_constructor 报告](files/implementation/facts/2026-10-05_170000_job_constructor.md) |
| 3. CoqEAL refinements | 继续延期（外部边界）；环境未改动。 | — |
| 4. `model/task/arrival/example.v` | **仍阻塞，已记录确切原因**：已验收闭包只有语句抽取模块，没有 hint 引理；官方 55 文件证明闭包在 `rocq93rc1` 下首个失败为 `util/list.v:23` `Stack overflow`；零声明验证器只接受 `Require Export` 聚合模块。 | [example 报告](files/model/task/arrival/2026-10-05_160000_example.md)；`Validation/logs/design_decisions_2026-09-30/example/` |

## 报告约定

每个已开始的 v0.6 source file 只维护一份 `files/<source-directory>/<首次报告时间>_<source-basename>.md`。后续批次、失败、修复和验收均更新该报告；文件名前的时间沿用最早的历史报告，不随更新改变。详细历史与发现请读[逐文件报告目录](files/)；跨文件执行记录见[runs/](runs/)。

[legacy/](legacy/) 保留可能被引用的旧报告，不能把其中的阶段性 PASS 当成最终验收。原始机器日志位于[Validation/logs/](../Validation/logs/)；正式验收和覆盖始终以[Validation/planning/v06_pipeline/](../Validation/planning/v06_pipeline/)中的 status/manifest 为准。`Prosa/` 中存在候选或 Rocq 证书编译通过，均不足以单独构成 `ACCEPTED_V06_FILE`。

每次整文件正式发布或已有验收证据失效后，运行 `python3 Validation/scripts/update_reports_readme.py`，随后以 `--check` 模式核对本页；不要手工改动自动生成区域。
