# 翻译与验证报告

## 当前状态

<!-- V06_STATUS_BEGIN -->
截至 2026-09-24，正式 machine state 记录 **51/357 个文件、377/2439 个 public declarations 已验收**。依据：[最新累计 status](../Validation/planning/v06_pipeline/model_processor_overheads_module_status.json)。表中的“是”仅表示已有 `ACCEPTED_V06_FILE`；“否”可能是未开始、进行中或受阻，不能据此推断尚未翻译。零声明文件也只有通过模块接口验收才写“是”。
<!-- V06_STATUS_END -->

<!-- V06_NAV_BEGIN -->
<details open>
<summary><b>📊 Translation Status</b></summary>

| Progress | Latest completed | Quick navigation |
|---|---|---|
| **51/357 files** · **377/2439 declarations** | **Rank 50** · `model/processor/overheads.v` | [🎯 Jump to latest completed](#latest-completed) · [✅ Finished](#finished-files) · [⏳ Unfinished](#unfinished-files) |

</details>
<!-- V06_NAV_END -->


- [Rank 50 `model/processor/overheads.v` 报告](files/model/processor/2026-09-24_111300_overheads.md)：完整 proof-body 导入关闭了原先 11 个 class/proof-field statement-only 依赖。
- [Rank 52 `model/processor/restricted_supply.v` 报告](files/model/processor/2026-09-24_144500_restricted_supply.md)：记录 concrete processor state 的整文件验证。
- [较早的阻塞项：`util/lcmseq.v`](files/util/2026-09-23_073256_lcmseq.md)：尚未验收，不计入上述数字。
- [本次连续执行汇总](runs/2026-09-24_035607_translation_order_continuous_run.md)：跨文件进展与运行背景；不替代正式状态。

下一个执行文件须依据[文件顺序](../v06_file_translation_order.md)、最新 status/manifest 和文件依赖图重新判定；本页不固定其 READY 状态。

## 逐文件验证状态

按正式执行顺序列出 pinned v0.6 的全部 357 个 source file；声明数来自 `Validation/planning/v06_dependency/declaration_inventory.csv`，完成状态来自最新有效的逐文件 status，并与累计 machine state 核对。此表是报告快照，不代替 artifact/hash/assumption 的正式验收门槛。

完成记录时间按香港本地时间（UTC+08:00）的“月:日:时:分”显示，优先取 manifest 的 `published_at` 或 canonical report 明确记载的整文件验收事件；其余旧记录使用首次 `ACCEPTED_V06_FILE` status 文件写入时间作为近似机器记录时间，不能将它理解为独立核验的精确完成时刻。[逐文件时间依据](../Validation/planning/v06_pipeline/reports_readme_completion_evidence.json)保存了来源和哈希；报告文件名中的时间是首次写报告的时间，不是验收时间。

<a id="file-validation-table"></a>

<!-- V06_FILE_TABLE_BEGIN -->
<details open>
<summary><b>✅ Finished — 51 files</b></summary>

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
| 50 | 10 | <a id="latest-completed"></a>[`model/processor/overheads.v`](files/model/processor/2026-09-24_111300_overheads.md) | 13 | ✅ 是 | 09:24:17:04 |
| 51 | 10 | [`model/processor/platform_properties.v`](files/model/processor/2026-09-24_134231_platform_properties.md) | 6 | ✅ 是 | 09:24:14:40 |
| 52 | 10 | [`model/processor/restricted_supply.v`](files/model/processor/2026-09-24_144500_restricted_supply.md) | 5 | ✅ 是 | 09:24:15:24 |

</details>

<details open>
<summary><b>⏳ Unfinished — 306 files</b></summary>

<a id="unfinished-files"></a>

| Rank | Layer | v0.6 source file | Public declarations | 验证完成 |
| ---: | ---: | --- | ---: | :---: |
| 30 | 1 | [`util/lcmseq.v`](files/util/2026-09-23_073256_lcmseq.md) | 5 | ○ 否 |
| 53 | 10 | `model/processor/spin.v` | 5 | ○ 否 |
| 54 | 10 | `model/processor/varspeed.v` | 5 | ○ 否 |
| 55 | 10 | `model/readiness/basic.v` | 0 | ○ 否 |
| 56 | 10 | `model/readiness/jitter.v` | 2 | ○ 否 |
| 57 | 10 | `model/schedule/edf.v` | 2 | ○ 否 |
| 58 | 10 | `model/schedule/nonpreemptive.v` | 1 | ○ 否 |
| 59 | 10 | `model/schedule/scheduled.v` | 3 | ○ 否 |
| 60 | 10 | `model/schedule/work_conserving.v` | 2 | ○ 否 |
| 61 | 10 | `model/task/concept.v` | 19 | ○ 否 |
| 62 | 11 | `analysis/abstract/definitions.v` | 15 | ○ 否 |
| 63 | 11 | `analysis/abstract/search_space.v` | 6 | ○ 否 |
| 64 | 11 | `analysis/definitions/overheads/schedule_change.v` | 4 | ○ 否 |
| 65 | 11 | `analysis/definitions/task_schedule.v` | 7 | ○ 否 |
| 66 | 11 | `analysis/facts/behavior/supply.v` | 16 | ○ 否 |
| 67 | 11 | `analysis/facts/model/ideal_uni_exceed.v` | 7 | ○ 否 |
| 68 | 11 | `analysis/facts/model/restricted_supply/schedule.v` | 3 | ○ 否 |
| 69 | 11 | `analysis/facts/model/task_cost.v` | 2 | ○ 否 |
| 70 | 11 | `analysis/facts/model/uniprocessor.v` | 1 | ○ 否 |
| 71 | 11 | `implementation/definitions/generic_scheduler.v` | 4 | ○ 否 |
| 72 | 11 | `model/priority/definitions.v` | 20 | ○ 否 |
| 73 | 11 | `model/schedule/tdma.v` | 15 | ○ 否 |
| 74 | 11 | `model/task/absolute_deadline.v` | 1 | ○ 否 |
| 75 | 11 | `model/task/arrival/sporadic.v` | 5 | ○ 否 |
| 76 | 11 | `model/task/arrivals.v` | 13 | ○ 否 |
| 77 | 11 | `model/task/jitter.v` | 3 | ○ 否 |
| 78 | 12 | `analysis/abstract/restricted_supply/busy_sbf.v` | 2 | ○ 否 |
| 79 | 12 | `analysis/definitions/infinite_jobs.v` | 1 | ○ 否 |
| 80 | 12 | `analysis/definitions/readiness_interference.v` | 3 | ○ 否 |
| 81 | 12 | `analysis/facts/SBF.v` | 3 | ○ 否 |
| 82 | 12 | `analysis/facts/behavior/arrivals.v` | 45 | ○ 否 |
| 83 | 12 | `analysis/facts/tdma.v` | 6 | ○ 否 |
| 84 | 12 | `model/priority/coercion.v` | 10 | ○ 否 |
| 85 | 12 | `model/task/arrival/curves.v` | 14 | ○ 否 |
| 86 | 12 | `model/task/arrival/request_bound_functions.v` | 8 | ○ 否 |
| 87 | 12 | `model/task/arrival/task_max_inter_arrival.v` | 5 | ○ 否 |
| 88 | 12 | `model/task/sequentiality.v` | 2 | ○ 否 |
| 89 | 13 | `analysis/definitions/delay_propagation.v` | 7 | ○ 否 |
| 90 | 13 | `analysis/facts/model/scheduled.v` | 14 | ○ 否 |
| 91 | 13 | `analysis/facts/model/task_arrivals.v` | 23 | ○ 否 |
| 92 | 13 | `implementation/definitions/maximal_arrival_sequence.v` | 7 | ○ 否 |
| 93 | 13 | `model/composite/valid_task_arrival_sequence.v` | 6 | ○ 否 |
| 94 | 13 | `model/priority/classes.v` | 0 | ○ 否 |
| 95 | 13 | `model/readiness/sequential.v` | 0 | ○ 否 |
| 96 | 13 | `model/task/arrival/curve_as_rbf.v` | 12 | ○ 否 |
| 97 | 14 | `analysis/definitions/always_higher_priority.v` | 2 | ○ 否 |
| 98 | 14 | `analysis/definitions/carry_in.v` | 1 | ○ 否 |
| 99 | 14 | `analysis/definitions/overheads/priority_bump.v` | 1 | ○ 否 |
| 100 | 14 | `analysis/definitions/priority/classes.v` | 1 | ○ 否 |
| 101 | 14 | `analysis/definitions/work_bearing_readiness.v` | 1 | ○ 否 |
| 102 | 14 | `analysis/facts/behavior/service.v` | 57 | ○ 否 |
| 103 | 14 | `analysis/facts/delay_propagation.v` | 12 | ○ 否 |
| 104 | 14 | `analysis/facts/job_index.v` | 21 | ○ 否 |
| 105 | 14 | `analysis/facts/model/arrival_curves.v` | 3 | ○ 否 |
| 106 | 14 | `analysis/facts/model/sbf/average.v` | 3 | ○ 否 |
| 107 | 14 | `analysis/facts/model/sbf/periodic.v` | 9 | ○ 否 |
| 108 | 14 | `analysis/facts/sporadic/arrival_bound.v` | 4 | ○ 否 |
| 109 | 14 | `implementation/facts/maximal_arrival_sequence.v` | 14 | ○ 否 |
| 110 | 14 | `model/aggregate/service_of_jobs.v` | 8 | ○ 否 |
| 111 | 14 | `model/aggregate/workload.v` | 8 | ○ 否 |
| 112 | 14 | `model/preemption/parameter.v` | 14 | ○ 否 |
| 113 | 14 | `model/priority/deadline_monotonic.v` | 4 | ○ 否 |
| 114 | 14 | `model/priority/edf.v` | 4 | ○ 否 |
| 115 | 14 | `model/priority/fifo.v` | 4 | ○ 否 |
| 116 | 14 | `model/priority/gel.v` | 7 | ○ 否 |
| 117 | 14 | `model/priority/numeric_fixed_priority.v` | 7 | ○ 否 |
| 118 | 14 | `model/priority/rate_monotonic.v` | 4 | ○ 否 |
| 119 | 15 | `analysis/definitions/interference.v` | 15 | ○ 否 |
| 120 | 15 | `analysis/definitions/progress.v` | 4 | ○ 否 |
| 121 | 15 | `analysis/definitions/readiness.v` | 3 | ○ 否 |
| 122 | 15 | `analysis/facts/behavior/completion.v` | 30 | ○ 否 |
| 123 | 15 | `analysis/facts/model/ideal/schedule.v` | 19 | ○ 否 |
| 124 | 15 | `analysis/facts/model/ideal/service_of_jobs.v` | 2 | ○ 否 |
| 125 | 15 | `analysis/facts/model/task_schedule.v` | 10 | ○ 否 |
| 126 | 15 | `analysis/facts/model/workload.v` | 17 | ○ 否 |
| 127 | 15 | `analysis/facts/priority/classes.v` | 22 | ○ 否 |
| 128 | 15 | `analysis/facts/sporadic/arrival_times.v` | 3 | ○ 否 |
| 129 | 15 | `implementation/definitions/task.v` | 15 | ○ 否 |
| 130 | 15 | `model/preemption/fully_nonpreemptive.v` | 0 | ○ 否 |
| 131 | 15 | `model/preemption/fully_preemptive.v` | 0 | ○ 否 |
| 132 | 15 | `model/preemption/limited_preemptive.v` | 5 | ○ 否 |
| 133 | 15 | `model/priority/elf.v` | 1 | ○ 否 |
| 134 | 15 | `model/processor/multiprocessor.v` | 6 | ○ 否 |
| 135 | 15 | `model/schedule/limited_preemptive.v` | 1 | ○ 否 |
| 136 | 15 | `model/schedule/preemption_time.v` | 1 | ○ 否 |
| 137 | 15 | `model/task/arrival/sporadic_as_curve.v` | 5 | ○ 否 |
| 138 | 15 | `model/task/preemption/parameters.v` | 13 | ○ 否 |
| 139 | 16 | `analysis/definitions/blocking_bound/edf.v` | 2 | ○ 否 |
| 140 | 16 | `analysis/definitions/blocking_bound/elf.v` | 1 | ○ 否 |
| 141 | 16 | `analysis/definitions/blocking_bound/fp.v` | 1 | ○ 否 |
| 142 | 16 | `analysis/definitions/busy_interval/classical.v` | 5 | ○ 否 |
| 143 | 16 | `analysis/definitions/request_bound_function.v` | 6 | ○ 否 |
| 144 | 16 | `analysis/definitions/schedulability.v` | 6 | ○ 否 |
| 145 | 16 | `analysis/definitions/service_inversion/pred.v` | 4 | ○ 否 |
| 146 | 16 | `analysis/facts/behavior/deadlines.v` | 4 | ○ 否 |
| 147 | 16 | `analysis/facts/preemption/job/preemptive.v` | 3 | ○ 否 |
| 148 | 16 | `analysis/facts/priority/jlfp_with_fp.v` | 8 | ○ 否 |
| 149 | 16 | `analysis/facts/readiness/backlogged.v` | 5 | ○ 否 |
| 150 | 16 | `analysis/facts/readiness/basic.v` | 3 | ○ 否 |
| 151 | 16 | `analysis/facts/readiness/sequential.v` | 4 | ○ 否 |
| 152 | 16 | `analysis/facts/sporadic/arrival_sequence.v` | 7 | ○ 否 |
| 153 | 16 | `analysis/facts/transform/replace_at.v` | 7 | ○ 否 |
| 154 | 16 | `implementation/definitions/job_constructor.v` | 4 | ○ 否 |
| 155 | 16 | `model/readiness/suspension.v` | 4 | ○ 否 |
| 156 | 16 | `model/schedule/priority_driven.v` | 3 | ○ 否 |
| 157 | 16 | `model/task/preemption/floating_nonpreemptive.v` | 2 | ○ 否 |
| 158 | 16 | `model/task/preemption/fully_nonpreemptive.v` | 1 | ○ 否 |
| 159 | 16 | `model/task/preemption/fully_preemptive.v` | 1 | ○ 否 |
| 160 | 16 | `model/task/preemption/limited_preemptive.v` | 8 | ○ 否 |
| 161 | 17 | `analysis/abstract/restricted_supply/busy_prefix.v` | 2 | ○ 否 |
| 162 | 17 | `analysis/definitions/busy_interval/edf_pi_bound.v` | 1 | ○ 否 |
| 163 | 17 | `analysis/definitions/demand_bound_function.v` | 2 | ○ 否 |
| 164 | 17 | `analysis/definitions/priority_inversion.v` | 8 | ○ 否 |
| 165 | 17 | `analysis/definitions/sbf/busy.v` | 2 | ○ 否 |
| 166 | 17 | `analysis/definitions/service_inversion/busy_prefix.v` | 2 | ○ 否 |
| 167 | 17 | `analysis/definitions/service_inversion/readiness_aware.v` | 3 | ○ 否 |
| 168 | 17 | `analysis/definitions/tardiness.v` | 1 | ○ 否 |
| 169 | 17 | `analysis/definitions/workload/bounded.v` | 1 | ○ 否 |
| 170 | 17 | `analysis/definitions/workload/edf_athep_bound.v` | 1 | ○ 否 |
| 171 | 17 | `analysis/definitions/workload/elf_athep_bound.v` | 4 | ○ 否 |
| 172 | 17 | `analysis/facts/behavior/all.v` | 0 | ○ 否 |
| 173 | 17 | `analysis/facts/busy_interval/quiet_time.v` | 4 | ○ 否 |
| 174 | 17 | `analysis/facts/edf_definitions.v` | 3 | ○ 否 |
| 175 | 17 | `analysis/facts/jitter.v` | 14 | ○ 否 |
| 176 | 17 | `analysis/facts/model/preemption.v` | 14 | ○ 否 |
| 177 | 17 | `analysis/facts/preemption/task/preemptive.v` | 2 | ○ 否 |
| 178 | 17 | `analysis/facts/suspension.v` | 11 | ○ 否 |
| 179 | 17 | `analysis/facts/transform/swaps.v` | 22 | ○ 否 |
| 180 | 17 | `implementation/definitions/ideal_uni_scheduler.v` | 5 | ○ 否 |
| 181 | 17 | `implementation/facts/generic_schedule.v` | 6 | ○ 否 |
| 182 | 17 | `implementation/facts/job_constructor.v` | 6 | ○ 否 |
| 183 | 17 | `model/task/suspension/dynamic.v` | 2 | ○ 否 |
| 184 | 18 | `analysis/facts/completes_at.v` | 5 | ○ 否 |
| 185 | 18 | `analysis/facts/model/dynamic_suspension.v` | 2 | ○ 否 |
| 186 | 18 | `analysis/facts/model/exceedance/SBF.v` | 4 | ○ 否 |
| 187 | 18 | `analysis/facts/model/rbf.v` | 27 | ○ 否 |
| 188 | 18 | `analysis/facts/model/sequential.v` | 3 | ○ 否 |
| 189 | 18 | `analysis/facts/model/service_of_jobs.v` | 22 | ○ 否 |
| 190 | 18 | `analysis/facts/preemption/job/nonpreemptive.v` | 4 | ○ 否 |
| 191 | 18 | `analysis/facts/preemption/rtc_threshold/job_preemptable.v` | 14 | ○ 否 |
| 192 | 18 | `analysis/facts/priority/inversion.v` | 7 | ○ 否 |
| 193 | 18 | `analysis/facts/priority/sequential.v` | 1 | ○ 否 |
| 194 | 18 | `analysis/transform/prefix.v` | 3 | ○ 否 |
| 195 | 18 | `implementation/facts/ideal_uni/preemption_aware.v` | 10 | ○ 否 |
| 196 | 18 | `model/task/offset.v` | 7 | ○ 否 |
| 197 | 19 | `analysis/abstract/iw_auxiliary.v` | 6 | ○ 否 |
| 198 | 19 | `analysis/abstract/restricted_supply/search_space/fp.v` | 2 | ○ 否 |
| 199 | 19 | `analysis/facts/busy_interval/existence.v` | 14 | ○ 否 |
| 200 | 19 | `analysis/facts/interference.v` | 17 | ○ 否 |
| 201 | 19 | `analysis/facts/model/dbf.v` | 8 | ○ 否 |
| 202 | 19 | `analysis/facts/model/ideal/priority_inversion.v` | 4 | ○ 否 |
| 203 | 19 | `analysis/facts/model/offset.v` | 2 | ○ 否 |
| 204 | 19 | `analysis/facts/preemption/job/limited.v` | 10 | ○ 否 |
| 205 | 19 | `analysis/facts/preemption/rtc_threshold/nonpreemptive.v` | 3 | ○ 否 |
| 206 | 19 | `analysis/facts/preemption/rtc_threshold/preemptive.v` | 1 | ○ 否 |
| 207 | 19 | `analysis/facts/preemption/task/nonpreemptive.v` | 2 | ○ 否 |
| 208 | 19 | `analysis/facts/priority/edf.v` | 5 | ○ 否 |
| 209 | 19 | `analysis/facts/priority/gel.v` | 6 | ○ 否 |
| 210 | 19 | `analysis/facts/workload/edf_athep_bound.v` | 4 | ○ 否 |
| 211 | 19 | `analysis/facts/workload/elf_athep_bound.v` | 6 | ○ 否 |
| 212 | 19 | `analysis/transform/edf_trans.v` | 6 | ○ 否 |
| 213 | 19 | `analysis/transform/wc_trans.v` | 6 | ○ 否 |
| 214 | 19 | `implementation/facts/ideal_uni/prio_aware.v` | 5 | ○ 否 |
| 215 | 19 | `model/task/arrival/periodic.v` | 5 | ○ 否 |
| 216 | 19 | `results/transfer_schedulability/criterion.v` | 40 | ○ 否 |
| 217 | 20 | `analysis/abstract/busy_interval.v` | 15 | ○ 否 |
| 218 | 20 | `analysis/abstract/restricted_supply/search_space/edf.v` | 2 | ○ 否 |
| 219 | 20 | `analysis/abstract/restricted_supply/search_space/elf.v` | 2 | ○ 否 |
| 220 | 20 | `analysis/definitions/hyperperiod.v` | 7 | ○ 否 |
| 221 | 20 | `analysis/facts/busy_interval/carry_in.v` | 9 | ○ 否 |
| 222 | 20 | `analysis/facts/busy_interval/hep_at_pt.v` | 8 | ○ 否 |
| 223 | 20 | `analysis/facts/preemption/task/floating.v` | 2 | ○ 否 |
| 224 | 20 | `analysis/facts/preemption/task/limited.v` | 2 | ○ 否 |
| 225 | 20 | `analysis/facts/priority/elf.v` | 8 | ○ 否 |
| 226 | 20 | `analysis/facts/readiness_interference.v` | 2 | ○ 否 |
| 227 | 20 | `analysis/facts/transform/edf_opt.v` | 43 | ○ 否 |
| 228 | 20 | `analysis/facts/transform/wc_correctness.v` | 33 | ○ 否 |
| 229 | 20 | `model/task/arrival/periodic_as_sporadic.v` | 5 | ○ 否 |
| 230 | 20 | `results/transfer_schedulability/paper_model.v` | 19 | ○ 否 |
| 231 | 21 | `analysis/abstract/lower_bound_on_service.v` | 3 | ○ 否 |
| 232 | 21 | `analysis/facts/busy_interval/arrival.v` | 3 | ○ 否 |
| 233 | 21 | `analysis/facts/busy_interval/pi.v` | 24 | ○ 否 |
| 234 | 21 | `analysis/facts/periodic/arrival_separation.v` | 3 | ○ 否 |
| 235 | 21 | `analysis/facts/preemption/rtc_threshold/floating.v` | 1 | ○ 否 |
| 236 | 21 | `analysis/facts/preemption/rtc_threshold/limited.v` | 3 | ○ 否 |
| 237 | 21 | `analysis/facts/transform/edf_wc.v` | 11 | ○ 否 |
| 238 | 21 | `model/task/arrival/example.v` | 0 | ○ 否 |
| 239 | 21 | `results/generality/elf.v` | 3 | ○ 否 |
| 240 | 22 | `analysis/abstract/abstract_rta.v` | 14 | ○ 否 |
| 241 | 22 | `analysis/facts/blocking_bound/edf.v` | 1 | ○ 否 |
| 242 | 22 | `analysis/facts/blocking_bound/elf.v` | 1 | ○ 否 |
| 243 | 22 | `analysis/facts/blocking_bound/fp.v` | 1 | ○ 否 |
| 244 | 22 | `analysis/facts/busy_interval/pi_bound.v` | 1 | ○ 否 |
| 245 | 22 | `analysis/facts/busy_interval/pi_cond.v` | 1 | ○ 否 |
| 246 | 22 | `analysis/facts/busy_interval/service_inversion.v` | 12 | ○ 否 |
| 247 | 22 | `analysis/facts/model/overheads/schedule.v` | 6 | ○ 否 |
| 248 | 22 | `analysis/facts/periodic/max_inter_arrival.v` | 3 | ○ 否 |
| 249 | 22 | `results/optimality/edf.v` | 4 | ○ 否 |
| 250 | 23 | `analysis/abstract/IBF/supply.v` | 3 | ○ 否 |
| 251 | 23 | `analysis/abstract/IBF/task.v` | 18 | ○ 否 |
| 252 | 23 | `analysis/abstract/ideal/abstract_rta.v` | 2 | ○ 否 |
| 253 | 23 | `analysis/facts/busy_interval/all.v` | 0 | ○ 否 |
| 254 | 23 | `analysis/facts/model/overheads/priority_bump.v` | 3 | ○ 否 |
| 255 | 23 | `analysis/facts/model/overheads/schedule_change.v` | 6 | ○ 否 |
| 256 | 23 | `analysis/facts/periodic/arrival_times.v` | 3 | ○ 否 |
| 257 | 24 | `analysis/abstract/IBF/supply_task.v` | 3 | ○ 否 |
| 258 | 24 | `analysis/abstract/ideal/abstract_seq_rta.v` | 2 | ○ 否 |
| 259 | 24 | `analysis/abstract/ideal/iw_instantiation.v` | 20 | ○ 否 |
| 260 | 24 | `analysis/abstract/restricted_supply/abstract_rta.v` | 10 | ○ 否 |
| 261 | 24 | `analysis/facts/model/overheads/schedule_change_bound.v` | 3 | ○ 否 |
| 262 | 24 | `analysis/facts/periodic/task_arrivals_size.v` | 8 | ○ 否 |
| 263 | 24 | `analysis/facts/priority/fifo.v` | 12 | ○ 否 |
| 264 | 24 | `model/processor/overhead_resource_model.v` | 10 | ○ 否 |
| 265 | 25 | `analysis/abstract/ideal/cumulative_bounds.v` | 2 | ○ 否 |
| 266 | 25 | `analysis/abstract/restricted_supply/abstract_seq_rta.v` | 3 | ○ 否 |
| 267 | 25 | `analysis/abstract/restricted_supply/iw_instantiation.v` | 17 | ○ 否 |
| 268 | 25 | `analysis/abstract/restricted_supply/iw_readiness.v` | 18 | ○ 否 |
| 269 | 25 | `analysis/abstract/restricted_supply/search_space/fifo.v` | 2 | ○ 否 |
| 270 | 25 | `analysis/facts/hyperperiod.v` | 10 | ○ 否 |
| 271 | 25 | `analysis/facts/model/overheads/blackout_bound.v` | 11 | ○ 否 |
| 272 | 25 | `analysis/facts/priority/fifo_ahep_bound.v` | 1 | ○ 否 |
| 273 | 25 | `results/generality/gel.v` | 5 | ○ 否 |
| 274 | 25 | `results/rta/ideal/fp/bounded_pi.v` | 6 | ○ 否 |
| 275 | 26 | `analysis/abstract/restricted_supply/bounded_bi/aux.v` | 3 | ○ 否 |
| 276 | 26 | `analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v` | 1 | ○ 否 |
| 277 | 26 | `analysis/abstract/restricted_supply/task_ibf_readiness.v` | 2 | ○ 否 |
| 278 | 26 | `analysis/abstract/restricted_supply/task_intra_interference_bound.v` | 2 | ○ 否 |
| 279 | 26 | `analysis/facts/model/overheads/sbf/fifo.v` | 6 | ○ 否 |
| 280 | 26 | `analysis/facts/model/overheads/sbf/fp.v` | 6 | ○ 否 |
| 281 | 26 | `analysis/facts/model/overheads/sbf/jlfp.v` | 6 | ○ 否 |
| 282 | 26 | `analysis/facts/shifted_job_costs.v` | 3 | ○ 否 |
| 283 | 26 | `results/rta/ideal/edf/bounded_pi.v` | 8 | ○ 否 |
| 284 | 26 | `results/rta/ideal/elf/bounded_pi.v` | 22 | ○ 否 |
| 285 | 26 | `results/rta/ideal/fifo/bounded_nps.v` | 8 | ○ 否 |
| 286 | 26 | `results/rta/ideal/fp/bounded_nps.v` | 3 | ○ 否 |
| 287 | 26 | `results/rta/ideal/fp/nonseq/bounded_pi.v` | 10 | ○ 否 |
| 288 | 26 | `results/rta/ideal/gel/bounded_pi.v` | 10 | ○ 否 |
| 289 | 27 | `analysis/abstract/restricted_supply/bounded_bi/edf.v` | 2 | ○ 否 |
| 290 | 27 | `analysis/abstract/restricted_supply/bounded_bi/elf.v` | 1 | ○ 否 |
| 291 | 27 | `analysis/abstract/restricted_supply/bounded_bi/fp.v` | 1 | ○ 否 |
| 292 | 27 | `analysis/abstract/restricted_supply/bounded_bi/jlfp.v` | 1 | ○ 否 |
| 293 | 27 | `results/rta/ideal/edf/bounded_nps.v` | 5 | ○ 否 |
| 294 | 27 | `results/rta/ideal/fp/floating_nonpreemptive.v` | 1 | ○ 否 |
| 295 | 27 | `results/rta/ideal/fp/fully_nonpreemptive.v` | 1 | ○ 否 |
| 296 | 27 | `results/rta/ideal/fp/fully_preemptive.v` | 1 | ○ 否 |
| 297 | 27 | `results/rta/ideal/fp/limited_preemptive.v` | 1 | ○ 否 |
| 298 | 28 | `results/rta/arm/edf/floating_nonpreemptive.v` | 3 | ○ 否 |
| 299 | 28 | `results/rta/arm/edf/fully_nonpreemptive.v` | 3 | ○ 否 |
| 300 | 28 | `results/rta/arm/edf/fully_preemptive.v` | 3 | ○ 否 |
| 301 | 28 | `results/rta/arm/edf/limited_preemptive.v` | 3 | ○ 否 |
| 302 | 28 | `results/rta/arm/fifo/bounded_nps.v` | 3 | ○ 否 |
| 303 | 28 | `results/rta/arm/fp/floating_nonpreemptive.v` | 3 | ○ 否 |
| 304 | 28 | `results/rta/arm/fp/fully_nonpreemptive.v` | 3 | ○ 否 |
| 305 | 28 | `results/rta/arm/fp/fully_preemptive.v` | 3 | ○ 否 |
| 306 | 28 | `results/rta/arm/fp/limited_preemptive.v` | 3 | ○ 否 |
| 307 | 28 | `results/rta/exc/fp/fully_nonpreemptive.v` | 3 | ○ 否 |
| 308 | 28 | `results/rta/ideal/edf/floating_nonpreemptive.v` | 1 | ○ 否 |
| 309 | 28 | `results/rta/ideal/edf/fully_nonpreemptive.v` | 1 | ○ 否 |
| 310 | 28 | `results/rta/ideal/edf/fully_preemptive.v` | 1 | ○ 否 |
| 311 | 28 | `results/rta/ideal/edf/limited_preemptive.v` | 1 | ○ 否 |
| 312 | 28 | `results/rta/ideal/fp/comp/fully_preemptive.v` | 1 | ○ 否 |
| 313 | 28 | `results/rta/ovh/edf/floating_nonpreemptive.v` | 3 | ○ 否 |
| 314 | 28 | `results/rta/ovh/edf/fully_nonpreemptive.v` | 3 | ○ 否 |
| 315 | 28 | `results/rta/ovh/edf/fully_preemptive.v` | 3 | ○ 否 |
| 316 | 28 | `results/rta/ovh/edf/limited_preemptive.v` | 3 | ○ 否 |
| 317 | 28 | `results/rta/ovh/fifo/bounded_nps.v` | 3 | ○ 否 |
| 318 | 28 | `results/rta/ovh/fp/floating_nonpreemptive.v` | 3 | ○ 否 |
| 319 | 28 | `results/rta/ovh/fp/fully_nonpreemptive.v` | 3 | ○ 否 |
| 320 | 28 | `results/rta/ovh/fp/fully_preemptive.v` | 3 | ○ 否 |
| 321 | 28 | `results/rta/ovh/fp/limited_preemptive.v` | 3 | ○ 否 |
| 322 | 28 | `results/rta/prm/edf/floating_nonpreemptive.v` | 3 | ○ 否 |
| 323 | 28 | `results/rta/prm/edf/fully_nonpreemptive.v` | 3 | ○ 否 |
| 324 | 28 | `results/rta/prm/edf/fully_preemptive.v` | 3 | ○ 否 |
| 325 | 28 | `results/rta/prm/edf/limited_preemptive.v` | 3 | ○ 否 |
| 326 | 28 | `results/rta/prm/fifo/bounded_nps.v` | 3 | ○ 否 |
| 327 | 28 | `results/rta/prm/fp/floating_nonpreemptive.v` | 3 | ○ 否 |
| 328 | 28 | `results/rta/prm/fp/fully_nonpreemptive.v` | 3 | ○ 否 |
| 329 | 28 | `results/rta/prm/fp/fully_preemptive.v` | 3 | ○ 否 |
| 330 | 28 | `results/rta/prm/fp/limited_preemptive.v` | 3 | ○ 否 |
| 331 | 28 | `results/rta/rs/edf/floating_nonpreemptive.v` | 3 | ○ 否 |
| 332 | 28 | `results/rta/rs/edf/fully_nonpreemptive.v` | 3 | ○ 否 |
| 333 | 28 | `results/rta/rs/edf/fully_preemptive.v` | 3 | ○ 否 |
| 334 | 28 | `results/rta/rs/edf/limited_preemptive.v` | 3 | ○ 否 |
| 335 | 28 | `results/rta/rs/elf/floating_nonpreemptive.v` | 3 | ○ 否 |
| 336 | 28 | `results/rta/rs/elf/fully_nonpreemptive.v` | 3 | ○ 否 |
| 337 | 28 | `results/rta/rs/elf/fully_preemptive.v` | 3 | ○ 否 |
| 338 | 28 | `results/rta/rs/elf/limited_preemptive.v` | 3 | ○ 否 |
| 339 | 28 | `results/rta/rs/fifo/bounded_nps.v` | 3 | ○ 否 |
| 340 | 28 | `results/rta/rs/fp/floating_nonpreemptive.v` | 3 | ○ 否 |
| 341 | 28 | `results/rta/rs/fp/fully_nonpreemptive.v` | 3 | ○ 否 |
| 342 | 28 | `results/rta/rs/fp/fully_preemptive.v` | 3 | ○ 否 |
| 343 | 28 | `results/rta/rs/fp/limited_preemptive.v` | 3 | ○ 否 |
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

## 报告约定

每个已开始的 v0.6 source file 只维护一份 `files/<source-directory>/<首次报告时间>_<source-basename>.md`。后续批次、失败、修复和验收均更新该报告；文件名前的时间沿用最早的历史报告，不随更新改变。详细历史与发现请读[逐文件报告目录](files/)；跨文件执行记录见[runs/](runs/)。

[legacy/](legacy/) 保留可能被引用的旧报告，不能把其中的阶段性 PASS 当成最终验收。原始机器日志位于[Validation/logs/](../Validation/logs/)；正式验收和覆盖始终以[Validation/planning/v06_pipeline/](../Validation/planning/v06_pipeline/)中的 status/manifest 为准。`Prosa/` 中存在候选或 Rocq 证书编译通过，均不足以单独构成 `ACCEPTED_V06_FILE`。

每次整文件正式发布或已有验收证据失效后，运行 `python3 Validation/scripts/update_reports_readme.py`，随后以 `--check` 模式核对本页；不要手工改动自动生成区域。
