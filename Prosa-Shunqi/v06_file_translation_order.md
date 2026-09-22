# Prosa v0.6 文件翻译执行顺序

## 使用方式

本文件是**正式 file execution order，但不是 acceptance 证据**。正式路径固定为
`Prosa-Shunqi/v06_file_translation_order.md`；正式 workspace 为
`Prosa-Shunqi/`，历史 `Prosa-fei/` 只读。Agent 开始新文件前必须重读本文件、
`.agents/skills/prosa-v06-translation/SKILL.md`、最新 pipeline manifest/status
以及 authoritative file DAG。file DAG 决定 READY；本文件只在多个 READY 文件间
决定先后。

## Authority 与快照

- 唯一 specification：Prosa v0.6 `414e66760333eaa4ef78c685bcf53291c527a548`。
- 本次读取 RTS commit：`4e9f60d54e5722a92170413bf4506c7df91cdf21`。
- 正式验证环境：Lean 4.33.1；Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`；Rocq 9.3。
- 调度 authority：`Validation/planning/v06_dependency/file_layers.csv`；数量及种类来自 `file_inventory.csv`、`declaration_inventory.csv`。
- 完整范围：357 个文件。343 个属于 main；14 个 refinement 文件单独保留为 deferred。普通 MathComp/HB/Stdlib 依赖不因此被一概排除。
- `scope_manifest.json` 中较早的 worktree 路径和工具版本是历史 inventory provenance，不是要求退回旧 workspace 或旧验证环境。

JSON 内锁定了四个 planning input 的 Git blob SHA。正常的新翻译 commit 不改变这份顺序；planning input 变更则检查失败，必须重新审查计划，不能只改 hash 绕过检查。

## Agent 执行规则

1. **按本文件的 rank 顺序，选择下一个尚未完整完成的 source file。** 若该文件已存在有效的 `ACCEPTED_V06_FILE` 证据，则检查证据仍与当前 source/artifact/certificate 匹配后跳过；否则继续完成该文件。开始前仍必须满足 scope 允许且 **所有直接文件依赖均已有效验收**。
2. 依赖文件只有部分 declarations accepted、证据 stale 或只有 compile PASS，都不满足文件门槛。某项被阻塞时记录 blocker，可继续其他已 READY 的独立文件；不可启动其下游，不可删 DAG 边制造 READY。记录跳过原因，解除阻塞后回到较早 rank。
3. 一个任务优先以 **whole file** 为单位。通常 ≤15 个声明整文件一批；16–20 个先检查新语义边界；>20 个先完成 whole-file operation inventory、核对已有 bridges 和计算/export interface，再冻结 snapshot 并按相互关联的声明组开发证书。大文件内部允许分批，但整文件没收尾之前仍不能放行下游。声明 DAG 只细化文件内顺序，不替代文件 DAG。
4. 每个新 class/计算边界先做最小 actual-artifact 预检；之后收齐本文件候选并冻结 snapshot，复用 prepare→check→finalize。输入、完整相关依赖、工具链及配置 hash 全匹配时，优先复用已验证的 accepted dependency artifact；certificate-only 修改不重跑 Lean/export/import，输入变化或 cache 损坏则准确失效并 fail closed。
5. 新文件先匹配已审核的 source/export/import/normalization pattern，并优先组合已认证 correspondence DAG 或生成最小 artifact-local adapter。只为真正缺失的操作新增具名、可复用证书；不复证已有 List/Nat/equality，不用 source/target 业务 theorem 自证。每项继续要求 `semantic_premises=[]`、source/target self-dependency=false、unexpected assumptions=[]，并保留准确的 foundation 分类。
6. **每个 authoritative source file 恰好维护一个 file-level report，不多也不少。** 固定放在 `Prosa-Shunqi/Reports/files/<source directory>/<first-report-timestamp>_<source basename>.md`；时间戳继承该 file 最早历史 report 的时间、不带 timezone 后缀，后续更新不改变文件名。例如当前 `util/list.v` 对应 `Reports/files/util/2026-09-21_082258_list.md`。首次处理该文件时创建；后续内部 batch、重试、blocker、revalidation 都追加/更新同一个 report，禁止再为同一 source file 创建第二份 report。零声明文件也需要自己的 report。Report 至少记录 source identity、处理范围、translation/proof/semantic-validation 状态、reused/new correspondence、blocker、最终 acceptance 和关键 artifact/certificate evidence。
7. **不要因为普通证明困难就改写已经忠实的 Lean translation。** 默认先尝试已有 bridge、局部 proof 重构、actual-artifact equations、最小 operation certificate 和合理的 validation adapter。只有同一个具体语义卡点已经持续非常久、经过多种实质不同的方法和多轮实际验证仍无法闭合，并且有证据表明当前 Lean 表示/实现本身是主要障碍时，才允许重写受影响的 Lean translation。重写必须仍忠实于 v0.6 source 和已批准 representation policy；重写后相关 snapshot、artifact、certificate 和 acceptance evidence 一律视为失效并重新验证。不得为了“更容易证明”而改变 source semantics。
8. 文件 acceptance 来自正式 validator/publication。不能以本 JSON 的参考状态、一个文件存在、一个历史 PASS，或单纯 `Print Assumptions` 没列出某个常量代替完整检查。

**零声明文件不是自动完成。** 要检查其 imports/re-exports、notation、instances/coercions 和可观察接口，并获得符合项目规则的模块验收记录。没有适用 gate 时记录缺口，不把 0/0 当成证明，也不凭这份计划发明一种自动放行状态。

**当前增量脚本仍是 List 专用。** `check_utility_list_batch.sh` 中仍指定 List snapshot 和 ListBatch certificate modules。后续文件应使用已有对应入口，或复用 common 层建立最小文件配置/入口；不能只把路径换成另一个 `.lean` 就声称完成验证。不要为此启动无关的大型 pipeline 重构。

## 确定性顺序

这是一条选定的合法拓扑线性顺序，不声称是唯一顺序或最优耗时顺序：

- 从 Rank 1 开始依次检查；已完整 accepted 的文件跳过，执行下一个尚未完整完成且依赖 READY 的文件。
- Rank 12–21：关闭 `util/all.v` 的剩余依赖。
- Rank 22–28：Job→Arrival→Schedule→Service→Ready→Behavior aggregation，再做 processor supply。
- Rank 29–32：完成四个没有被 `util/all.v` 统一纳入的 utility 模块。
- Rank 33–343：剩余 main 文件按 `(数值 layer, 大小写敏感的完整 source path)` 排列。
- Rank 344–357：refinement 预留顺序，同样按 layer/path 排列，但**不会因 main 完成而自动获准启动**。

前32项允许层号回落：这里依赖检查优先于全局“必须先做完整个低层”的人为屏障。后半不按 Model/Analysis/Results 目录分别清空，因为全图存在跨目录回依赖。

## 前置主线

数字是 authoritative public declaration 数，不把 Lean helpers、生成的 projections/recursors 再计为源声明。参考状态仅绑定上面的 review commit。

| Rank | Source file | Declarations | 执行说明 |
|---:|---|---:|---|
| 1 | `behavior/time.v` | 2 | review时已整文件验收；检查当前证据有效后跳过。 |
| 2 | `util/tactics.v` | 2 | review时已整文件验收；检查当前证据有效后跳过。 |
| 3 | `util/notation.v` | 1 | review时已整文件验收；检查当前证据有效后跳过。 |
| 4 | `util/rel.v` | 3 | review时已整文件验收；检查当前证据有效后跳过。 |
| 5 | `util/seqset.v` | 3 | review时已整文件验收；检查当前证据有效后跳过。 |
| 6 | `util/subadditivity.v` | 6 | review时已整文件验收；检查当前证据有效后跳过。 |
| 7 | `util/supremum.v` | 7 | review时已整文件验收；检查当前证据有效后跳过。 |
| 8 | `util/nat.v` | 2 | review时已整文件验收；检查当前证据有效后跳过。 |
| 9 | `util/unit_growth.v` | 12 | review时已整文件验收；检查当前证据有效后跳过。 |
| 10 | `util/search_arg.v` | 8 | review时已整文件验收；检查当前证据有效后跳过。 |
| 11 | `util/list.v` | 57 | 大文件；若尚未整文件 accepted，则按语义簇完成并最终 whole-file 验收。 |
| 12 | `util/sum.v` | 25 | 大文件；按语义簇拆分并最终 whole-file 验收；保留现有 review gates。 |
| 13 | `util/epsilon.v` | 0 | notation/模块审计；0项不等于自动 accepted。 |
| 14 | `util/bigop.v` | 1 | 整文件；泛型 bigop 的运算/单位元/laws 边界需要预检。 |
| 15 | `util/setoid.v` | 3 | 整文件；先于 minmax。 |
| 16 | `util/poet.v` | 1 | 整文件；复用现有 List/zip 等关系。 |
| 17 | `util/bigcat.v` | 13 | 整文件；bigcat 聚合对应需预检。 |
| 18 | `util/minmax.v` | 10 | 整文件；List/Nat/Notation/Setoid 均应已验收。 |
| 19 | `util/div_mod.v` | 15 | 整文件目标；division/modulo 等新运算先预检。 |
| 20 | `util/nondecreasing.v` | 33 | 按语义簇拆分，但文件整体收尾后才放行 all。 |
| 21 | `util/all.v` | 0 | 聚合模块审计；18个直接文件依赖全部 accepted 后才收尾。 |
| 22 | `behavior/job.v` | 5 | 整文件；保持 eqType/DecidableEq 与 class 字段边界。 |
| 23 | `behavior/arrival_sequence.v` | 14 | 整文件；保留 arrival sequence 顺序、重复项和 Bool 观察。 |
| 24 | `behavior/schedule.v` | 5 | 先 ProcessorState 表示证书，再派生定义；不是只有5项就容易。 |
| 25 | `behavior/service.v` | 12 | 整文件目标；Schedule 验收之后处理实际 service/completion 计算链。 |
| 26 | `behavior/ready.v` | 7 | 整文件；审计 JobReady 与 schedule validity 的完整契约。 |
| 27 | `behavior/all.v` | 0 | 聚合模块审计；六个 Behavior 依赖全部 accepted。 |
| 28 | `model/processor/supply.v` | 5 | 整文件；直接依赖 schedule；不是 util/all 的门槛。 |
| 29 | `util/int.v` | 0 | imports/notation/实例接口审计；0项不自动 accepted。 |
| 30 | `util/lcmseq.v` | 5 | 整文件；LCM/整除运算预检；不阻塞之前的 util/all。 |
| 31 | `util/fixpoint.v` | 17 | 递归计算先预检；整文件优先，必要时内部拆簇。 |
| 32 | `util/superadditivity.v` | 12 | 整文件目标；检查新增 extension/算术运算，不是 util/all 的前置门槛。 |

### 几个不能漏掉的门槛

- `util/minmax.v` 直接依赖 `util/setoid.v`；`util/nondecreasing.v` 直接依赖 `util/epsilon.v`。
- `behavior/job.v` 直接依赖 `behavior/time.v` 与 `util/all.v`；只有这两个直接依赖都已有效验收时 Job 才 READY。
- `util/all.v` 的18个直接依赖为：`bigcat, bigop, div_mod, epsilon, list, minmax, nat, nondecreasing, notation, poet, rel, search_arg, seqset, setoid, sum, supremum, tactics, unit_growth`（均为 `util/*.v`）。
- `util/subadditivity.v` 是 all 的间接前置（经 div_mod）；`lcmseq, int, fixpoint, superadditivity` 不属于 all 的这条依赖闭包，不人为增加这四个门槛。
- `ProcessorState` 按已批准的 nested State/Core、有限性/判等、per-core scheduled/supply/service 与两条 laws 实现；`scheduled_in/supply_in/service_in` 仍是派生定义。未闭合这个边界，不启动 Service 下游。

## 全部文件顺序：MAIN

列表中的路径全是官方 v0.6 source identity；对应 Lean 路径/声明从现有 mapping 解析，不能用旧 v0.4 名称或机械改后缀替代。

```text
Rank Layer Source file Public declarations
001  L00  behavior/time.v  2
002  L00  util/tactics.v  2
003  L00  util/notation.v  1
004  L00  util/rel.v  3
005  L00  util/seqset.v  3
006  L00  util/subadditivity.v  6
007  L00  util/supremum.v  7
008  L01  util/nat.v  2
009  L01  util/unit_growth.v  12
010  L01  util/search_arg.v  8
011  L01  util/list.v  57
012  L02  util/sum.v  25
013  L00  util/epsilon.v  0
014  L00  util/bigop.v  1
015  L00  util/setoid.v  3
016  L02  util/poet.v  1
017  L02  util/bigcat.v  13
018  L02  util/minmax.v  10
019  L02  util/div_mod.v  15
020  L02  util/nondecreasing.v  33
021  L03  util/all.v  0
022  L04  behavior/job.v  5
023  L05  behavior/arrival_sequence.v  14
024  L06  behavior/schedule.v  5
025  L07  behavior/service.v  12
026  L08  behavior/ready.v  7
027  L09  behavior/all.v  0
028  L07  model/processor/supply.v  5
029  L00  util/int.v  0
030  L01  util/lcmseq.v  5
031  L03  util/fixpoint.v  17
032  L02  util/superadditivity.v  12
033  L04  implementation/definitions/extrapolated_arrival_curve.v  21
034  L05  analysis/definitions/sbf/sbf.v  1
035  L05  implementation/definitions/arrival_bound.v  3
036  L05  implementation/facts/extrapolated_arrival_curve.v  10
037  L08  analysis/definitions/completion_sequence.v  1
038  L08  analysis/definitions/finish_time.v  5
039  L08  analysis/definitions/sbf/average.v  2
040  L08  analysis/definitions/sbf/periodic.v  2
041  L08  analysis/definitions/sbf/pred.v  5
042  L08  analysis/definitions/service.v  2
043  L09  analysis/definitions/sbf/plain.v  3
044  L09  analysis/definitions/schedule_prefix.v  3
045  L10  analysis/definitions/job_response_time.v  1
046  L10  analysis/transform/swap.v  2
047  L10  model/job/properties.v  2
048  L10  model/processor/ideal.v  2
049  L10  model/processor/ideal_uni_exceed.v  7
050  L10  model/processor/overheads.v  13
051  L10  model/processor/platform_properties.v  6
052  L10  model/processor/restricted_supply.v  5
053  L10  model/processor/spin.v  5
054  L10  model/processor/varspeed.v  5
055  L10  model/readiness/basic.v  0
056  L10  model/readiness/jitter.v  2
057  L10  model/schedule/edf.v  2
058  L10  model/schedule/nonpreemptive.v  1
059  L10  model/schedule/scheduled.v  3
060  L10  model/schedule/work_conserving.v  2
061  L10  model/task/concept.v  19
062  L11  analysis/abstract/definitions.v  15
063  L11  analysis/abstract/search_space.v  6
064  L11  analysis/definitions/overheads/schedule_change.v  4
065  L11  analysis/definitions/task_schedule.v  7
066  L11  analysis/facts/behavior/supply.v  16
067  L11  analysis/facts/model/ideal_uni_exceed.v  7
068  L11  analysis/facts/model/restricted_supply/schedule.v  3
069  L11  analysis/facts/model/task_cost.v  2
070  L11  analysis/facts/model/uniprocessor.v  1
071  L11  implementation/definitions/generic_scheduler.v  4
072  L11  model/priority/definitions.v  20
073  L11  model/schedule/tdma.v  15
074  L11  model/task/absolute_deadline.v  1
075  L11  model/task/arrival/sporadic.v  5
076  L11  model/task/arrivals.v  13
077  L11  model/task/jitter.v  3
078  L12  analysis/abstract/restricted_supply/busy_sbf.v  2
079  L12  analysis/definitions/infinite_jobs.v  1
080  L12  analysis/definitions/readiness_interference.v  3
081  L12  analysis/facts/SBF.v  3
082  L12  analysis/facts/behavior/arrivals.v  45
083  L12  analysis/facts/tdma.v  6
084  L12  model/priority/coercion.v  10
085  L12  model/task/arrival/curves.v  14
086  L12  model/task/arrival/request_bound_functions.v  8
087  L12  model/task/arrival/task_max_inter_arrival.v  5
088  L12  model/task/sequentiality.v  2
089  L13  analysis/definitions/delay_propagation.v  7
090  L13  analysis/facts/model/scheduled.v  14
091  L13  analysis/facts/model/task_arrivals.v  23
092  L13  implementation/definitions/maximal_arrival_sequence.v  7
093  L13  model/composite/valid_task_arrival_sequence.v  6
094  L13  model/priority/classes.v  0
095  L13  model/readiness/sequential.v  0
096  L13  model/task/arrival/curve_as_rbf.v  12
097  L14  analysis/definitions/always_higher_priority.v  2
098  L14  analysis/definitions/carry_in.v  1
099  L14  analysis/definitions/overheads/priority_bump.v  1
100  L14  analysis/definitions/priority/classes.v  1
101  L14  analysis/definitions/work_bearing_readiness.v  1
102  L14  analysis/facts/behavior/service.v  57
103  L14  analysis/facts/delay_propagation.v  12
104  L14  analysis/facts/job_index.v  21
105  L14  analysis/facts/model/arrival_curves.v  3
106  L14  analysis/facts/model/sbf/average.v  3
107  L14  analysis/facts/model/sbf/periodic.v  9
108  L14  analysis/facts/sporadic/arrival_bound.v  4
109  L14  implementation/facts/maximal_arrival_sequence.v  14
110  L14  model/aggregate/service_of_jobs.v  8
111  L14  model/aggregate/workload.v  8
112  L14  model/preemption/parameter.v  14
113  L14  model/priority/deadline_monotonic.v  4
114  L14  model/priority/edf.v  4
115  L14  model/priority/fifo.v  4
116  L14  model/priority/gel.v  7
117  L14  model/priority/numeric_fixed_priority.v  7
118  L14  model/priority/rate_monotonic.v  4
119  L15  analysis/definitions/interference.v  15
120  L15  analysis/definitions/progress.v  4
121  L15  analysis/definitions/readiness.v  3
122  L15  analysis/facts/behavior/completion.v  30
123  L15  analysis/facts/model/ideal/schedule.v  19
124  L15  analysis/facts/model/ideal/service_of_jobs.v  2
125  L15  analysis/facts/model/task_schedule.v  10
126  L15  analysis/facts/model/workload.v  17
127  L15  analysis/facts/priority/classes.v  22
128  L15  analysis/facts/sporadic/arrival_times.v  3
129  L15  implementation/definitions/task.v  15
130  L15  model/preemption/fully_nonpreemptive.v  0
131  L15  model/preemption/fully_preemptive.v  0
132  L15  model/preemption/limited_preemptive.v  5
133  L15  model/priority/elf.v  1
134  L15  model/processor/multiprocessor.v  6
135  L15  model/schedule/limited_preemptive.v  1
136  L15  model/schedule/preemption_time.v  1
137  L15  model/task/arrival/sporadic_as_curve.v  5
138  L15  model/task/preemption/parameters.v  13
139  L16  analysis/definitions/blocking_bound/edf.v  2
140  L16  analysis/definitions/blocking_bound/elf.v  1
141  L16  analysis/definitions/blocking_bound/fp.v  1
142  L16  analysis/definitions/busy_interval/classical.v  5
143  L16  analysis/definitions/request_bound_function.v  6
144  L16  analysis/definitions/schedulability.v  6
145  L16  analysis/definitions/service_inversion/pred.v  4
146  L16  analysis/facts/behavior/deadlines.v  4
147  L16  analysis/facts/preemption/job/preemptive.v  3
148  L16  analysis/facts/priority/jlfp_with_fp.v  8
149  L16  analysis/facts/readiness/backlogged.v  5
150  L16  analysis/facts/readiness/basic.v  3
151  L16  analysis/facts/readiness/sequential.v  4
152  L16  analysis/facts/sporadic/arrival_sequence.v  7
153  L16  analysis/facts/transform/replace_at.v  7
154  L16  implementation/definitions/job_constructor.v  4
155  L16  model/readiness/suspension.v  4
156  L16  model/schedule/priority_driven.v  3
157  L16  model/task/preemption/floating_nonpreemptive.v  2
158  L16  model/task/preemption/fully_nonpreemptive.v  1
159  L16  model/task/preemption/fully_preemptive.v  1
160  L16  model/task/preemption/limited_preemptive.v  8
161  L17  analysis/abstract/restricted_supply/busy_prefix.v  2
162  L17  analysis/definitions/busy_interval/edf_pi_bound.v  1
163  L17  analysis/definitions/demand_bound_function.v  2
164  L17  analysis/definitions/priority_inversion.v  8
165  L17  analysis/definitions/sbf/busy.v  2
166  L17  analysis/definitions/service_inversion/busy_prefix.v  2
167  L17  analysis/definitions/service_inversion/readiness_aware.v  3
168  L17  analysis/definitions/tardiness.v  1
169  L17  analysis/definitions/workload/bounded.v  1
170  L17  analysis/definitions/workload/edf_athep_bound.v  1
171  L17  analysis/definitions/workload/elf_athep_bound.v  4
172  L17  analysis/facts/behavior/all.v  0
173  L17  analysis/facts/busy_interval/quiet_time.v  4
174  L17  analysis/facts/edf_definitions.v  3
175  L17  analysis/facts/jitter.v  14
176  L17  analysis/facts/model/preemption.v  14
177  L17  analysis/facts/preemption/task/preemptive.v  2
178  L17  analysis/facts/suspension.v  11
179  L17  analysis/facts/transform/swaps.v  22
180  L17  implementation/definitions/ideal_uni_scheduler.v  5
181  L17  implementation/facts/generic_schedule.v  6
182  L17  implementation/facts/job_constructor.v  6
183  L17  model/task/suspension/dynamic.v  2
184  L18  analysis/facts/completes_at.v  5
185  L18  analysis/facts/model/dynamic_suspension.v  2
186  L18  analysis/facts/model/exceedance/SBF.v  4
187  L18  analysis/facts/model/rbf.v  27
188  L18  analysis/facts/model/sequential.v  3
189  L18  analysis/facts/model/service_of_jobs.v  22
190  L18  analysis/facts/preemption/job/nonpreemptive.v  4
191  L18  analysis/facts/preemption/rtc_threshold/job_preemptable.v  14
192  L18  analysis/facts/priority/inversion.v  7
193  L18  analysis/facts/priority/sequential.v  1
194  L18  analysis/transform/prefix.v  3
195  L18  implementation/facts/ideal_uni/preemption_aware.v  10
196  L18  model/task/offset.v  7
197  L19  analysis/abstract/iw_auxiliary.v  6
198  L19  analysis/abstract/restricted_supply/search_space/fp.v  2
199  L19  analysis/facts/busy_interval/existence.v  14
200  L19  analysis/facts/interference.v  17
201  L19  analysis/facts/model/dbf.v  8
202  L19  analysis/facts/model/ideal/priority_inversion.v  4
203  L19  analysis/facts/model/offset.v  2
204  L19  analysis/facts/preemption/job/limited.v  10
205  L19  analysis/facts/preemption/rtc_threshold/nonpreemptive.v  3
206  L19  analysis/facts/preemption/rtc_threshold/preemptive.v  1
207  L19  analysis/facts/preemption/task/nonpreemptive.v  2
208  L19  analysis/facts/priority/edf.v  5
209  L19  analysis/facts/priority/gel.v  6
210  L19  analysis/facts/workload/edf_athep_bound.v  4
211  L19  analysis/facts/workload/elf_athep_bound.v  6
212  L19  analysis/transform/edf_trans.v  6
213  L19  analysis/transform/wc_trans.v  6
214  L19  implementation/facts/ideal_uni/prio_aware.v  5
215  L19  model/task/arrival/periodic.v  5
216  L19  results/transfer_schedulability/criterion.v  40
217  L20  analysis/abstract/busy_interval.v  15
218  L20  analysis/abstract/restricted_supply/search_space/edf.v  2
219  L20  analysis/abstract/restricted_supply/search_space/elf.v  2
220  L20  analysis/definitions/hyperperiod.v  7
221  L20  analysis/facts/busy_interval/carry_in.v  9
222  L20  analysis/facts/busy_interval/hep_at_pt.v  8
223  L20  analysis/facts/preemption/task/floating.v  2
224  L20  analysis/facts/preemption/task/limited.v  2
225  L20  analysis/facts/priority/elf.v  8
226  L20  analysis/facts/readiness_interference.v  2
227  L20  analysis/facts/transform/edf_opt.v  43
228  L20  analysis/facts/transform/wc_correctness.v  33
229  L20  model/task/arrival/periodic_as_sporadic.v  5
230  L20  results/transfer_schedulability/paper_model.v  19
231  L21  analysis/abstract/lower_bound_on_service.v  3
232  L21  analysis/facts/busy_interval/arrival.v  3
233  L21  analysis/facts/busy_interval/pi.v  24
234  L21  analysis/facts/periodic/arrival_separation.v  3
235  L21  analysis/facts/preemption/rtc_threshold/floating.v  1
236  L21  analysis/facts/preemption/rtc_threshold/limited.v  3
237  L21  analysis/facts/transform/edf_wc.v  11
238  L21  model/task/arrival/example.v  0
239  L21  results/generality/elf.v  3
240  L22  analysis/abstract/abstract_rta.v  14
241  L22  analysis/facts/blocking_bound/edf.v  1
242  L22  analysis/facts/blocking_bound/elf.v  1
243  L22  analysis/facts/blocking_bound/fp.v  1
244  L22  analysis/facts/busy_interval/pi_bound.v  1
245  L22  analysis/facts/busy_interval/pi_cond.v  1
246  L22  analysis/facts/busy_interval/service_inversion.v  12
247  L22  analysis/facts/model/overheads/schedule.v  6
248  L22  analysis/facts/periodic/max_inter_arrival.v  3
249  L22  results/optimality/edf.v  4
250  L23  analysis/abstract/IBF/supply.v  3
251  L23  analysis/abstract/IBF/task.v  18
252  L23  analysis/abstract/ideal/abstract_rta.v  2
253  L23  analysis/facts/busy_interval/all.v  0
254  L23  analysis/facts/model/overheads/priority_bump.v  3
255  L23  analysis/facts/model/overheads/schedule_change.v  6
256  L23  analysis/facts/periodic/arrival_times.v  3
257  L24  analysis/abstract/IBF/supply_task.v  3
258  L24  analysis/abstract/ideal/abstract_seq_rta.v  2
259  L24  analysis/abstract/ideal/iw_instantiation.v  20
260  L24  analysis/abstract/restricted_supply/abstract_rta.v  10
261  L24  analysis/facts/model/overheads/schedule_change_bound.v  3
262  L24  analysis/facts/periodic/task_arrivals_size.v  8
263  L24  analysis/facts/priority/fifo.v  12
264  L24  model/processor/overhead_resource_model.v  10
265  L25  analysis/abstract/ideal/cumulative_bounds.v  2
266  L25  analysis/abstract/restricted_supply/abstract_seq_rta.v  3
267  L25  analysis/abstract/restricted_supply/iw_instantiation.v  17
268  L25  analysis/abstract/restricted_supply/iw_readiness.v  18
269  L25  analysis/abstract/restricted_supply/search_space/fifo.v  2
270  L25  analysis/facts/hyperperiod.v  10
271  L25  analysis/facts/model/overheads/blackout_bound.v  11
272  L25  analysis/facts/priority/fifo_ahep_bound.v  1
273  L25  results/generality/gel.v  5
274  L25  results/rta/ideal/fp/bounded_pi.v  6
275  L26  analysis/abstract/restricted_supply/bounded_bi/aux.v  3
276  L26  analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v  1
277  L26  analysis/abstract/restricted_supply/task_ibf_readiness.v  2
278  L26  analysis/abstract/restricted_supply/task_intra_interference_bound.v  2
279  L26  analysis/facts/model/overheads/sbf/fifo.v  6
280  L26  analysis/facts/model/overheads/sbf/fp.v  6
281  L26  analysis/facts/model/overheads/sbf/jlfp.v  6
282  L26  analysis/facts/shifted_job_costs.v  3
283  L26  results/rta/ideal/edf/bounded_pi.v  8
284  L26  results/rta/ideal/elf/bounded_pi.v  22
285  L26  results/rta/ideal/fifo/bounded_nps.v  8
286  L26  results/rta/ideal/fp/bounded_nps.v  3
287  L26  results/rta/ideal/fp/nonseq/bounded_pi.v  10
288  L26  results/rta/ideal/gel/bounded_pi.v  10
289  L27  analysis/abstract/restricted_supply/bounded_bi/edf.v  2
290  L27  analysis/abstract/restricted_supply/bounded_bi/elf.v  1
291  L27  analysis/abstract/restricted_supply/bounded_bi/fp.v  1
292  L27  analysis/abstract/restricted_supply/bounded_bi/jlfp.v  1
293  L27  results/rta/ideal/edf/bounded_nps.v  5
294  L27  results/rta/ideal/fp/floating_nonpreemptive.v  1
295  L27  results/rta/ideal/fp/fully_nonpreemptive.v  1
296  L27  results/rta/ideal/fp/fully_preemptive.v  1
297  L27  results/rta/ideal/fp/limited_preemptive.v  1
298  L28  results/rta/arm/edf/floating_nonpreemptive.v  3
299  L28  results/rta/arm/edf/fully_nonpreemptive.v  3
300  L28  results/rta/arm/edf/fully_preemptive.v  3
301  L28  results/rta/arm/edf/limited_preemptive.v  3
302  L28  results/rta/arm/fifo/bounded_nps.v  3
303  L28  results/rta/arm/fp/floating_nonpreemptive.v  3
304  L28  results/rta/arm/fp/fully_nonpreemptive.v  3
305  L28  results/rta/arm/fp/fully_preemptive.v  3
306  L28  results/rta/arm/fp/limited_preemptive.v  3
307  L28  results/rta/exc/fp/fully_nonpreemptive.v  3
308  L28  results/rta/ideal/edf/floating_nonpreemptive.v  1
309  L28  results/rta/ideal/edf/fully_nonpreemptive.v  1
310  L28  results/rta/ideal/edf/fully_preemptive.v  1
311  L28  results/rta/ideal/edf/limited_preemptive.v  1
312  L28  results/rta/ideal/fp/comp/fully_preemptive.v  1
313  L28  results/rta/ovh/edf/floating_nonpreemptive.v  3
314  L28  results/rta/ovh/edf/fully_nonpreemptive.v  3
315  L28  results/rta/ovh/edf/fully_preemptive.v  3
316  L28  results/rta/ovh/edf/limited_preemptive.v  3
317  L28  results/rta/ovh/fifo/bounded_nps.v  3
318  L28  results/rta/ovh/fp/floating_nonpreemptive.v  3
319  L28  results/rta/ovh/fp/fully_nonpreemptive.v  3
320  L28  results/rta/ovh/fp/fully_preemptive.v  3
321  L28  results/rta/ovh/fp/limited_preemptive.v  3
322  L28  results/rta/prm/edf/floating_nonpreemptive.v  3
323  L28  results/rta/prm/edf/fully_nonpreemptive.v  3
324  L28  results/rta/prm/edf/fully_preemptive.v  3
325  L28  results/rta/prm/edf/limited_preemptive.v  3
326  L28  results/rta/prm/fifo/bounded_nps.v  3
327  L28  results/rta/prm/fp/floating_nonpreemptive.v  3
328  L28  results/rta/prm/fp/fully_nonpreemptive.v  3
329  L28  results/rta/prm/fp/fully_preemptive.v  3
330  L28  results/rta/prm/fp/limited_preemptive.v  3
331  L28  results/rta/rs/edf/floating_nonpreemptive.v  3
332  L28  results/rta/rs/edf/fully_nonpreemptive.v  3
333  L28  results/rta/rs/edf/fully_preemptive.v  3
334  L28  results/rta/rs/edf/limited_preemptive.v  3
335  L28  results/rta/rs/elf/floating_nonpreemptive.v  3
336  L28  results/rta/rs/elf/fully_nonpreemptive.v  3
337  L28  results/rta/rs/elf/fully_preemptive.v  3
338  L28  results/rta/rs/elf/limited_preemptive.v  3
339  L28  results/rta/rs/fifo/bounded_nps.v  3
340  L28  results/rta/rs/fp/floating_nonpreemptive.v  3
341  L28  results/rta/rs/fp/fully_nonpreemptive.v  3
342  L28  results/rta/rs/fp/fully_preemptive.v  3
343  L28  results/rta/rs/fp/limited_preemptive.v  3
```

## Deferred：refinement / CoqEAL 边界

以下14项保留在完整范围中，不计为已完成、也不从分母删除。启动前需要明确批准扩展范围，并解决对应外部构建、source elaboration 和语义验证边界。

```text
Rank Layer Source file Public declarations
344  L16  implementation/refinements/refinements.v  42
345  L17  implementation/refinements/arrival_bound.v  36
346  L18  implementation/refinements/task.v  24
347  L19  implementation/refinements/arrival_curve.v  20
348  L20  implementation/refinements/EDF/nonpreemptive_sched.v  9
349  L20  implementation/refinements/EDF/preemptive_sched.v  6
350  L20  implementation/refinements/FP/nonpreemptive_sched.v  9
351  L20  implementation/refinements/FP/preemptive_sched.v  6
352  L20  implementation/refinements/arrival_curve_prefix.v  4
353  L21  implementation/refinements/fast_search_space_computation.v  8
354  L27  implementation/refinements/FP/fast_search_space.v  10
355  L28  implementation/refinements/EDF/fast_search_space.v  14
356  L28  implementation/refinements/FP/refinements.v  28
357  L29  implementation/refinements/EDF/refinements.v  23
```

## 核对范围与运行前检查

`Validation/scripts/update_v06_translation_order.py` 已在当前 repo 中读取完整
authoritative CSV/JSON，并核对 357 个文件精确覆盖、rank 1–357 唯一连续、
343/14 main/refinement 分组、全部 1359 条内部依赖边、DAG 层号、0 个 cycle，
以及 2439 个 public declarations。每行 declaration 数直接由
`declaration_inventory.csv` 聚合生成；检查模式会拒绝过期数量。当前审计为
`PASS`，没有反向 dependency edge 或 layer mismatch，机器证据位于
`Validation/planning/v06_pipeline/file_translation_order_audit.json`。这次顺序
审计不需要也没有重跑无关 Lean/Rocq validation。

本计划始终让最新有效 validator 证据决定 READY/accepted。审计输出 `order_audit=PASS` 只代表顺序检查通过，绝不代表任何翻译或证书通过。

## 依据文件（相对 Prosa-Shunqi）

- `Validation/planning/v06_dependency/file_layers.csv`
- `Validation/planning/v06_dependency/file_inventory.csv`
- `Validation/planning/v06_dependency/declaration_inventory.csv`
- `Validation/planning/v06_dependency/file_dag_summary.md`
- `Validation/planning/v06_dependency/scope_manifest.json`
- `Validation/planning/v06_mapping/v06_coq_lean_mapping_policy.md`
- `Validation/planning/v06_mapping/foundational_representation_decisions.md`
- `Validation/planning/v06_pipeline/foundation_slice_2_closure_status.json`
- `Validation/planning/v06_pipeline/utility_foundation_expansion_status.json`
- `Validation/scripts/check_utility_list_batch.sh`

仓库根目录另有 `.agents/skills/prosa-v06-translation/SKILL.md`。旧 planning snapshot 保留原 provenance，不改写为本次执行记录。
