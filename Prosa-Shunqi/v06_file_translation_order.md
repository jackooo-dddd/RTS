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
3. 一个任务优先以 **whole file** 为单位。通常 ≤15 个声明整文件一批；16–20 个先检查新语义边界；>20 个按相互关联的声明组拆分。大文件内部允许分批，但整文件没收尾之前仍不能放行下游。声明 DAG 只细化文件内顺序，不替代文件 DAG。
4. 每个新 class/计算边界先做最小 actual-artifact 预检；之后收齐本文件候选并冻结 snapshot，复用 prepare→check→finalize 模式。共享的是同一冻结输入的准备产物，不是承诺整个文件永远只需要一次试验。输入变了必须重新准备。
5. 新文件优先组合已认证 correspondence DAG。缺失操作做最小、具名、可复用的证书；不复证已有 List/Nat/equality，不用 source/target 业务 theorem 自证。每项继续要求 `semantic_premises=[]`、source/target self-dependency=false、unexpected assumptions=[]，并保留准确的 foundation 分类。
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
Rank Layer Source file
001  L00  behavior/time.v
002  L00  util/tactics.v
003  L00  util/notation.v
004  L00  util/rel.v
005  L00  util/seqset.v
006  L00  util/subadditivity.v
007  L00  util/supremum.v
008  L01  util/nat.v
009  L01  util/unit_growth.v
010  L01  util/search_arg.v
011  L01  util/list.v
012  L02  util/sum.v
013  L00  util/epsilon.v
014  L00  util/bigop.v
015  L00  util/setoid.v
016  L02  util/poet.v
017  L02  util/bigcat.v
018  L02  util/minmax.v
019  L02  util/div_mod.v
020  L02  util/nondecreasing.v
021  L03  util/all.v
022  L04  behavior/job.v
023  L05  behavior/arrival_sequence.v
024  L06  behavior/schedule.v
025  L07  behavior/service.v
026  L08  behavior/ready.v
027  L09  behavior/all.v
028  L07  model/processor/supply.v
029  L00  util/int.v
030  L01  util/lcmseq.v
031  L03  util/fixpoint.v
032  L02  util/superadditivity.v
033  L04  implementation/definitions/extrapolated_arrival_curve.v
034  L05  analysis/definitions/sbf/sbf.v
035  L05  implementation/definitions/arrival_bound.v
036  L05  implementation/facts/extrapolated_arrival_curve.v
037  L08  analysis/definitions/completion_sequence.v
038  L08  analysis/definitions/finish_time.v
039  L08  analysis/definitions/sbf/average.v
040  L08  analysis/definitions/sbf/periodic.v
041  L08  analysis/definitions/sbf/pred.v
042  L08  analysis/definitions/service.v
043  L09  analysis/definitions/sbf/plain.v
044  L09  analysis/definitions/schedule_prefix.v
045  L10  analysis/definitions/job_response_time.v
046  L10  analysis/transform/swap.v
047  L10  model/job/properties.v
048  L10  model/processor/ideal.v
049  L10  model/processor/ideal_uni_exceed.v
050  L10  model/processor/overheads.v
051  L10  model/processor/platform_properties.v
052  L10  model/processor/restricted_supply.v
053  L10  model/processor/spin.v
054  L10  model/processor/varspeed.v
055  L10  model/readiness/basic.v
056  L10  model/readiness/jitter.v
057  L10  model/schedule/edf.v
058  L10  model/schedule/nonpreemptive.v
059  L10  model/schedule/scheduled.v
060  L10  model/schedule/work_conserving.v
061  L10  model/task/concept.v
062  L11  analysis/abstract/definitions.v
063  L11  analysis/abstract/search_space.v
064  L11  analysis/definitions/overheads/schedule_change.v
065  L11  analysis/definitions/task_schedule.v
066  L11  analysis/facts/behavior/supply.v
067  L11  analysis/facts/model/ideal_uni_exceed.v
068  L11  analysis/facts/model/restricted_supply/schedule.v
069  L11  analysis/facts/model/task_cost.v
070  L11  analysis/facts/model/uniprocessor.v
071  L11  implementation/definitions/generic_scheduler.v
072  L11  model/priority/definitions.v
073  L11  model/schedule/tdma.v
074  L11  model/task/absolute_deadline.v
075  L11  model/task/arrival/sporadic.v
076  L11  model/task/arrivals.v
077  L11  model/task/jitter.v
078  L12  analysis/abstract/restricted_supply/busy_sbf.v
079  L12  analysis/definitions/infinite_jobs.v
080  L12  analysis/definitions/readiness_interference.v
081  L12  analysis/facts/SBF.v
082  L12  analysis/facts/behavior/arrivals.v
083  L12  analysis/facts/tdma.v
084  L12  model/priority/coercion.v
085  L12  model/task/arrival/curves.v
086  L12  model/task/arrival/request_bound_functions.v
087  L12  model/task/arrival/task_max_inter_arrival.v
088  L12  model/task/sequentiality.v
089  L13  analysis/definitions/delay_propagation.v
090  L13  analysis/facts/model/scheduled.v
091  L13  analysis/facts/model/task_arrivals.v
092  L13  implementation/definitions/maximal_arrival_sequence.v
093  L13  model/composite/valid_task_arrival_sequence.v
094  L13  model/priority/classes.v
095  L13  model/readiness/sequential.v
096  L13  model/task/arrival/curve_as_rbf.v
097  L14  analysis/definitions/always_higher_priority.v
098  L14  analysis/definitions/carry_in.v
099  L14  analysis/definitions/overheads/priority_bump.v
100  L14  analysis/definitions/priority/classes.v
101  L14  analysis/definitions/work_bearing_readiness.v
102  L14  analysis/facts/behavior/service.v
103  L14  analysis/facts/delay_propagation.v
104  L14  analysis/facts/job_index.v
105  L14  analysis/facts/model/arrival_curves.v
106  L14  analysis/facts/model/sbf/average.v
107  L14  analysis/facts/model/sbf/periodic.v
108  L14  analysis/facts/sporadic/arrival_bound.v
109  L14  implementation/facts/maximal_arrival_sequence.v
110  L14  model/aggregate/service_of_jobs.v
111  L14  model/aggregate/workload.v
112  L14  model/preemption/parameter.v
113  L14  model/priority/deadline_monotonic.v
114  L14  model/priority/edf.v
115  L14  model/priority/fifo.v
116  L14  model/priority/gel.v
117  L14  model/priority/numeric_fixed_priority.v
118  L14  model/priority/rate_monotonic.v
119  L15  analysis/definitions/interference.v
120  L15  analysis/definitions/progress.v
121  L15  analysis/definitions/readiness.v
122  L15  analysis/facts/behavior/completion.v
123  L15  analysis/facts/model/ideal/schedule.v
124  L15  analysis/facts/model/ideal/service_of_jobs.v
125  L15  analysis/facts/model/task_schedule.v
126  L15  analysis/facts/model/workload.v
127  L15  analysis/facts/priority/classes.v
128  L15  analysis/facts/sporadic/arrival_times.v
129  L15  implementation/definitions/task.v
130  L15  model/preemption/fully_nonpreemptive.v
131  L15  model/preemption/fully_preemptive.v
132  L15  model/preemption/limited_preemptive.v
133  L15  model/priority/elf.v
134  L15  model/processor/multiprocessor.v
135  L15  model/schedule/limited_preemptive.v
136  L15  model/schedule/preemption_time.v
137  L15  model/task/arrival/sporadic_as_curve.v
138  L15  model/task/preemption/parameters.v
139  L16  analysis/definitions/blocking_bound/edf.v
140  L16  analysis/definitions/blocking_bound/elf.v
141  L16  analysis/definitions/blocking_bound/fp.v
142  L16  analysis/definitions/busy_interval/classical.v
143  L16  analysis/definitions/request_bound_function.v
144  L16  analysis/definitions/schedulability.v
145  L16  analysis/definitions/service_inversion/pred.v
146  L16  analysis/facts/behavior/deadlines.v
147  L16  analysis/facts/preemption/job/preemptive.v
148  L16  analysis/facts/priority/jlfp_with_fp.v
149  L16  analysis/facts/readiness/backlogged.v
150  L16  analysis/facts/readiness/basic.v
151  L16  analysis/facts/readiness/sequential.v
152  L16  analysis/facts/sporadic/arrival_sequence.v
153  L16  analysis/facts/transform/replace_at.v
154  L16  implementation/definitions/job_constructor.v
155  L16  model/readiness/suspension.v
156  L16  model/schedule/priority_driven.v
157  L16  model/task/preemption/floating_nonpreemptive.v
158  L16  model/task/preemption/fully_nonpreemptive.v
159  L16  model/task/preemption/fully_preemptive.v
160  L16  model/task/preemption/limited_preemptive.v
161  L17  analysis/abstract/restricted_supply/busy_prefix.v
162  L17  analysis/definitions/busy_interval/edf_pi_bound.v
163  L17  analysis/definitions/demand_bound_function.v
164  L17  analysis/definitions/priority_inversion.v
165  L17  analysis/definitions/sbf/busy.v
166  L17  analysis/definitions/service_inversion/busy_prefix.v
167  L17  analysis/definitions/service_inversion/readiness_aware.v
168  L17  analysis/definitions/tardiness.v
169  L17  analysis/definitions/workload/bounded.v
170  L17  analysis/definitions/workload/edf_athep_bound.v
171  L17  analysis/definitions/workload/elf_athep_bound.v
172  L17  analysis/facts/behavior/all.v
173  L17  analysis/facts/busy_interval/quiet_time.v
174  L17  analysis/facts/edf_definitions.v
175  L17  analysis/facts/jitter.v
176  L17  analysis/facts/model/preemption.v
177  L17  analysis/facts/preemption/task/preemptive.v
178  L17  analysis/facts/suspension.v
179  L17  analysis/facts/transform/swaps.v
180  L17  implementation/definitions/ideal_uni_scheduler.v
181  L17  implementation/facts/generic_schedule.v
182  L17  implementation/facts/job_constructor.v
183  L17  model/task/suspension/dynamic.v
184  L18  analysis/facts/completes_at.v
185  L18  analysis/facts/model/dynamic_suspension.v
186  L18  analysis/facts/model/exceedance/SBF.v
187  L18  analysis/facts/model/rbf.v
188  L18  analysis/facts/model/sequential.v
189  L18  analysis/facts/model/service_of_jobs.v
190  L18  analysis/facts/preemption/job/nonpreemptive.v
191  L18  analysis/facts/preemption/rtc_threshold/job_preemptable.v
192  L18  analysis/facts/priority/inversion.v
193  L18  analysis/facts/priority/sequential.v
194  L18  analysis/transform/prefix.v
195  L18  implementation/facts/ideal_uni/preemption_aware.v
196  L18  model/task/offset.v
197  L19  analysis/abstract/iw_auxiliary.v
198  L19  analysis/abstract/restricted_supply/search_space/fp.v
199  L19  analysis/facts/busy_interval/existence.v
200  L19  analysis/facts/interference.v
201  L19  analysis/facts/model/dbf.v
202  L19  analysis/facts/model/ideal/priority_inversion.v
203  L19  analysis/facts/model/offset.v
204  L19  analysis/facts/preemption/job/limited.v
205  L19  analysis/facts/preemption/rtc_threshold/nonpreemptive.v
206  L19  analysis/facts/preemption/rtc_threshold/preemptive.v
207  L19  analysis/facts/preemption/task/nonpreemptive.v
208  L19  analysis/facts/priority/edf.v
209  L19  analysis/facts/priority/gel.v
210  L19  analysis/facts/workload/edf_athep_bound.v
211  L19  analysis/facts/workload/elf_athep_bound.v
212  L19  analysis/transform/edf_trans.v
213  L19  analysis/transform/wc_trans.v
214  L19  implementation/facts/ideal_uni/prio_aware.v
215  L19  model/task/arrival/periodic.v
216  L19  results/transfer_schedulability/criterion.v
217  L20  analysis/abstract/busy_interval.v
218  L20  analysis/abstract/restricted_supply/search_space/edf.v
219  L20  analysis/abstract/restricted_supply/search_space/elf.v
220  L20  analysis/definitions/hyperperiod.v
221  L20  analysis/facts/busy_interval/carry_in.v
222  L20  analysis/facts/busy_interval/hep_at_pt.v
223  L20  analysis/facts/preemption/task/floating.v
224  L20  analysis/facts/preemption/task/limited.v
225  L20  analysis/facts/priority/elf.v
226  L20  analysis/facts/readiness_interference.v
227  L20  analysis/facts/transform/edf_opt.v
228  L20  analysis/facts/transform/wc_correctness.v
229  L20  model/task/arrival/periodic_as_sporadic.v
230  L20  results/transfer_schedulability/paper_model.v
231  L21  analysis/abstract/lower_bound_on_service.v
232  L21  analysis/facts/busy_interval/arrival.v
233  L21  analysis/facts/busy_interval/pi.v
234  L21  analysis/facts/periodic/arrival_separation.v
235  L21  analysis/facts/preemption/rtc_threshold/floating.v
236  L21  analysis/facts/preemption/rtc_threshold/limited.v
237  L21  analysis/facts/transform/edf_wc.v
238  L21  model/task/arrival/example.v
239  L21  results/generality/elf.v
240  L22  analysis/abstract/abstract_rta.v
241  L22  analysis/facts/blocking_bound/edf.v
242  L22  analysis/facts/blocking_bound/elf.v
243  L22  analysis/facts/blocking_bound/fp.v
244  L22  analysis/facts/busy_interval/pi_bound.v
245  L22  analysis/facts/busy_interval/pi_cond.v
246  L22  analysis/facts/busy_interval/service_inversion.v
247  L22  analysis/facts/model/overheads/schedule.v
248  L22  analysis/facts/periodic/max_inter_arrival.v
249  L22  results/optimality/edf.v
250  L23  analysis/abstract/IBF/supply.v
251  L23  analysis/abstract/IBF/task.v
252  L23  analysis/abstract/ideal/abstract_rta.v
253  L23  analysis/facts/busy_interval/all.v
254  L23  analysis/facts/model/overheads/priority_bump.v
255  L23  analysis/facts/model/overheads/schedule_change.v
256  L23  analysis/facts/periodic/arrival_times.v
257  L24  analysis/abstract/IBF/supply_task.v
258  L24  analysis/abstract/ideal/abstract_seq_rta.v
259  L24  analysis/abstract/ideal/iw_instantiation.v
260  L24  analysis/abstract/restricted_supply/abstract_rta.v
261  L24  analysis/facts/model/overheads/schedule_change_bound.v
262  L24  analysis/facts/periodic/task_arrivals_size.v
263  L24  analysis/facts/priority/fifo.v
264  L24  model/processor/overhead_resource_model.v
265  L25  analysis/abstract/ideal/cumulative_bounds.v
266  L25  analysis/abstract/restricted_supply/abstract_seq_rta.v
267  L25  analysis/abstract/restricted_supply/iw_instantiation.v
268  L25  analysis/abstract/restricted_supply/iw_readiness.v
269  L25  analysis/abstract/restricted_supply/search_space/fifo.v
270  L25  analysis/facts/hyperperiod.v
271  L25  analysis/facts/model/overheads/blackout_bound.v
272  L25  analysis/facts/priority/fifo_ahep_bound.v
273  L25  results/generality/gel.v
274  L25  results/rta/ideal/fp/bounded_pi.v
275  L26  analysis/abstract/restricted_supply/bounded_bi/aux.v
276  L26  analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v
277  L26  analysis/abstract/restricted_supply/task_ibf_readiness.v
278  L26  analysis/abstract/restricted_supply/task_intra_interference_bound.v
279  L26  analysis/facts/model/overheads/sbf/fifo.v
280  L26  analysis/facts/model/overheads/sbf/fp.v
281  L26  analysis/facts/model/overheads/sbf/jlfp.v
282  L26  analysis/facts/shifted_job_costs.v
283  L26  results/rta/ideal/edf/bounded_pi.v
284  L26  results/rta/ideal/elf/bounded_pi.v
285  L26  results/rta/ideal/fifo/bounded_nps.v
286  L26  results/rta/ideal/fp/bounded_nps.v
287  L26  results/rta/ideal/fp/nonseq/bounded_pi.v
288  L26  results/rta/ideal/gel/bounded_pi.v
289  L27  analysis/abstract/restricted_supply/bounded_bi/edf.v
290  L27  analysis/abstract/restricted_supply/bounded_bi/elf.v
291  L27  analysis/abstract/restricted_supply/bounded_bi/fp.v
292  L27  analysis/abstract/restricted_supply/bounded_bi/jlfp.v
293  L27  results/rta/ideal/edf/bounded_nps.v
294  L27  results/rta/ideal/fp/floating_nonpreemptive.v
295  L27  results/rta/ideal/fp/fully_nonpreemptive.v
296  L27  results/rta/ideal/fp/fully_preemptive.v
297  L27  results/rta/ideal/fp/limited_preemptive.v
298  L28  results/rta/arm/edf/floating_nonpreemptive.v
299  L28  results/rta/arm/edf/fully_nonpreemptive.v
300  L28  results/rta/arm/edf/fully_preemptive.v
301  L28  results/rta/arm/edf/limited_preemptive.v
302  L28  results/rta/arm/fifo/bounded_nps.v
303  L28  results/rta/arm/fp/floating_nonpreemptive.v
304  L28  results/rta/arm/fp/fully_nonpreemptive.v
305  L28  results/rta/arm/fp/fully_preemptive.v
306  L28  results/rta/arm/fp/limited_preemptive.v
307  L28  results/rta/exc/fp/fully_nonpreemptive.v
308  L28  results/rta/ideal/edf/floating_nonpreemptive.v
309  L28  results/rta/ideal/edf/fully_nonpreemptive.v
310  L28  results/rta/ideal/edf/fully_preemptive.v
311  L28  results/rta/ideal/edf/limited_preemptive.v
312  L28  results/rta/ideal/fp/comp/fully_preemptive.v
313  L28  results/rta/ovh/edf/floating_nonpreemptive.v
314  L28  results/rta/ovh/edf/fully_nonpreemptive.v
315  L28  results/rta/ovh/edf/fully_preemptive.v
316  L28  results/rta/ovh/edf/limited_preemptive.v
317  L28  results/rta/ovh/fifo/bounded_nps.v
318  L28  results/rta/ovh/fp/floating_nonpreemptive.v
319  L28  results/rta/ovh/fp/fully_nonpreemptive.v
320  L28  results/rta/ovh/fp/fully_preemptive.v
321  L28  results/rta/ovh/fp/limited_preemptive.v
322  L28  results/rta/prm/edf/floating_nonpreemptive.v
323  L28  results/rta/prm/edf/fully_nonpreemptive.v
324  L28  results/rta/prm/edf/fully_preemptive.v
325  L28  results/rta/prm/edf/limited_preemptive.v
326  L28  results/rta/prm/fifo/bounded_nps.v
327  L28  results/rta/prm/fp/floating_nonpreemptive.v
328  L28  results/rta/prm/fp/fully_nonpreemptive.v
329  L28  results/rta/prm/fp/fully_preemptive.v
330  L28  results/rta/prm/fp/limited_preemptive.v
331  L28  results/rta/rs/edf/floating_nonpreemptive.v
332  L28  results/rta/rs/edf/fully_nonpreemptive.v
333  L28  results/rta/rs/edf/fully_preemptive.v
334  L28  results/rta/rs/edf/limited_preemptive.v
335  L28  results/rta/rs/elf/floating_nonpreemptive.v
336  L28  results/rta/rs/elf/fully_nonpreemptive.v
337  L28  results/rta/rs/elf/fully_preemptive.v
338  L28  results/rta/rs/elf/limited_preemptive.v
339  L28  results/rta/rs/fifo/bounded_nps.v
340  L28  results/rta/rs/fp/floating_nonpreemptive.v
341  L28  results/rta/rs/fp/fully_nonpreemptive.v
342  L28  results/rta/rs/fp/fully_preemptive.v
343  L28  results/rta/rs/fp/limited_preemptive.v
```

## Deferred：refinement / CoqEAL 边界

以下14项保留在完整范围中，不计为已完成、也不从分母删除。启动前需要明确批准扩展范围，并解决对应外部构建、source elaboration 和语义验证边界。

```text
Rank Layer Source file
344  L16  implementation/refinements/refinements.v
345  L17  implementation/refinements/arrival_bound.v
346  L18  implementation/refinements/task.v
347  L19  implementation/refinements/arrival_curve.v
348  L20  implementation/refinements/EDF/nonpreemptive_sched.v
349  L20  implementation/refinements/EDF/preemptive_sched.v
350  L20  implementation/refinements/FP/nonpreemptive_sched.v
351  L20  implementation/refinements/FP/preemptive_sched.v
352  L20  implementation/refinements/arrival_curve_prefix.v
353  L21  implementation/refinements/fast_search_space_computation.v
354  L27  implementation/refinements/FP/fast_search_space.v
355  L28  implementation/refinements/EDF/fast_search_space.v
356  L28  implementation/refinements/FP/refinements.v
357  L29  implementation/refinements/EDF/refinements.v
```

## 核对范围与运行前检查

本次逐段读取了357个文件的路径和层级，单独读取了前置主线与 deferred 相关46个文件的全部直接依赖（111条），并对交付的顺序做了节点唯一性、范围和这些已读依赖的程序检查。其余 main 按 authoritative layer/path 排列；deferred 的直接下游均仍在 deferred 区域，因此推迟它们不切断 main 的前置。

**本次没有在完整本地 repo 上执行全部1359条边的审计，也没有重跑 Lean/Rocq。** 附带脚本在 agent 的实际 repo 中读取完整 CSV 后，会逐一检查全部1359条边、357文件精确覆盖、层级、343/14分组、2439个声明及输入 hash；这一步必须在执行计划前通过。11项本地单元测试检查了正常排序及反向依赖、遗漏、重复、错误层级、主线依赖 deferred、CSV 引号解析、hash 变化等拒绝路径；它们不是全仓库验证的替代品。

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
