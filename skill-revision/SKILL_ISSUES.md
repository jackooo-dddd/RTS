# Skill 本身的问题与规则边界

这里集中记录从 Lean 迁移批注中分离出来的问题：即使继续使用原来的 Rocq/Coq，也需要检查这些规则或说明。它们不是换成 Lean 才产生的差异。

以下区分“规则过强”和“适用范围需要说清楚”，不把项目选择的证明风格直接判成错误。本次只移走相关批注和灰色标记，原英文规则、代码、元数据与链接都保留；下面的建议尚未实施。

## count-bridging

### 1. 把失败症状直接当成已经查明的原因

**位置：**[Problem Shape](count-bridging/SKILL.md#lean-review-problem-shape)、[Boundary Failure Signs](count-bridging/SKILL.md#lean-review-bool-prop)、[Failure Signatures For This Skill](count-bridging/SKILL.md#lean-review-failure-signatures)。

**代表原句：**

> The root cause is not that one specific lemma is missing. The branch crossed the bool/Prop boundary without deciding which layer should own the rest of the proof.

> The branch is not yet in the expected indicator-sum head form.

> The arithmetic step is too early; the count layer or the bool-to-Prop bridge is not finished.

**问题：**症状表把几个候选原因写成了确定结论：改写失败就认定表示没有整理好或缺桥接，不等式失败就归因于跨层。具体案例可能确实如此，但原文没有说明需要哪些目标、类型或执行结果才能确认原因；只凭报错或失败阶段还不足以排除其他解释。

**建议：**把“原因就是……”改成“优先检查是否……”，为每个候选原因列出确认条件；先检查当前表达式、实际类型、定义展开和改写方向，再决定要补数学前提、连接等式还是调整证明步骤。

## failure-signature

### 1. 看不见等式左侧，就要求新增桥接引理

**位置：**[Practical Rule](failure-signature/SKILL.md#lean-review-4)、[Common Messages](failure-signature/SKILL.md#lean-review-2)。

**代表原句：**

> If the answer is no, add a bridge lemma instead of trying another algebraic rewrite.

**问题：**把“没有按字面显示某个表达式”直接当成“必须新增桥接引理”，要求过强。定义展开后可能已经能匹配，失败也可能只是类型或改写方向不对；这些情况在原证明环境中同样存在。

**建议：**保留记录当前表达式和候选引理的检查表，但把字面出现当观察项；先核对定义等同、类型、作用位置与方向，确认确实缺少连接等式时才补引理。不要要求所有表达式都先显示为某个固定字面形状。

### 2. 把报错直接等同于缺少某个整理步骤

**位置：**[Failure Signatures](failure-signature/SKILL.md)、[Common Messages](failure-signature/SKILL.md#lean-review-2)。

**代表原句：**

> This reference maps common Coq and ssreflect rewrite errors to the missing normalization step.

> The goal is no longer a standard ordinal big operator head.

**问题：**速查表把错误文字与单个原因直接绑定，还把处理范围说成寻找“缺少的规范化步骤”。一般的失败信息不能单独证明目标已离开某种形式，或证明发生了表示漂移；这些更适合作为检查线索。

**建议：**把“它意味着什么”写成“可能原因与核实条件”。记录当时的目标、引理类型和失败步骤，用这些证据确认原因后再选择动作；规范化只作为一种可能的修复路线。

## math

### 1. 把字面匹配当成改写的硬门槛

**位置：**[Core Rule](math/SKILL.md#lean-review-2)、[Procedure](math/SKILL.md#lean-review-3)、[Bigop Endgame Discipline](math/SKILL.md#lean-review-6)、[Anti-Patterns](math/SKILL.md#lean-review-10)、[Minimal Debug Log](math/SKILL.md#lean-review-11)、[Success Condition](math/SKILL.md#lean-review-12)。

**代表原句：**

> Ask whether that left-hand side occurs syntactically in the current goal.

> If the answer is no, stop and choose a bridge step instead.

> The proof is on track when each rewrite is justified by a literal syntactic match, and every bridge lemma moves the branch toward a single stable normal form instead of introducing another oscillation.

**问题：**原 skill 把“打印出来没有同样的子式”直接当成必须先整理或搭桥的依据，还把字面匹配写进验收条件。外观检查有用，但定义展开、参数实例化和实际匹配也会影响改写；这个限制原来就存在，并不是迁移到另一种语言后才出现。

**建议：**把外观匹配降为第一步检查；随后核对实际类型、参数、改写方向和必要的定义展开。只有真实缺少连接等式时才新增桥接。调试记录和验收依据改写实际成功及目标是否推进，不只填字面 yes/no。

### 2. 把错误消息直接当成根因

**位置：**[Common Failure Signatures](math/SKILL.md#lean-review-9)。

**代表原句：**

> `The LHS of mulnC ... does not match any subterm` means there is no multiplication node yet, or not the one you think.

> `No applicable tactic` after several rewrites usually means the proof drifted across multiple normal forms without a stable bridge.

**问题：**故障速查表把错误消息直接连接到缺少乘法节点或表示漂移。它们可以是排查线索，但仅凭这条消息不一定能确定原因；其中“usually”也应有案例依据。这个诊断边界在原语言中同样需要澄清。

**建议：**将表项写成“可能原因→需要检查的目标/引理类型/中间状态→确认后的动作”。保留真实案例支持的经验判断，但区分已观察事实与推测，不把消息本身当作原因证明。

### 3. 部分引用仍指向旧路径或缺失资源

**位置：**[Prefer a generic bridge lemma when](math/SKILL.md#lean-review-5)、[When To Switch To Count Bridging](math/SKILL.md#lean-review-7)、[Common Failure Signatures](math/SKILL.md#lean-review-9)。

**代表原句：**

> ```text
> More ready-to-copy templates are in [bridge-lemma-templates](./assets/bridge-lemma-templates.v).
> ```

> ```text
> If the branch has clearly become a counting proof, switch to [ssreflect-count-bridging](./skill_count.md) instead of staying here.
> ```

> ```text
> See [failure-signatures](./references/failure-signatures.md) for a mapping from common error messages to the missing normalization step.
> ```

**问题：**当前文件布局中，这三个相对链接对应的 math/assets/bridge-lemma-templates.v、math/skill_count.md、math/references/failure-signatures.md 均不存在，用户无法按原文打开配套材料。计数 skill 实际位于 count-bridging/SKILL.md。路径或资源缺失原本就存在，与证明语言迁移无关。

**建议：**先核对配套文件是否遗漏；补齐应随 skill 提供的资源，或按其真实位置修正相对链接。现有计数 skill 对应相对路径为 ../count-bridging/SKILL.md。其余两个资源需找到或补齐后再确定链接；不要仅改扩展名便假定文件存在。

## parameter

### 1. 参数被后续条件引用，不代表必须马上手填

**位置：**[What Must Be Fixed First](parameter/SKILL.md#lean-review-2)。

**代表原句：**

> An implicit argument or instance must be fixed first if it does one of the following:

> appears in the type of later hypotheses, so Coq cannot state those hypotheses until the binder is chosen

**问题：**这里把“影响实例或后续类型”列成必须先确定参数的条件，但依赖关系本身还没有说明该参数能否从当前目标或已有实参推断，或者是否允许暂留约束。读者可能把“存在依赖”误读成“必须马上手填”；这是原规则的适用边界，不是迁移新产生的问题。

**建议：**将清单定位为检查线索，再要求展示该次调用为何确实被某项信息阻塞。区分能推断的参数、当前确实无法继续的项和普通证明前提；只对实际阻塞项要求提前确定。

### 2. 没有说清显式调用禁令的边界

**位置：**[Hard Rule](parameter/SKILL.md#lean-review-5)、[Preferred Application Style](parameter/SKILL.md#lean-review-6)、[Final-Theorem Example](parameter/SKILL.md#lean-review-9)、[Anti-Patterns](parameter/SKILL.md#lean-review-10)。

**代表原句：**

> For this failure mode, `exact (@lemma ...)` is prohibited as a repair strategy.

> If `apply:` or `eapply` already exposes ordinary subgoals, then the explicit `exact (@lemma ...)` form is strictly worse and should be rejected.

> That style is brittle because it forces you to guess generalized binder order, policy choices, and instance placement all at once. One small drift in a threshold instance, interference instance, or policy coercion can make the entire term ill-typed.

**问题：**原文明确把完整显式调用禁令限定在这一失败场景，并不是禁止所有 exact/@。需要澄清的是：反对未经核对地猜位置，还是即使已经核对声明也仍禁止完整显式调用。forces you to guess、strictly worse 和 stronger 容易把工作流偏好说成表达形式必然有缺陷或证明更强；这与迁移无关。

**建议：**保留目标驱动和维护已验证进度的优先策略，明确它拒绝哪种修复行为及理由。如果任务刻意禁止完整显式项，就说明这是受限工作流规则；不要由调用形式直接推断其数学有效性或是否经过核对。对“stronger”说明指的是流程优势，而非定理更强。

### 3. 把不同应用错误统一归为提前绑定失败

**位置：**[argument-hint 配置](parameter/SKILL.md)、[Failure Signals](parameter/SKILL.md#lean-review-3)。

**代表原句：**

> argument-hint: '[theorem name] [goal shape or early-binding error]'

> These are early-binding failures. They are not ordinary missing premises.

**问题：**收到证明却期待数据，能说明该处应用的类型不匹配，但要进一步区分参数位置错误和确实尚未确定的实例/策略。“这些都是 early-binding”需要明确在本 skill 中采用多宽的定义，不能把故障分类误当作已经查明唯一原因。输入提示也预先使用 early-binding error 这一分类；若用于尚未查明原因的诊断，应允许用户先提供原始错误，不要求先接受分类。

**建议：**先给出该次调用的期望参数及实际提供值，再说明属于参数错位还是未解析信息阻塞；如果 early-binding 在文中是总称，应说明其范围，并分别给出后续检查动作。输入提示先请求原始报错、目标和调用，再按证据命名故障。

## goal

### 1. 目标数不是 1，就要求进入恢复流程

**位置：**[Core Rule](goal/SKILL.md#lean-review-2)、[Required Procedure](goal/SKILL.md#lean-review-3)、[Hard Recovery Protocol](goal/SKILL.md#lean-review-6)、[Bullet-Based Repair Pattern](goal/SKILL.md#lean-review-11)。

**代表原句：**

> If the current focused goal count is not exactly one, the next step is a recovery step, not a math step.

> If the goal count changed, respond structurally, not mathematically.

> If the goal count is still not exactly one, repeat this protocol.

**问题：**把“目标数不是 1”直接当成证明出错，并冻结后续数学步骤，条件过强。正常分类会产生多个目标，完成局部证明也可能暂时没有目标；这两种情况在 Rocq 中同样会出现。反复要求恢复到 1 个目标，可能把合法进展误判为必须修复的状态。

**建议：**保留目标数量记录，但把恢复入口改为“当前目标或分支归属与预期不符，或本以为已完成的局部证明仍留有目标”。只有某个具体命令要求单目标时，才检查该命令的局部前提；不要把它升级为整个证明的统一门槛。

### 2. 把多目标之后的错误统一当成次生噪声

**位置：**[Core Rule](goal/SKILL.md#lean-review-2)、[Anti-Patterns](goal/SKILL.md#lean-review-9)、[Trace Example From This Workspace](goal/SKILL.md#lean-review-10)。

**代表原句：**

> Do not respond to secondary errors like `Cannot apply lemma ...` or `No such goal` before restoring the goal count to one.

> Any later lemma-application mismatch is diagnostic noise until the focus count returns to one.

**问题：**把多目标之后的引理应用错误统一当成噪声，可能跳过真正的首个原因。分支尚未处理完时，也可能同时写错引理、参数或名称；这种错误不会因为目标数量恢复到 1 就自动消失。原案例可以展示连锁报错，但不能推出所有后续报错都属于这一类。

**建议：**先检查错误所在位置、当前目标和上下文。只有确认某条消息由更早的状态错误引起，才延后处理；对独立的类型、名称或参数错误，仍按证据修复。

### 3. 要求每次分类前都先展开目标定义

**位置：**[When to Use](goal/SKILL.md#lean-review-1)、[Core Rule](goal/SKILL.md#lean-review-2)、[Required Procedure](goal/SKILL.md#lean-review-3)、[Hidden Goal Head Before Case Split](goal/SKILL.md#lean-review-4)、[Goal-Count Checklist](goal/SKILL.md#lean-review-8)、[Anti-Patterns](goal/SKILL.md#lean-review-9)、[Success Condition](goal/SKILL.md#lean-review-13)。

**代表原句：**

> Inspect the literal goal head before any new split.

> before splitting a boolean goal, check whether the boolean expression is literally present in the current goal head

> every split acts on a literal visible goal head rather than a hidden wrapper definition

**问题：**把“分类对象必须直接出现在目标头，先展开定义才能分类”写成了通用硬规则。实际需要区分两件事：建立不同情况的假设，以及用这些假设改写当前目标。分类本身可以有用，即使目标还包在定义里；某一次改写需要先展开，并不说明所有分类都必须先展开。这也是原 Rocq 规则的适用范围问题。

**建议：**保留“检查分类有没有产生预期效果”的排查办法。先明确这一步要建立哪些情况、改写哪里，再根据具体操作决定是否展开定义；把先展开的要求限定到确实依赖目标形状的步骤。

### 4. 把顺序处理多个目标一律当成错误

**位置：**[Core Rule](goal/SKILL.md#lean-review-2)、[Anti-Patterns](goal/SKILL.md#lean-review-9)。

**代表原句：**

> If there is more than one goal, switch to bullet management immediately. Do not continue with a single-goal script.

> Do not keep writing linear tactics after a branching tactic created multiple goals.

**问题：**把产生多个目标后继续顺序写 tactic 一律列为错误，混淆了证明风格和正确性。危险的是没有确认当前目标就继续，而不是顺序书写本身。若每一步的目标明确，顺序处理多个目标在原 Rocq 中也可以合法工作。

**建议：**可以把逐支使用 bullet 保留为项目风格要求，但应说明这是组织纪律。诊断时区分“违反项目书写规则”和“实际用错目标或漏掉分支”，不要仅凭线性写法就断定证明状态已经失控。

## tactics

### 1. 展开后出现分支，就要求修复结构

**位置：**[Required Procedure](tactics/SKILL.md#lean-review-4)、[First Revealed Error -> Real Cause](tactics/SKILL.md#lean-review-5)、[What To Do After Expansion](tactics/SKILL.md#lean-review-6)。

**代表原句：**

> More than one goal: the payload split the proof and needs bullets or braces.

> If branches appeared, fix proof structure first.

**问题：**把“展开后出现多个分支”直接判成证明结构出错，容易把正常推进误当成恢复任务。例如证明两个条件同时成立，本来就可能留下两个目标；在原 Coq 环境中也是如此。

**建议：**先确认这些分支是否是上一步预期生成的，以及是否仍在预期分支上。只有分支归属混乱或局部块遗漏时才进入结构恢复；正常分支继续分别证明即可。

### 2. 把改写失败简单归为字面不匹配

**位置：**[First Revealed Error -> Real Cause](tactics/SKILL.md#lean-review-5)。

**代表原句：**

> The chosen rewrite does not literally fit the current goal shape.

**问题：**这句把改写失败归结为字面形状不匹配，但打印出来的文字只是一条线索。实际类型、隐式参数、定义展开或改写方向也可能影响匹配；这些并非换到 Lean 才出现的问题。

**建议：**把字面形状写成待核实的候选原因，连同目标、等式类型、展开情况和方向一起检查，再选择修复动作。

### 3. 转交其他 skill 的路径已经过时

**位置：**[What To Do After Expansion](tactics/SKILL.md#lean-review-6)。

**代表原句：**

> `skill_goal.md`

> `.github/skills/coq-proof-state-discipline/skill_math.md`

**问题：**转交其他 skill 时引用了旧目录或旧文件名；它们与当前这份技能包的 goal/SKILL.md、math/SKILL.md 布局不一致。这是文档打包和路径维护问题，与证明语言无关。

**建议：**按实际安装布局修正交叉引用；在当前目录布局下，从本文件可使用 ../goal/SKILL.md 和 ../math/SKILL.md。这里只记录建议，不修改原文路径。
