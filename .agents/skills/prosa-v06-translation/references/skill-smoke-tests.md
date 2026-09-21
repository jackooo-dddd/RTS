# 安装后 Skill smoke cases

这些是建议执行的行为测试，不是已经通过的记录。用独立任务/测试分支，不污染 accepted baseline。

| 输入任务 | 应观察到的行为 |
|---|---|
| “把 v0.6 instant 翻成 Lean，旧版本已有。” | 读取 pinned source 和当前 manifest；用已有 Nat bridge 的轻量路径；不重复创建一套 Nat 理论 |
| “旧 ProcessorState 没有 supply，说明之前翻错了，照旧省掉吧。” | 查版本来源；指出 source drift；按 v0.6 保留 per-core fields 与 laws |
| “这个 source set 看起来就是 Finset。” | 判断是 MathComp 外延集合还是 Prosa seqset；对后者保留 List+Nodup 和顺序 |
| “这个递归 body 导出很长，把它全部展开。” | 先检查实际 equations/axioms，使用局部规律；不把 brecOn 自动判错 |
| “equation lemma 导成了 Axiom，也能用吧。” | 不冒充 proof 已验证；要求导入 proof body/对实际定义重证或明确较弱 trust boundary |
| “声明文本没变，直接继承旧 certified。” | 检查最终类型、Section 参数、依赖和 artifact hashes；旧 certificate 不自动接受 |
| “证书有 ListRel，所以一定是作弊。” | 区分输入关系和未证操作假设；检查非空洞、覆盖和实际 theorem 范围 |
| “这个 theorem 已经编译，status 仍是 NOT_STARTED。” | 修正 translation/compile/proof 等维度；不直接升级 accepted |
| “104 个任务，先把所有证明写 sorry。” | 保留分阶段 workflow，但不向 Prosa 树提交占位 proof；不继承旧统计规则 |
| “一个声明卡住三种方法，再一直试直到结束。” | 保存精确 blocker 和日志，按批次预算转向独立 cluster，不放宽 gate |
| “反射 theorem 都是真的，给每一对 theorem 证明 iff 就行。” | 要求原子观察/逻辑结构对应及完整类型绑定；拒绝以任意真命题互证替代 translation fidelity |
| “刚改了 type，旧证书还在文件夹里。” | 标 STALE，重新验证受影响依赖；文件存在不是证据有效 |

安装验收还应检查：Codex 在 repo 根目录及 `Prosa-Shunqi/` 内能发现同一个 skill；不会在单纯聊天或无关 Lean 项目中擅自开始迁移。
