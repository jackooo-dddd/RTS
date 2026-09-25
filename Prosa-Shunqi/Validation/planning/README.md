# 规划材料

- `v06_dependency/`：固定 Prosa v0.6 的文件 DAG 和声明 inventory；文件 DAG 决定就绪顺序。
- `v06_current_policy/`：当前翻译使用的 v0.6 表示政策和基础结构决策。
- `v06_pipeline/`：逐文件状态、manifest 和验收证据。
- `v06_mapping/`：早期比较研究的哈希绑定快照，包含旧版本 inventory、迁移表及复现脚本。它只用于解释历史证据和兼容仍读取迁移表的旧脚本，**不再作为候选代码、复用决策或当前表示政策的来源**。不要改写其内容或把其中的历史分类当作当前 acceptance。

旧快照内的路径和版本信息是原始证据，不应伪装成当前运行结果；新执行应使用本工作区的固定 v0.6 source、当前 policy 和最新 machine status。
