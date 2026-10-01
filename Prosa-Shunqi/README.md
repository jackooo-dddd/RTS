# Prosa v0.6 → Lean 4

本项目将实时系统形式化库 [Prosa](https://prosa.mpi-sws.org/) 的 v0.6 版本（commit
`414e66760333eaa4ef78c685bcf53291c527a548`）完整翻译为 Lean 4，并逐文件、逐声明地机器验证每个翻译与官方
Rocq 定义和定理语义对应。

| | |
|---|---|
| 翻译范围 | Prosa v0.6 全部 **357** 个 source file、**2439** 个 public declaration |
| 验收状态 | **357/357 个文件、2439/2439 个声明已通过正式验收**（`ACCEPTED_V06_FILE`） |
| Lean 环境 | Lean 4.33.1；Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` |
| 验证环境 | Rocq 9.3（opam switch `rocq93rc1`）；CoqEAL 2.1.2 本地构建（仅 `implementation/refinements/*`） |
| 状态与报告 | [Reports/README.md](Reports/README.md) |

## 验证方法

每个 source file 由同一条流水线 `Validation/scripts/translation_file_pipeline.py` 处理，分三个阶段：

1. **prepare**：编译官方 Rocq 源码（官方证明闭包，加上记录在案、仅涉及证明的 Rocq 9.3 兼容补丁）和 Lean 翻译；以 `lean4export` 导出实际编译出的 Lean 常量，再以 `rocq-lean-import` 导入 Rocq。
2. **check**：编译逐声明的 correspondence 证书，证明导入后的 Lean 定义和语句与官方 Rocq 定义和语句对应，并对每个证书做 fail-closed 的假设审计。
3. **publish**：核对官方类型证据、全部哈希与累计 coverage，写出 manifest 与 status。

验收门槛：

- **实际产物绑定**：证书只引用实际编译出的产物，每个产物都以哈希记录。
- **精确类型**：每个声明的类型须与官方工具链的类型证据逐字一致。
- **无自依赖**：证书不使用本文件自身的 source 或 target 定理。
- **假设审计**：不允许语义前提、未列入白名单的公理或 `sorryAx`。

逐文件报告记录与官方 Prosa 的全部差异：表示选择、兼容补丁、导出边界与每次失败尝试。

## 目录结构

```text
Prosa-Shunqi/
├── Prosa/                         Lean 4 翻译（357 个模块，结构与 Prosa v0.6 一一对应）
├── Reports/
│   ├── README.md                  验收状态总表与报告索引
│   ├── files/                     每个 source file 一份 canonical report
│   └── casestudy/                 单声明端到端验证示例（Finish Time）
├── Validation/
│   ├── scripts/                   验证流水线及其辅助脚本
│   ├── tooling/                   导出/导入工具的固定版本、补丁、file specs 与导出配置
│   ├── fixtures/                  导出根模块与仅用于验证的接口等式（随产物导出，由内核检查）
│   ├── certificates/              逐文件 Rocq correspondence 证书与假设配置
│   ├── patches/                   官方证明闭包的 Rocq 9.3 兼容补丁
│   ├── planning/                  文件 DAG、声明 inventory、表示政策、逐文件 manifest/status
│   ├── imported/                  已发布的导入产物（不纳入版本控制）
│   └── logs/                      原始机器日志
├── v06_file_translation_order.md  正式文件执行顺序（按文件 DAG 分层）
├── lakefile.lean · lean-toolchain · lake-manifest.json
└── README.md
```

## 构建

```bash
lake exe cache get   # 获取 Mathlib 预编译产物
lake build           # 编译全部 Prosa/ 模块
```

## 复现验证

验证需要 opam switch `rocq93rc1`（Rocq 9.3 与 MathComp），以及按固定 commit 和补丁重建的导出/导入工具：

```bash
Validation/tooling/setup_validation_tooling.sh   # 构建 lean4export 与 rocq-lean-import（fail-closed 校验）
```

单个文件的验证：

```bash
cd Validation
python3 scripts/translation_file_pipeline.py tooling/file_specs/<slug>.json prepare
python3 scripts/translation_file_pipeline.py tooling/file_specs/<slug>.json check
python3 scripts/translation_file_pipeline.py tooling/file_specs/<slug>.json publish
python3 scripts/update_reports_readme.py && python3 scripts/update_reports_readme.py --check
```

运行目录位于 `Validation/.work/`（不纳入版本控制）。

## 约定

- 唯一规范是固定的 Prosa v0.6 commit。Lean 文件存在不代表已验收；验收与 coverage 只以
  `Validation/planning/v06_pipeline/` 中的 status/manifest 为准。
- 文件就绪由文件 DAG（`Validation/planning/v06_dependency/`）决定；多个文件同时就绪时，按
  [文件执行顺序](v06_file_translation_order.md)选择。
- 新翻译遵循[当前表示政策](Validation/planning/v06_current_policy/representation_policy.md)。
- 每个 source file 只维护一份报告，更新时沿用首次报告的文件名。
