# Mini Math Kernel（迷你数学内核）

一套**从零开始、零依赖的 Lean 4 实现**，涵盖大学层次的数学基础与证明论。每个子包对应 MIT（及其他顶尖大学）课程，使用 Lean 4 证明助手从第一性原理构建形式化数学基础。

## 子包

| 子包 | 主题 | 核心课程 |
|------|------|----------|
| [mini-logic-kernel](mini-logic-kernel/) | 命题逻辑、谓词、量词、重言式检查器 | MIT 6.042J, Stanford CS103 |
| [mini-syntax-kernel](mini-syntax-kernel/) | 项语言、de Bruijn 索引、绑定结构 | MIT 6.821, Cambridge Part II |
| [mini-object-kernel](mini-object-kernel/) | 对象类型类、理论名称、类型化结构 | MIT 18.996, Princeton MAT 595 |
| [mini-proof-kernel](mini-proof-kernel/) | 自然演绎、证明树、矢列演算 | MIT 6.825, CMU 15-317 |
| [mini-axiom-kernel](mini-axiom-kernel/) | 公理系统、公理集合、一致性检查 | MIT 18.510, Princeton MAT 560 |
| [mini-construction-kernel](mini-construction-kernel/) | 结构、积、余积、商、函数空间 | MIT 18.996, Cambridge Part III |
| [mini-theory-dependency-kernel](mini-theory-dependency-kernel/) | 理论依赖图、依赖类型、理论清单 | MIT 6.821, Oxford CS |

## 设计理念

- **零外部依赖** -- 纯 Lean 4，仅导入内核模块
- **自包含子包** -- 每个子包拥有独立的 `lakefile.lean`、Core/、Morphisms/、Constructions/、Properties/、Theorems/
- **理论到代码的映射** -- 每个模块包含内联 `#eval` 示例和定理陈述
- **模式库** -- 建立所有下游领域包复用的编码规范

## 构建

每个子包独立构建。使用 Lake 构建：

```bash
cd mini-logic-kernel
lake build
lake env lean --run Test/Smoke.lean
```

需要 **Lean 4** 和 **Lake**。

## 项目结构

```
0. mini-math-kernel/
├── mini-logic-kernel/               # 命题/谓词逻辑、重言式检查
├── mini-syntax-kernel/              # 项语言、de Bruijn 索引、绑定
├── mini-object-kernel/              # 对象类型类、类型化结构
├── mini-proof-kernel/               # 自然演绎、证明树、矢列演算
├── mini-axiom-kernel/               # 公理系统、一致性检查
├── mini-construction-kernel/        # 积、余积、商、函数空间
├── mini-theory-dependency-kernel/   # 理论依赖图和清单
├── plan.md                          # 分阶段执行计划
├── lakefile.lean
└── lean-toolchain
```

## 许可证

MIT
