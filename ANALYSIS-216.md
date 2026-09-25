# JSP-000216 / Erdős 245：当前数学分析

更新时间：2026-09-25。

## 题目与语义

令

```text
A_N = |A ∩ [1,N]|,
B_N = |(A+A) ∩ [1,N]|.
```

原题要求对每个无限且零密度的 `A ⊆ ℕ` 证明

```text
limsup B_N / A_N ≥ 3.
```

Formal Conjectures 的精确声明（`FormalConjectures/ErdosProblems/245.lean`）是：

```lean
∀ (A : Set ℕ), A.Infinite →
  atTop.Tendsto (fun N ↦ (A ∩ Icc 1 ⌊N⌋₊ |>.ncard : ℝ) / N) (𝓝 0) →
  3 ≤ atTop.limsup
    (fun N : ℝ ↦ ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal)
      / (A ∩ Icc 1 ⌊N⌋₊).ncard)
```

该文件目前仍以 `sorry` 占位。主工程没有把这个占位声明复制成一个
伪证明；`JSP000216.lean` 只保留不依赖 Mathlib 的自然数接口。

Erdős 问题 [#245](https://www.erdosproblems.com/245) 页面明确记载：常数 2 的版本来自 Mann 的结果，常数 3 的肯定解归于 Freiman [Fr73]，页面没有给出证明展览。JSP-000216 是奖项目录编号，不能把它误读为 Erdős 问题 #216。Formal Conjectures 的对应 Lean 声明在 [`FormalConjectures/ErdosProblems/245.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/245.lean)，目前也是 `sorry` 占位。

当前核心文件中的 `DiscreteThreeExact` 要求无穷多个 `N` 满足
`3 * A_N ≤ B_N`，这比实数 limsup 结论更强，因为比值可能从下方趋近 3 而永远不达到 3。现在实际使用的 `DiscreteThreeApprox` 是：对每个 `k > 0`，无穷多个 `N` 满足

```text
(3k − 1) A_N ≤ k B_N.
```

这对应误差 `1/k`，是后续连接 EReal limsup 的正确离散接口；仍需在 Mathlib 层处理“分母最终为正”和自然数索引到实数索引的等价性。

核心层现在还证明了接口层级：`DiscreteThreeExact` 蕴含
`DiscreteThreeApprox`，而后者取 `k = 1` 蕴含常数 2 的离散陈述
`DiscreteTwo`。这只是离散接口之间的逻辑关系，不是对 Freiman 定理的替代。

## 已完成的有限层

`JSP000216.lean` 已证明：若 `x 0 < ... < x (n-1)`，则

```text
x 0 + x 0, ..., x 0 + x (n-1),
x 1 + x (n-1), ..., x (n-1) + x (n-1)
```

给出 `2n−1` 个两两不同的和。该结果通过 `HasDistinctWitnesses` 表示，避免在 core-only 文件中伪造 `Finset.card`。它是标准的 `|F+F| ≥ 2|F|−1` 基础界，但只能支持常数 2 附近的论证，不能单独推出题目的常数 3。

现在还增加了 `TruncatedSumSet A N` 和对应的截断 witness 定理：如果参与构造的序列元素都在 `[1,N]`，则这 `2n−1` 个和落在 `TruncatedSumSet A (2N)` 中。这样后续 Mathlib 层可以把 witness 下界接到题目中的 `B_{2N}`，同时保留截断上界，而不是丢掉区间信息。

此外，核心层已固定截断和集的单调性：增大截断端点或扩大底集都会保留已有 witness。它们仍然用显式注入 witness 表达，尚未声称等于 `Finset.ncard`；这一步应在引入 Mathlib 后由有限区间枚举完成。

核心层现在还从 `Infinite A` 自动抽取任意长度的正严格递增前缀，并推出某个端点 `N` 使 `TruncatedSumSet A (2N)` 含有 `2n−1` 个显式不同元素。这个结果仍然只是基础下界；它说明了“无限性 → 有限截断 witness”的接口已经闭合，但没有解决常数 3 的结构转移。

现在还证明了一个选择引理：给定正整数 `k` 和任意下界 `M`，无限零密度集合存在某个 `N ≥ M`，使 `A_N > 0` 且 `k A_N ≤ N`。同时，`(A+A)` 的正截断计数沿偶数端点无界。这两条结果把“分母最终为正”和“稀疏误差尺度”的自然数接口固定下来，仍不包含 Freiman 的 `3k−4` 结构定理。

为避免把有限三块构造误当成无限转移，核心层现在定义了
`GapSparseThreeApprox`：它明确要求每个误差参数和端点都存在满足 gap、严格递增和分母控制的有限块，并已无公理地证明该接口蕴含 `DiscreteThreeApprox`。因此剩余缺口被收窄为证明所有无限零密度集合满足这个 witness 接口，而不是隐藏在一个未审计的目标定义里。

又新增了计数桥梁：若 `f 0 < ... < f (m−1)` 是 `S` 中的正元素且都不超过 `N`，则 `m ≤ countPos S N`。应用到边界和序列后得到

```text
2*n − 1 ≤ countPos (SumSet A) (2*N).
```

这已经把显式 witness 变成了题目分子使用的递归计数函数。它完整解释了 Erdős 所说的常数 2 基础层，但仍没有给出常数 3；后者必须利用 Freiman 的结构性信息，而不是再增加一条边界和链。

另外，`countPos_eventually_pos` 已证明：对无限 `A`，分母计数在某个端点之后始终为正。这解决了 EReal 商的最终定义域问题，但不解决商的下界问题。

核心层现在还形式化了一个有限的“三块”构造。对前缀 `x 0 < … < x (n−1)` 和新元素 `x n`，若

```text
2*x(n−1) < x n + x 0,
```

则前缀的 `2n−1` 个边界和与 `x n + x i` 的 `n` 个交叉和彼此分离，合计得到 `3n−1` 个严格递增的和，并证明

```text
3*n − 1 ≤ countPos (SumSet A) (x n + x (n−1)).
```

这是真正出现常数 3 的有限机制。无限题的缺口已经更具体：必须从零密度序列中选择满足这种间隔/分母控制的嵌套块；仅凭无限性不能保证该 gap 条件。

## Freiman 结构定理提供的真正桥梁

可核查的独立形式化资料是 Isabelle AFP 的 [Freiman's 3k−4 Theorem](https://devel.isa-afp.org/entries/Freiman_3k_4.html)。其最终有限定理的形状是：若有限整数集 `F` 满足 `|F| ≥ 3` 且

```text
|F+F| ≤ 3|F| − 4,
```

则 `F` 包含在一个正差等差数列中，数列长度至多

```text
|F+F| − |F| + 1.
```

该 AFP 条目是有限整数集的结构定理，不是 Erdős 245 的无限零密度结论，也没有被复制或作为 Lean 依赖使用。

因此，原题的关键反证方向应当是一个“有限结构到无限密度”的转移定理：如果某个无限集的截断和集比值长期低于 `3−ε`，则不断增大的有限截断会被短等差数列控制；嵌套截断和零密度条件最终迫使 `A` 在某些长区间具有正比例密度，矛盾。这个转移步骤是当前项目最大的数学缺口，不能用 `2n−1` 的基础界替代。

## 容易出错的截断关系

对 `F_N = A ∩ [1,N]`，确实有

```text
F_N + F_N ⊆ (A+A) ∩ [1,2N].
```

但这只给出 `B_{2N} ≥ |F_N+F_N|`，分母却是 `A_{2N}`，不等于 `A_N`。零密度本身并不自动给出 `A_{2N}/A_N → 1`。所以不能把有限 `3k−4` 定理直接套在 `F_N` 上，就宣称得到目标 limsup；还需要一个尺度选择或嵌套结构引理。

同样，`A` 无限只能保证 `A_N > 0` 对充分大的 `N` 成立；在此之前 EReal 中的分母为零必须单独处理，不能把自然数整数比值接口直接当作原题的实值函数。

## 建议的下一步形式化顺序

1. 在 Mathlib 分支中固定与 Formal Conjectures 相同的 `Set ℕ`、`Icc`、`ncard`、`EReal` 和 `atTop.limsup` 表述，并证明 `A_N` 最终为正。
2. 先形式化截断和集的包含关系及有限集 `2n−1` 下界；这部分可复用 core 文件的 witness 结果。
3. 形式化有限 `3k−4` 结构定理的 Lean 版本，或明确记录一个可独立审查的完整证明依赖；不能把 Isabelle 定理当成 Lean 已证明定理。
4. 单独证明 Freiman 的无限转移引理：零密度与“所有充分大截断的比值 `< 3−ε`”不相容。
5. 最后证明离散误差接口与 Formal Conjectures 中 EReal limsup 的双向蕴含，并审计完整依赖闭包。

## 依赖边界记录

在本地忽略目录中已经核对过 Mathlib 所需的主要接口：
`Set.ncard`（`Mathlib.Data.Set.Card`）、`ncard_Icc_nat`
（`Mathlib.Order.Interval.Set.Nat`）、`EReal`（`Mathlib.Data.EReal.Basic`）
以及 `Filter.limsup`（`Mathlib.Order.LiminfLimsup`）。这些接口足以表达
目录中的目标类型，但不能提供 Freiman 的无限转移证明。由于主工程当前
刻意保持 Lean 4.33.0、无外部包依赖的可复现构建，Mathlib 试验没有被写入
`lakefile.toml`，也没有把 Formal Conjectures 的 `sorry` 作为依赖提交。

在第 4 步完成以前，项目只能称为有限层和接口层进展，不能称为 JSP-000216 的完整证明。
