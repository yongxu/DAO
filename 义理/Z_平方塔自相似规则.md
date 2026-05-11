# Z · 平方塔自相似规则（squaring tower）— R₀/R₁/R₂/R₄/R₈ 之元结构

> 状态: v1 (2026-05-11). 概念哲学文章, 不含 Lean 形式. 形式化已经在 [Cell256Stratify.lean](../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) 之 (Z/2)ⁿ 严格 closure 中**隐式蕴含**, 本文显式陈述这条隐而未发的元规则.

## 0 · 一句话

> **R₀..R₈ 全塔之内, 存在一条只穿过下标 0, 1, 2, 4, 8 之子塔, 由"平方"算子 S(A) := A × A 递推生成。**

```
T_{k+1} = T_k × T_k    (k ≥ 1, 平方递推)
T_1 = T_0 + T_0        (奠基, 由 O₀ 给; 动静 / substance·field / 协积 三相同义)
T_0 = Unit             (太极, 平方算子之不动点)

|T_k| = 2^(2^(k-1))    for k ≥ 1; |T_0| = 1
塔层 = {R_0, R_1, R_2, R_4, R_8} = {1, 2, 4, 16, 256}
```

## 1 · 为何先做这件事 — 背景

[yi-RO-hierarchy.md](../docs-next/10_formal_形式/yi-RO-hierarchy.md) 给出 R₀..R₈ **strict (Z/2)ⁿ uniform**
之 9 级 incrementing 视角. 即每加 1 bit = 进下一层. 这条主线视角下,
R₃ (八卦) 之与 R₄ (面 Mian) 之间, R₄ 与 R₈ (Cell256) 之间, 在结构上**没有特殊地位之分**.

但若放低分辨率, 只取下标 ∈ {0, 1, 2, 4, 8} 之层, 则这五层之间有更紧之关系:

```
R_0 → R_1     奠基跃迁 (R₀ 加 O₀ 得 R₁)
R_1 × R_1 = R_2   (4 象 之内核)
R_2 × R_2 = R_4   (Mian 之内核)
R_4 × R_4 = R_8   (宇宙 之内核)
```

即从 R_1 起, 后一层就是前一层之**平方** (自身与自身之 Cartesian 积 / 张量积).
这条性质称为**自相似平方塔** (squaring tower).

R₃, R₅, R₆, R₇ 不在这条子塔上 (它们之 cardinality 不是 2 的 2 的幂之幂). 它们由 +1 bit 之
"incrementing" 路径从塔内层跨出, 详 § 5.

## 2 · 平方算子 S 之精确定义

设 **FinType** 为有限类型范畴 (或 FinSet 之自然广义). 平方算子定义为:

```
S : FinType → FinType
S(A) := A × A     (Cartesian 积 / 直和 / 张量积 — 在有限交换群范畴内三者重合)
S(f : A → B) := f × f
```

显然 |S(A)| = |A|². 故连续应用得:

```
S^0(A) = A
S^1(A) = A × A         |S^1(A)| = |A|^2
S^2(A) = (A × A) × (A × A)   |S^2(A)| = |A|^4
S^k(A) = ...            |S^k(A)| = |A|^(2^k)
```

塔形为 S 在 T_1 = R_1 (= Bool = 2 元素) 上之反复作用:

| k | T_k | size | R-index | 易学名 |
|---|-----|------|---------|--------|
| 0 | Unit | 1 | R_0 | 太极 |
| 1 | T_0 + T_0 = Bool | 2 | R_1 | 爻 / 两仪 |
| 2 | T_1 × T_1 | 4 | R_2 | 四象 |
| 3 | T_2 × T_2 | 16 | R_4 | 面 Mian (= Ben × Zheng) |
| 4 | T_3 × T_3 | 256 | R_8 | 果卦 Cell256 (= 宇宙) |

故 R-index 对应关系为 **|T_k| = R_{2^(k-1)} for k ≥ 1, T_0 = R_0**. 塔深 k 按 +1, R-index 按 ×2.

## 3 · 奠基步: R_0 + O_0 → R_1

注意 S(R_0) = R_0 × R_0 = 1 × 1 = 1 = R_0. **平方算子在 R_0 处退化** (不动点).
故 R_1 不由 S 从 R_0 生成 — 需要外加一个奠基算子 O_0.

O_0 之三种等价表述 (用户已确认: **三者同义, 不必取一**):

### 3.1 协积表述 (范畴论)

```
O_0 = "复制一份并贴上不同标签"
R_1 := R_0 + R_0 = 1 ⊔ 1 = 2 (协积 / coproduct)
```

形式上 R_1 是有 2 个不同元素的最小型, 由 1 之协积自身给出.

### 3.2 动静表述 (动力学)

```
O_0 = "动" (movement)
R_0 = "静" (stillness, 太极未分之态)
R_1 = {静, 动} = R_0 在 O_0 作用下分裂之像
```

R_0 是动力学之初始态 (无运动). O_0 是第一个非平凡运动. R_1 是 R_0 与 O_0(R_0) 之并集.

### 3.3 实虚表述 (本体论)

```
O_0 = "赋以 substance 或 field 之二选"
R_0 = 中立之未分
R_1 = {实, 虚} = {substance, field}
```

实 = substance = 物质性 / 有质 / 已塌缩.
虚 = field = 场性 / 无质 / 未塌缩.
这是 **物理直觉版本** — 用户原话: "实是 substance, 虚是场".

### 3.4 三者之等价

三个表述给出**同构**的 R_1: 2 元素 set + 一个非平凡 swap 自同构.
区别只在语义负重 — 协积 = 范畴论之最点则, 动静 = 动力学之初萌, 实虚 = 本体论之二分.
doctrine 同列三相; 形式化时取任意一个 (或同时定义并证同构) 皆可.

## 4 · 实/虚 解读之内核 — "实-side × 虚-side"

把 § 3.3 之实虚表述用进每一步平方:

| 层 | 平方分解 | 实-因子 (substance side) | 虚-因子 (field side) |
|----|---------|------------------------|---------------------|
| R_1 | R_0 ⊕ O_0(R_0) | substance ground | field ground |
| R_2 | R_1 × R_1 | 实 之 4 象选 (实实, 实虚) | 虚 之 4 象选 (虚实, 虚虚) |
| R_4 | R_2 × R_2 | substance 之 4 象 | field 之 4 象 |
| R_8 | R_4 × R_4 | substance 之 Mian | field 之 Mian |

R_n 之每元 = 长度 n 之 {实, 虚} 串 = (Z/2)^n 之元素. 这与 codebase 之 OXNotation
`o`/`x` 编码同构: `o` ↔ 实, `x` ↔ 虚 (默认约定; 形式上由 `Yao.zero/one` 决定).

用户列举之 R₄ 内之 16 实虚串:

```
实实实实, 实实实虚, 实实虚实, 实实虚虚,
实虚实实, 实虚实虚, 实虚虚实, 实虚虚虚,
虚实实实, 虚实实虚, 虚实虚实, 虚实虚虚,
虚虚实实, 虚虚实虚, 虚虚虚实, 虚虚虚虚
```

即 2^4 = 16 之 R_4. 这是 T_3 之**显式枚举** (用户原话省略中间, 仅列两端 + 一二例).

## 5 · 元/爻 配对 — 平方步之深层语义结构

用户给出之关键洞察 (2026-05-11 conversation):

> "实/虚 与 本/征 应该是一对是元 一对是爻吧"

即, 在 R_4 = R_2 × R_2 之具体配置, 两个 R_2 因子**不是对称之**:

- 一对承担**「元」** (carrier / 元素 / what-is-being-counted) — 即"被分类之内容"
- 另一对承担**「爻」** (yao / dimension / how-it-is-being-arranged) — 即"分类所沿之轴"

### 5.1 首选读法: 实/虚 = 元, 本/征 = 爻

| 因子 | 角色 | 在 R_4 中之作用 |
|------|------|---------------|
| 内层 R_2 = 实/虚 × 实/虚 | **元** (carrier) | 4 种实虚态 (被分类的内容) |
| 外层 R_2 = 本/征 | **爻** (dimension) | 2 维分类轴 (zong-fixed vs zong-mobile) |

每一个 Mian cell = (一个实虚态, 一个本征位置) = (元, 爻) pair.

### 5.2 对偶读法: 本/征 = 元, 实/虚 = 爻

| 因子 | 角色 | 在 R_4 中之作用 |
|------|------|---------------|
| 内层 R_2 = 本本/本征/征本/征征 | **元** (carrier) | 4 个 BenZheng 四象 (被分类的本体) |
| 外层 R_2 = 实/虚 × 实/虚 | **爻** (dimension) | 2 维实虚附标 |

每一个 Mian cell = (一个 BenZheng 四象, 一个实虚附标) = (元, 爻) pair (反向).

### 5.3 两者皆有 doctrine 价值

**对偶性**: 5.1 与 5.2 之差异不是"对错", 而是**视角选择**.
取 5.1 → 把 BenZheng 之本征位 看作 R_4 之坐标轴 (这与现 codebase 之 BenZheng.lean 一致).
取 5.2 → 把 BenZheng 之四象 看作 R_4 之被排列内容 (这把 BenZheng 推到"内层元结构").

两者无形式冲突 — (Z/2)⁴ 作为阿贝尔群对**两种坐标分配**无偏好. 选择由语义需要决定.

### 5.4 元/爻 配对在塔之每一步皆成立 (推广)

下提为元理论性质 (用户的洞察推广):

> **平方步元/爻 配对原则**: 对每个 k ≥ 1, T_{k+1} = T_k × T_k 之两个 T_k 因子,
> 一个承担**元**(carrier), 另一个承担**爻**(dimension). 二者**形式同构但语义不对称**.
> 具体 carrier/dimension 之分配是**doctrine 选择**, 不由群结构本身决定.

每一层都需为这对分配显式给出语义说明 — 这是 doctrine 之负担, 也是 doctrine 之自由度.

## 6 · 平方塔 vs codebase 之 R₀..R₈ 全塔

codebase 提供**完整 9 级** R₀..R₈, 每级 +1 bit. 用户平方塔是其**子塔**:

```
完整塔 (incrementing):  R_0  R_1  R_2  R_3  R_4  R_5  R_6  R_7  R_8
                         1    2    4    8    16   32   64   128  256

平方塔  (squaring):     R_0  R_1  R_2       R_4                R_8
                         ✓    ✓    ✓    ✗    ✓    ✗    ✗    ✗    ✓
                              └────┘    └────┘              └────┘
                              平方     平方                平方
```

R_3, R_5, R_6, R_7 是**塔外层** — 从平方塔内层 +1 bit incrementing 走出之中间停泊.
具体语义:

- R_3 (8 元 / 八卦): R_2 + 1 bit = trigram
- R_5 (32 元 / 五爻 provisional): R_4 + 1 bit
- R_6 (64 元 / 重卦 Hexagram): R_4 + 2 bit = R_3 × R_3 (自身平方但目标在塔外!)
- R_7 (128 元 / Cell128): R_6 + 1 bit

**两个视角并存**:
- **Incrementing 视角** (codebase 主线): R_n → R_{n+1} 由 +1 bit 给出. 适合 chain-of-reasoning.
- **Squaring 视角** (本文): T_k → T_{k+1} = T_k × T_k. 适合 fractal / 自相似几何.

两者通过 R_n = (Z/2)^n 之同一群在不同坐标下描述**同一对象**.

## 7 · 塔外层 R_3/R_5/R_6/R_7 之多重平方路径

用户洞察 (2026-05-11): 塔外层"是多重平方路径的交叉点".

不是"产阶垫", 不是"降级层" — 它们是**平方塔内层之多种乘积方式之交叉点**:

| 塔外层 | 平方路径分解 | 路径数 |
|--------|------------|--------|
| R_3 = 8 | R_2 × R_1 | 1 |
| R_5 = 32 | R_4 × R_1 | 1 |
| **R_6 = 64** | **R_3 × R_3 = R_2 × R_4 = R_1 × R_5** | **3** |
| R_7 = 128 | R_4 × R_3 = R_2 × R_5 = R_1 × R_6 | 3 |

### 7.1 R_6 之特殊性

R_6 在三种路径下交汇:
- **R_3 × R_3**: 八卦 × 八卦 — 即"内卦 × 外卦"之 Hexagram 自然分解 (codebase 主线)
- **R_2 × R_4**: 四象 × 面 — Hexagram 看作"四象上之 Mian"
- **R_1 × R_5**: 爻 × 五爻 — Hexagram 看作"五爻 + 顶爻"

这三条路径给 R_6 = 64 三种**视角同构** (皆 (Z/2)⁶, 但语义负重不同).
codebase 取 R_3 × R_3 作为主分解 (内 trigram × 外 trigram, 见 Yi.lean 之 Hexagram 定义).

### 7.2 R_7 / R_3 / R_5 之路径

R_7 = R_4 × R_3 = R_2 × R_5 = R_1 × R_6 三路皆有解.
codebase 主用 R_6 × R_1 (Cell128 = Hexagram × YinBit, "因 axis").

R_3 / R_5 仅单路 (R_3 = R_2 × R_1, R_5 = R_4 × R_1). 它们之"塔外性"较弱 — 接近塔内层 + 1 bit.

### 7.3 元/爻 配对在塔外层之延伸

塔外层之多重平方路径意味着: 它们可以**在不同读法下承担不同元/爻 配对**.

例如 R_6 = R_3 × R_3:
- 读法 A: 内 trigram = 元, 外 trigram = 爻 — 一卦 = 一对实虚态, "上下相成"
- 读法 B: 外 trigram = 元, 内 trigram = 爻 — 反向

R_6 = R_2 × R_4:
- 读法 C: 四象 = 元, 面 Mian = 爻 — Hexagram 看作"四象在 Mian 16 维空间之坐标"
- 读法 D: 面 Mian = 元, 四象 = 爻 — 反向

故 R_6 至少有 **6 种** 元/爻配对读法 (3 路径 × 2 方向). 这是它"富结构"之具体含义.

## 8 · 道、真ₛ、(1,1)-quarter 在平方塔下之归位

参考用户在前几轮已澄清:
- **真ₛ** = predicate "Cell256 之末 2 bits = `oo`" = V₄ 之 dao-slice = 64 元素子集 = R_6 大小
- **道** = Cell256.origin = (Z/2)⁸ identity = `OX["oooooooo"]` = 1 元素
- **(1,1)-quarter** = "末 2 bits = `xx`" = V₄ 之 今-slice = 64 元素子集 = R_6 大小

在平方塔 R_8 = R_4 × R_4 = (Mian-元, Mian-爻) 视角下:

| 对象 | 表式 | 大小 | 平方塔身份 |
|------|-----|-----|-----------|
| 道 | (Mian-元 = 0, Mian-爻 = 0) | 1 | T_4 之零元 (双层全 substance / 全静) |
| 真ₛ slice | Mian-爻 之"末 2 bit = 0" 子集 × 全 Mian-元 | 64 | T_4 之 (R_4 × R_2) 子集 |
| (1,1) slice | Mian-爻 之"末 2 bit = 1" 子集 × 全 Mian-元 | 64 | T_4 之另一 (R_4 × R_2) 子集 |

### 8.1 "(1,1) 部分与 R_4 自相似"之精化

用户主张: "(1,1) 之 1/4 部分和 R_4 自相似".

在 R_8 = R_4 × R_4 视角下, **任何**固定一个 Mian-爻 值都给出 R_4 之一个 fiber (16 cells).
(1,1)-quarter 是 4 个 Mian-爻 值固定到末 2 bit = `xx` (其余 2 bit 可变), 故包含
4 × 16 = 64 = R_2 × R_4 = **4 个 R_4 fiber**.

故"与 R_4 自相似"之**精确含义** = **(1,1)-quarter 含 4 个 R_4 fiber, 每 fiber 与 R_4 同构**.

dao-slice (真ₛ) 同结构 — 也含 4 个 R_4 fiber. 二者作为 V_4 之 dao/今 极对应,
有相同 R_2 × R_4 = 64 结构, 互为 V_4 群下之最远 anti-pole.

### 8.2 道 与 (1,1)-quarter 之锚定

道 = 唯一一个外内 Mian 双零之 cell, 落在 dao-slice 内之 (qian, dao) 位.
其 V_4 对偶元 (`OX["xxxxxxxx"]`) 落在 (1,1)-quarter 内之 (kun, jin) 位.
这两 cell 是 R_8 之**两个 distinguished 角** — 定义平方塔之"自相似几何对称轴".

故"道和真ₛ — 最后两个位一直为真"之精确读法:
> 在平方塔 R_8 = R_4 × R_4 视角下, 真ₛ 不是"另一个 cell", 而是"末 2 bit = `oo` 之 slice 谓词".
> 道 ∈ 真ₛ slice. 平方塔之 (R_4 × R_2) 子结构 (真ₛ slice 或 (1,1)-quarter) 是**R_4 自相似嵌套**之
> "投影像" — 每 V_4 选择固定 → 一个 R_4 之 fiber 复制 4 份.

## 9 · "R_4 一次分叉自相似 = 宇宙" 之精确陈述

把所有上文综合, 用户假说 "R_4 一次分叉自相似 = 宇宙" 之**精确数学陈述**:

> **宇宙 = R_8 = T_4 = T_3 × T_3 = R_4 × R_4 = (Mian-元) × (Mian-爻)**
>
> 即: 宇宙是 16 元 Ben×Zheng 结构 (R_4) 与其自身的**一次**自相似嵌套 (R_4 → R_4²),
> 内层 Mian 提供 carrier (被分类之实虚态), 外层 Mian 提供 dimension (分类之本征轴).
> (或对偶反读: 内层提供 dimension, 外层提供 carrier — 二者皆 doctrine 合法.)
>
> 平方塔之"末步" (T_3 → T_4) 即"R_4 之一次分叉自相似 → R_8". 用户之"一次"=
> "塔深 k=3 → k=4 之一步, 即从 R_4 到 R_8 之单次平方".

## 10 · 与 codebase 形式化之关系

本规则在 codebase 已**隐式成立**:

- [Cell256Stratify.lean](../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) 之 (Z/2)ⁿ 严格 closure 即 R_n × R_m ≃+ R_{n+m}, 包含 R_n × R_n ≃+ R_{2n} 作为特例
- [BenZheng.lean:230](../formal/SSBX/Foundation/Bagua/BenZheng.lean:230) 之 `Mian := Ben × Zheng` 即 T_3 = T_2 × T_2 之具体落地
- [Cell256.lean](../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7.4 之 (Z/2)⁸ origin 群律保证 R_8 之分解之"无偏好性"

**未来可选之形式化扩展** (非本轮): 显式构造 `R_8 ≃+ R_4 × R_4` 之 AddEquiv, 给定文件
`Foundation/Squaring/R4SelfSquare.lean` (~80 LOC, 0 sorry). 但**已蕴含于现有 Cell256 group 律**,
新文件不引入新数学, 仅作 doctrine 锚.

## 11 · 三句话总结

1. **数学**: R_8 = R_4 × R_4 = R_2 × R_2 × R_2 × R_2 是 (Z/2)⁸ 之**平方塔分解**;
   平方塔 = {R_0, R_1, R_2, R_4, R_8}, 由 T_{k+1} = T_k × T_k (k ≥ 1) + R_0 + O_0 = R_1 之奠基步给出.

2. **本体论**: 每平方步两因子分担**元 (carrier) / 爻 (dimension)** 之非对称角色;
   实/虚 与 本/征 之配对方向是 doctrine 自由度, 不由群结构决定.

3. **形而上**: 宇宙 = R_8 = R_4 之一次平方分叉自相似; 道与真ₛ 是其末步 V_4 子结构之
   两个 distinguished 极 (identity 极 / PT 极), 锚定平方塔之自相似几何对称轴.

## 12 · 与其他 doctrine 文档之衔接

| 文档 | 关切 |
|------|-----|
| [yi-RO-hierarchy.md](../docs-next/10_formal_形式/yi-RO-hierarchy.md) | R₀..R₈ incrementing 全塔 (本文之 dual 视角) |
| [表六 256 全表](../六表_实虚史真/表六_256格全表.md) § 12 | 256 = R_6 × V_4 之主分解 (本文增 16×16 之 dual 读法) |
| [C_实虚史真.md](C_实虚史真.md) | modal / 史 / 真假 三轴 (本文之**真ₛ vs 真ₑ** 分由此而来) |
| [BenZheng.lean:230](../formal/SSBX/Foundation/Bagua/BenZheng.lean:230) | R_4 Mian = Ben × Zheng 之 Lean 落地 |
| [Cell256.lean § 1](../formal/SSBX/Foundation/Bagua/Cell256.lean) | V_4 Shi + 道 = origin 之 codebase 实现 |

— *Z_平方塔自相似规则.md v1, 2026-05-11. 概念哲学 doctrine, 不含 Lean. 本文之 §1-§3 + §9 总结
回答用户 2026-05-11 conversation 之"R4 一次分叉自相似 = 宇宙"假说.*
