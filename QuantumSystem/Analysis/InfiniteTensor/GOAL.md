# InfiniteTensor 層の目標

このディレクトリの目的は、von Neumann 1939 の無限テンソル積を
それ自体の完全な再現として形式化することではなく、
**代数的場の理論 (AQFT) を展開するために十分な無限テンソル積の基盤**を
整備することである。

本リポジトリでは、局所ネット、準局所 C\*-代数、真空ベクトル、
共変性、GNS 表現、KMS / modular theory、相対エントロピーなどを
最終的な展開対象とする。そのため InfiniteTensor 層は、
AQFT 側の表現空間と局所作用素の受け皿として機能するところまで
拡充されていればよい。

## 目標

InfiniteTensor 層の到達目標は次である。

1. 不完全無限テンソル積 sector `ITPSector Ω` を安定に扱えること。
2. weak equivalence (`c0Rel`) による sector 分解を扱えること。
3. 任意 sector 上に有限領域の局所作用素を持ち上げられること。
4. 群作用による sector transport と共変性を、合成則を含めて扱えること。
5. AQFT 側の局所ネット・準局所代数・状態・GNS 構成に自然に接続できること。

言い換えると、InfiniteTensor 層は
「場の理論の数学を展開するための Hilbert 空間・sector・局所作用 API」
を与えるところまで完成していれば十分である。

## これが揃えば十分

AQFT の基礎展開に十分な条件は、少なくとも以下である。

### 1. 基本 sector 構成

- `UnitFamily`
- `regionTensor`
- `preITPSector`
- `ITPSector`
- 有限領域からの埋め込みと稠密性

これは「有限領域のテンソル積を無限体積へ極限する」ための最小核であり、
すでにかなり整っている。

### 2. sector 分解と sector 間輸送

必要なのは、単に sector が存在することだけではない。

- `c0Equiv` による sector の商構造
- `decomposableTensorProduct`
- `sectorEmbed Ω : ITPSector H Ω →ₗᵢ[ℂ] decomposableTensorProduct H`
- `c0Rel Ω Ω'` から sector 同型を作る標準 API
- 合成・逆・恒等を満たす coherent transport API

ここで重要なのは、AQFT では「同型がある」だけでは足りず、
群作用や sector の貼り合わせに使える**関手的な transport**が必要になる点である。

### 3. 局所作用素の pure-layer extension

有限領域の作用素を任意 sector 上に持ち上げる pure-layer API が必要である。

少なくとも以下の性質を持つべきである。

- 加法・スカラー倍・零写像に関する両立性
- 単位元・積・随伴に関する両立性
- isotony との両立性
- disjoint region での可換性
- reference sector では既存の lattice-side API と一致すること
- 作用素ノルム評価が取れること

これは AQFT では `B^#` よりも優先度が高い。場の理論でまず必要なのは、
局所代数が各 sector にどう作用するかであって、
von Neumann 1939 の作用素環分類そのものではないからである。

### 4. 共変性の functoriality

AQFT では、群作用は単なる点ごとの同型ではなく、
`U_g U_h = U_{gh}` を満たす表現として使える必要がある。

したがって、最終的には

- reindexed transport
- decomposable space 上の unitary action
- identity / multiplication laws

が揃っていることが望ましい。

### 5. 状態・GNS・熱力学との接続

InfiniteTensor 層そのものにすべてを押し込む必要はないが、
少なくとも以下へ自然に接続できるべきである。

- reference / product state
- vacuum vector / vacuum functional
- GNS 表現
- KMS state
- modular theory
- relative entropy

InfiniteTensor 層は、これらの理論が生きる Hilbert 空間の側を
安定に供給する役割を担う。

## 現在の進捗

2026-05-17 時点では、優先度 A のうち `sectorEmbed` と pure-layer の局所作用素
extension は実装済みであり、sector transport も bare API と coherent API の両方が
入っている。ただし、`c0Rel` から得る transport はまだ Bratteli–Robinson 的に
canonical な位相正規化版ではなく、`Classical.choice` を使う noncanonical な層が
残っている。下流接続は reference sector / lattice-side が先行しており、
arbitrary sector から state / GNS / KMS / modular theory へ直結する層は未完了である。

### 実装済み / 概ね実装済み

- `UnitFamily`
- `regionTensor`
- `preITPSector`
- `ITPSector`
- 有限領域からの埋め込みと稠密性
- `c0Rel` と `c0Equiv`
- `decomposableTensorProduct`
- `sectorEmbed Ω : ITPSector H Ω →ₗᵢ[ℂ] decomposableTensorProduct H`
- `sectorEquivOfEquivalent : c0Rel Ω Ω' → ITPSector H Ω ≃ₗᵢ[ℂ] ITPSector H Ω'`
- `SectorEquivData` / `C0SectorMorphism`
- `ReindexedSectorTransportData` による reindexed transport の forward API
- `extendOpLe` / `liftToSectorPre` / `liftToSector`
- pure-layer local operator extension の加法・スカラー倍・零・単位・積・随伴・
  isotony・disjoint region での可換性・作用素ノルム評価

### 継続中の課題

- `sectorEquivOfEquivalent` は `c0Rel` witness を受ける canonical な BR ルートではなく、
  `Classical.choice` による noncanonical rotation を経由している。
- coherent transport API はあるが、decomposable space 上の群表現として
  `U_g U_h = U_{gh}` を bundled に満たす最終形はまだ未整理である。
- AQFT 下流との接続は reference sector 側が中心であり、arbitrary sector /
  decomposable space から vacuum / state / GNS / KMS / modular theory /
  relative entropy へ自然に流れる API は未完成である。
- 既存の lattice-side `Classical.choice` 依存の削減は継続課題である。

## 優先順位

進捗記号は `[x] = 完了`, `[~] = 進行中`, `[ ] = 未着手` とする。

### 優先度 A: 直近で必要

1. `[x]` `sectorEmbed` の実装
2. `[~]` `c0Rel` に基づく sector transport の標準化
3. `[x]` pure-layer の局所作用素 extension
4. `[~]` 既存の lattice-side `Classical.choice` 依存箇所の削減

### 優先度 B: AQFT を綺麗に展開するために有益

1. `[~]` `SectorEquivData` / `C0SectorMorphism` を中心にした coherent API の整備
2. `[~]` group action の functoriality
3. `[ ]` finite excitation / ONB / separability を使う補助 API

### 優先度 C: 後回しでよい

1. `[ ]` von Neumann 1939 の full non-separable complete tensor product
2. `[ ]` `B^#`
3. `[ ]` Theorem IX / X
4. `[ ]` type `(II_1)` factor の古典的構成
5. `[~]` scalar-diagonal `U(z_α)` の完全な canonical 実装

これらは数学的には重要だが、AQFT の基礎を進めるための最短経路ではない。

## 当面の非目標

現段階では、以下を InfiniteTensor 層の完成条件にしない。

- von Neumann 1939 を定理番号まで完全に網羅すること
- non-separable な full complete tensor product を構成すること
- `B^#` の完全な理論を構成すること
- 作用素環の型分類そのものを主対象にすること

これらは、AQFT の local net / state / representation theory を
ある程度展開した後で、必要が生じた段階で扱えばよい。

## 完了条件

InfiniteTensor 層は、次が満たされた時点で AQFT 目的には十分とみなす。

1. reference sector と arbitrary sector の両方で local operator action が定義される。
2. decomposable sector space に各 sector を埋め込める。
3. sector transport が coherent で、共変性の議論に使える。
4. 下流の Haag-Kastler / quasi-local algebra / vacuum / state の議論が、
	ad hoc な choice に頼らずに記述できる。
5. 主要モジュールとその import 先が `lake build` で安定に通る。

## 方針

要するに、この層の目標は

> 「von Neumann 1939 を最後まで再現すること」ではなく、
> 「AQFT の Hilbert 空間・sector・局所作用の言語を十分に与えること」

である。

その意味で、まず完成させるべきなのは
**incomplete sectors + weak sector decomposition + coherent transport + local operator extension**
であり、`B^#` や Theorem IX/X は後段の課題とする。
