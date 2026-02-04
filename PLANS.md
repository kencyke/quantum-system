# Plan: Relative Entropy Extension (Finite-Dim → Trace-Class → von Neumann)

## Goal

現在の有限次元密度行列で完成している結果を、次の順で拡張する。

1. `B(H)` 上のトレースクラス状態に対する相対エントロピーと単調性
2. 一般 von Neumann 代数上の正規忠実状態に対する Araki 相対エントロピーと単調性

最終目標は、正規 UCP 写像 `Φ` に対して

`S(ψ ∘ Φ | φ ∘ Φ) ≤ S(ψ | φ)`

を一般 von Neumann 文脈で定理化すること。

---

## Current Codebase Snapshot (Fact-Based)

### Completed (Finite-Dimensional Matrix Track)

- Lieb 凹性（Effros 方式）
  - `QuantumSystem/Analysis/Matrix/LiebConcavity.lean`
  - `lieb_joint_concavity_semidef`
  - `lieb_joint_concavity_rect_semidef`
- 相対エントロピーの単調性（DPI）
  - `QuantumSystem/Channel/Entropy.lean`
  - `relativeEntropy_channel_le`
  - `relativeEntropy_channel_eq_iff_recoverable`
- 関連補題
  - `trace_rpow_mul_channel_le`
  - `trace_rpow_mul_jointly_concave`
  - `relativeEntropy_jointly_convex`
- 密度行列・量子チャネル
  - `QuantumSystem/State/DensityMatrix.lean` — `IsDensityMatrix`, `DensityMatrix`, スペクトル補題
  - `QuantumSystem/Channel/QuantumChannel.lean` — `IsQuantumChannel`, Kraus 表現, CPTP 合成

### Completed (Operator-Algebra Track)

- von Neumann 代数基盤
  - `QuantumSystem/Algebra/VonNeumannAlgebra/Basic.lean` — WOT/SOT 閉性 ↔ 二重交換子, GNS VNA
- 巡回・分離ベクトル
  - `QuantumSystem/Algebra/VonNeumannAlgebra/Separating.lean` — 巡回 ↔ 交換子分離の完全な同値
- 正規状態（predual ベース定義）
  - `QuantumSystem/Algebra/VonNeumannAlgebra/NormalState.lean` — `WStarAlgebra.NormalState`, predual 対, 拡大
- 非有界作用素基盤
  - `Unbounded/Basic.lean` — `DenselyDefinedLinearMap`, 対称・正値性
  - `Unbounded/Adjoint.lean` — 随伴域, 自己共役判定
  - `Unbounded/Closable.lean` — 対称 ⇒ 閉包可能, 本質的自己共役
  - `Unbounded/Antilinear.lean` — 反線型写像, `Conjugation` (J² = id), グラフ閉包
- Tomita 作用素
  - `QuantumSystem/Algebra/VonNeumannAlgebra/TomitaOperator.lean`
  - `tomitaOperator₀` 定義, `S₀² = 1`, **`S₀` は閉包可能** (完全証明)
- トレースクラス基盤
  - `TraceClass/Def.lean` — `IsTraceClass`, `TraceClass H`, 代数構造
  - `TraceClass/Basic.lean` — `trace`, `traceNorm`, 基底独立性
  - `TraceClass/Dual.lean` — `toTraceClassDual`, 単射性, **`B(H)` は W\*-代数** (predual = trace-class)

### 現状の Tomita 作用素到達点（Phase B 前提の詳細）

完成済み:
- `S₀(xΩ) = x*Ω` の定義と well-definedness
- `S₀² = 1` (on domain)
- `S₀` の closability（グラフ閉包引数 + 巡回分離双対性経由）

未実装:
- `S = S₀` の閉包（closed extension）
- 極分解 `S = JΔ^{1/2}` （`J` = modular 共役, `Δ` = modular 作用素）
- `Δ` の自己共役性とスペクトル分解
- 相対 modular 作用素 `Δ_{φ,ψ}` の構成

---

## Main Gaps to Close

1. `B(H)` 文脈の「状態」「チャネル」「相対エントロピー」の統一 API が未整備
2. 正規 CP/UCP 写像（前双対を含む）を扱う専用レイヤーが未整備
3. Petz recovery map の明示的構成とチャネル性証明が未整備
4. トレースクラス作用素の関数計算（CFC）API が未整備（B(H) DPI の前提）
5. Modular theory の発展（`S₀` 閉包 → 極分解 → `Δ` → 相対 modular 作用素）が必要
6. 一般 von Neumann での Araki 相対エントロピー定義ファイルが未整備
7. 一般論 DPI の証明ルート（B(H) からの持ち上げ／modular data 経由）が未実装

---

## Strategy (Two-Stage)

### Stage A: `B(H)` + Trace-Class States を先に完成

理由: 現コード資産（TraceClass, Unbounded, finite-dimensional DPI）を最大再利用でき、一般 von Neumann へ最短で橋渡しできるため。

### Stage B: 一般 von Neumann 正規忠実状態へ持ち上げ

理由: Stage A で得る定義・不等式・回復写像を中核に、modular theory / standard form 側の不足を局所的に埋めて一般化できるため。

持ち上げ戦略: 一般 vN 代数 `M` を `B(H)` 上に忠実正規表現し、Araki 相対エントロピーを
standard form 上の相対 modular 作用素 `Δ_{ψ,φ}` のスペクトル積分として定義する。
DPI は `B(H)` 版 DPI + 正規 UCP 写像の Stinespring 拡張 + 条件付き期待値への帰着で証明する。

---

## Work Plan

## Phase A0: Notation & Readability (定理ステートメントの可読性向上)

目的: 定理ステートメントを数学・物理の論文・教科書に近い形にし、プロジェクト全体の可読性を向上させる。
既存の証明は壊さず、型シグネチャのみ書き換える。

### Task A0.1: `CoeFun` インスタンスと `QuantumChannel.apply` の統合

- 対象ファイル: `QuantumSystem/Channel/QuantumChannel.lean`
- 実装内容:
  - `QuantumChannel` に `CoeFun` を定義し、`Φ(ρ)` / `Φ ρ` で channel 適用を可能にする
    ```lean
    noncomputable instance : CoeFun (QuantumChannel n m)
        (fun _ => DensityMatrix n → DensityMatrix m) where
      coe := QuantumChannel.apply
    ```
  - 公開定理 3 本のシグネチャを `QuantumChannel` サブタイプ引数に変更:
    - `IsQuantumChannel.comp` → `(Φ : QuantumChannel n m) (Ψ : QuantumChannel m k)`
    - `IsQuantumChannel.map_isDensityMatrix` → `(Φ : QuantumChannel n m)`
    - `IsQuantumChannel.kraus_sum_eq_one` → `(Φ : QuantumChannel n m)`
  - proof 内は `hΦ` → `Φ.property`、`Φ A` (LinearMap) → `Φ.val A` に機械的置換
- 変更しないもの:
  - `IsCompletelyPositive.map_isHermitian` — CP 単独仮定として有用
  - `isQuantumChannel_id` — 構築側のため
- 受け入れ条件:
  - `Φ(ρ) : DensityMatrix m` が型チェックを通る
  - `lake build` がエラーなし

### Task A0.2: Scoped Notation の定義

- 新規ファイル: `QuantumSystem/Notation.lean`
- 実装内容:
  - `namespace QuantumInfo` 内に以下の scoped 記法を定義:

  | 記法 | 展開先 | 方式 |
  |---|---|---|
  | `Tr[A]` | `Matrix.trace A` | `notation` |
  | `S(ρ)` | `Matrix.vonNeumannEntropy ρ` | `notation` |
  | `D(ρ ‖ σ)` | `Matrix.relativeEntropy ρ σ` | `notation` |
  | `⟪X, Y⟫_HS` | `Matrix.hsInnerProduct X Y` | `notation` |
  | `supp(ρ) ⊆ supp(σ)` | `Matrix.suppSubset ρ σ` | `syntax` + `macro_rules`* |

  - *`supp(·) ⊆ supp(·)` のみ、`⊆` が既存 `HasSubset.Subset` 中置と衝突するため `syntax` + `macro_rules` を使用。他は `notation` で実現可能。
  - `QuantumSystem.lean` (ルート) と `scripts/mk_all.lean` に import 追加
- 受け入れ条件:
  - `open scoped QuantumInfo` 下で全記法が機能する
  - スコープ外では従来の関数名表示のまま

### Task A0.3: Entropy.lean の定理ステートメント書き換え

- 対象ファイル: `QuantumSystem/Channel/Entropy.lean`
- 実装内容:
  - ファイル冒頭に `open scoped QuantumInfo` を追加
  - 公開定理 2 本のシグネチャを `QuantumChannel` サブタイプに変更 + 記法適用:
    - `relativeEntropy_channel_le`:
      `(Φ : QuantumChannel n m) (ρ σ : DensityMatrix n) : D(Φ ρ ‖ Φ σ) ≤ D(ρ ‖ σ)`
    - `relativeEntropy_channel_eq_iff_recoverable`:
      `(Φ : QuantumChannel n m) ... (R : QuantumChannel m n) (hRρ : R (Φ ρ) = ρ) (hRσ : R (Φ σ) = σ) : D(Φ ρ ‖ Φ σ) = D(ρ ‖ σ)`
  - private helper 3 本も同様に `QuantumChannel` サブタイプに変更
  - 他の公開定理ステートメントに記法を適用:
    - `vonNeumannEntropy_nonneg` : `0 ≤ S(ρ)`
    - `vonNeumannEntropy_eq_sum` : `S(ρ) = ∑ i, ...`
    - `vonNeumannEntropy_le_log_dim` : `S(ρ) ≤ Real.log ...`
    - `vonNeumannEntropy_concave` : `S(⟨mix, hρ⟩) ≥ p * S(ρ₁) + (1 - p) * S(ρ₂)`
    - `relativeEntropy_nonneg` : `0 ≤ D(ρ ‖ σ)`
    - `relativeEntropy_eq_zero_iff` : `D(ρ ‖ σ) = 0 ↔ ρ.val = σ.val`
    - `relativeEntropy_jointly_convex` : `D(⟨mix_ρ, hρ⟩ ‖ ⟨mix_σ, hσ⟩) ≤ p * D(ρ₁ ‖ σ₁) + ...`
  - proof 内部は改変しない（`hΦ` → `Φ.property` 等の機械的置換のみ）
- 受け入れ条件:
  - `lake build` がエラーなし
  - 主要定理の `#check` が期待通りの記法で pretty-print される

### Task A0.4: LiebConcavity.lean の記法書き換え（任意）

- 対象ファイル: `QuantumSystem/Analysis/Matrix/LiebConcavity.lean`
- 実装内容:
  - `hsInnerProduct` → `⟪·, ·⟫_HS` 記法
  - `.trace` → `Tr[·]` 記法（定義 / ステートメントのみ）
- 受け入れ条件:
  - `lake build` がエラーなし

### 設計判断

| 項目 | 判断 | 理由 |
|---|---|---|
| `Φ(ρ)` の実現方式 | `CoeFun` インスタンス | `⊛` 等の特殊記法不要。Lean の自然な関数適用構文 |
| 記法の scope | `scoped` in `QuantumInfo` | `open scoped QuantumInfo` で有効化。AGENTS.md 禁止の `QuantumSystem` namespace を回避 |
| 記法の実装方式 | `notation` 優先、`⊆` 衝突箇所のみ `syntax` + `macro_rules` | 簡潔かつ保守的 |
| 定理の仮定形式 | `(Φ : QuantumChannel n m)` サブタイプ引数 | `{Φ : …} (hΦ : IsQuantumChannel Φ)` よりステートメントが簡潔。`CoeFun` と組み合わせで `Φ(ρ)` が可能に |
| `IsCompletelyPositive.map_isHermitian` | 変更しない | CP 単独仮定の定理として有用 |
| `isQuantumChannel_id` | 変更しない | `IsQuantumChannel` を構築する定理であり、消費する定理ではない |

## Phase A1: Trace-Class State API

### Task A1.1: トレースクラス状態の構造体

- 新規ファイル: `QuantumSystem/State/TraceClassState.lean`
- 実装内容:
  - トレースクラス正作用素かつトレース 1 を状態とする構造体
  - coercion / ext / 基本補題（`trace_eq_one`, positivity）
  - 凸結合が状態であること
- 受け入れ条件:
  - 密度行列（有限次元）からの埋め込みが定義できる

### Task A1.2: 有限次元との整合（スコープ限定）

- 新規ファイル: `QuantumSystem/State/TraceClassState/FiniteDim.lean`
- スコープ:
  - `Matrix n n ℂ` → `EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n` の埋め込み
  - 埋め込みがトレースクラスであること
  - `trace` の一致（`Matrix.trace` = `TraceClass.trace`）
- スコープ外（Phase A3 に延期）:
  - エントロピー量の一致（相対エントロピー定義後に扱う）
- 受け入れ条件:
  - 型変換 + trace 一致が証明済み

---

## Phase A2: Normal CP/UCP Map Layer on `B(H)`

### Task A2.1: 正規 CP/UCP 写像の定義

- 新規ファイル: `QuantumSystem/Algebra/VonNeumannAlgebra/NormalCPMap.lean`
- 設計方針:
  - 正規性は **predual ベース** で定義（既存 `WStarAlgebra.IsNormal` と統一）
  - CP 性は **amplification の正値性** で定義（`id ⊗ Φ` が正値）
    - 有限次元の `IsCompletelyPositive`（Kraus 表現ベース）との同値は別途証明
  - UCP = CP + `Φ(1) = 1`
  - TP = trace-preserving（前双対が unital）
- 実装内容:
  - `IsNormalCPMap`, `IsNormalUCPMap`, `IsNormalChannel` 述語
  - 合成・恒等・基本演算
  - `B(H)` 上の Stinespring 表現定理（statement のみまたは証明）
- 受け入れ条件:
  - `B(H)` でチャネルとして使える最小インターフェースが完成

### Task A2.2: 前双対作用

- 同ファイルまたは `NormalCPMap/Predual.lean`
- 実装内容:
  - チャネルの前双対作用（state pushforward / pullback）
  - 正規状態を正規状態へ写す補題
  - CP 写像の Choi-Jamiołkowski 対応（必要範囲）
- 受け入れ条件:
  - DPI の statement に必要な型が閉じる

---

## Phase A3: Relative Entropy on Trace-Class States

### Task A3.1: 定義と基本性質

- 新規ファイル: `QuantumSystem/State/TraceClassState/Entropy.lean`
- 実装内容:
  - Umegaki 型相対エントロピーの定義: `S(ρ‖σ) = Tr[ρ(log ρ - log σ)]`
    - `supp(ρ) ⊆ supp(σ)` のとき有限値、それ以外 `+∞`
  - 有限値条件（support 条件）
  - 有限次元との整合:
    - `TraceClassEntropy` = `relativeEntropy` （bridge 経由、A1.2 を使用）
- 受け入れ条件:
  - 非負性（Klein 不等式の TC 版）
  - 等号条件 `S(ρ‖σ) = 0 ↔ ρ = σ`

### Task A3.2: トレースクラス関数計算 API

- 新規ファイル: `QuantumSystem/Analysis/CFC/TraceClass/FunctionalCalculus.lean`
- 実装内容:
  - (a) 正値トレースクラス作用素の CFC（`f(T)` がトレースクラスである条件）
  - (b) `Tr[f(T)]` の ONB 表示との関係
  - (c) `T^s` (実べき) のトレースクラス性（`0 < s ≤ 1` の範囲で）
- 受け入れ条件:
  - DPI 証明で使う `F_s(ρ,σ) = Tr[ρ^s σ^{1-s}]` が well-defined

### Task A3.3: B(H) 版 DPI

- 新規ファイル: `QuantumSystem/State/TraceClassState/DPI.lean`
- 証明戦略: 有限次元 DPI の骨格（`F_s` 不等式 + 微分引数）の TC 版を構成
  - (a) `F_s(ρ,σ) = Tr[ρ^s σ^{1-s}]` の TC 版定義（Task A3.2 に依存）
  - (b) `F_s` のチャネル単調性: `F_s(Φ(ρ),Φ(σ)) ≤ F_s(ρ,σ)` （Lieb 凹性の TC 拡張）
  - (c) `s ↦ F_s` の s=1 での微分 = 相対エントロピー（TC 版 `hasDerivAt_trace_rpow_mul`）
  - (d) 微分不等式から DPI を導出
- 受け入れ条件:
  - `relativeEntropy_traceClass_channel_le` が証明済み
  - 有限次元定理が特別場合として recover できる

### Task A3.4: Petz Recovery Map（B(H)）

- 新規ファイル: `QuantumSystem/State/TraceClassState/PetzRecovery.lean`
- 実装内容:
  - Petz map の明示式定義:
    `R_{σ,Φ}(X) = σ^{1/2} Φ*(Φ(σ)^{-1/2} X Φ(σ)^{-1/2}) σ^{1/2}`
  - 正規 CP/UCP 性（Stinespring + Schwarz 不等式経由）
  - 回復仮定から等号成立の定理
- 受け入れ条件:
  - `relativeEntropy_channel_eq_iff_recoverable` の `B(H)` 対応版を提供

---

## Phase A4: Modular Theory 基盤

Phase B の前提となる modular theory を整備する。
現状 `TomitaOperator` は `S₀` の定義と closability まで完成。

### Task A4.1: Tomita 作用素の閉包と極分解

- 新規ファイル: `QuantumSystem/Algebra/VonNeumannAlgebra/ModularTheory/PolarDecomposition.lean`
- 実装内容:
  - `S = closure(S₀)` の構成（既存 `IsClosable` + `closure` を使用）
  - 極分解 `S = JΔ^{1/2}` の構成
    - `Δ = S*S` （非有界正自己共役作用素）
    - `J` = modular 共役（反線形等距写像, `J² = id`）
  - `J` の基本性質: `JMJ = M'`（Tomita の定理の核心部分）
- 受け入れ条件:
  - `Δ`, `J` が well-typed で基本恒等式を持つ

### Task A4.2: Modular 自己同型群

- 新規ファイル: `QuantumSystem/Algebra/VonNeumannAlgebra/ModularTheory/AutomorphismGroup.lean`
- 実装内容:
  - `σ_t(x) = Δ^{it} x Δ^{-it}` の定義
  - `σ_t` が `M` の *-自己同型であること
  - KMS 条件の statement
- 受け入れ条件:
  - Araki 相対エントロピー定義に必要な `Δ^{it}` が使える

### Task A4.3: 相対 Modular 作用素

- 新規ファイル: `QuantumSystem/Algebra/VonNeumannAlgebra/ModularTheory/RelativeModular.lean`
- 実装内容:
  - 2 状態 `φ, ψ` に対する相対 modular 作用素 `Δ_{ψ,φ}` の構成
  - 非有界自己共役作用素のスペクトル測度との接続
    - Mathlib の `spectralMeasure` / `IsSelfAdjoint` が使える範囲を確認
    - 不足分は必要最小限で構成
- 受け入れ条件:
  - `Δ_{ψ,φ}` が well-typed でスペクトル積分 `∫ f(λ) dE(λ)` が定義可能

---

## Phase B1: General von Neumann Relative Entropy

### Task B1.1: Araki 相対エントロピー定義

- 新規ファイル: `QuantumSystem/Algebra/VonNeumannAlgebra/RelativeEntropy/Definition.lean`
- 実装内容:
  - 正規忠実状態 `φ, ψ` に対する Araki 相対エントロピー:
    `S(ψ|φ) = -⟨ξ_ψ, (log Δ_{φ,ψ}) ξ_ψ⟩`
    （`ξ_ψ` は `ψ` の standard form ベクトル代表）
  - 既存 `NormalState`, `TomitaOperator`, Phase A4 の modular theory と接続
  - `B(H)` の場合に Umegaki 型定義（Task A3.1）と一致する補題
- 受け入れ条件:
  - 定義が well-typed で基本不変量補題を持つ
  - 非負性

### Task B1.2: 一般論単調性

- 新規ファイル: `QuantumSystem/Algebra/VonNeumannAlgebra/RelativeEntropy/Monotonicity.lean`
- 証明戦略:
  - 正規 UCP 写像 `Φ: M → N` に対し、Stinespring 型拡張で `B(H)` に持ち上げる
  - `B(H)` 版 DPI（Task A3.3）を適用
  - 条件付き期待値（conditional expectation）への帰着で不等式を得る
- 実装内容:
  - 正規 UCP 写像に対する DPI
- 受け入れ条件:
  - 目標定理 `S(ψ ∘ Φ | φ ∘ Φ) ≤ S(ψ | φ)` が証明済み

---

## Phase B2: Equality / Recovery (General vN)

### Task B2.1: Recovery sufficient condition

- 新規ファイル: `QuantumSystem/Algebra/VonNeumannAlgebra/RelativeEntropy/Recovery.lean`
- 実装内容:
  - 回復写像が存在する場合の等号成立
- 受け入れ条件:
  - finite-dimensional / `B(H)` / general の statement が整列

### Task B2.2: Petz 形式との接続（可能範囲）

- 実装内容:
  - 一般 vN での Petz 形式の表現（必要に応じ公理化を併用）
- 受け入れ条件:
  - ドキュメント上に「構成済み」「公理化」「未完」を明確区分

---

## File Layout

```
QuantumSystem/
  Notation.lean                             (A0.2)
  State/
    DensityMatrix.lean                    (既存)
    TraceClassState.lean                  (A1.1)
    TraceClassState/
      FiniteDim.lean                      (A1.2)
      Entropy.lean                        (A3.1)
      DPI.lean                            (A3.3)
      PetzRecovery.lean                   (A3.4)
  Analysis/CFC/TraceClass/
    Def.lean                              (既存)
    Basic.lean                            (既存)
    Dual.lean                             (既存)
    FunctionalCalculus.lean               (A3.2)
  Algebra/VonNeumannAlgebra/
    Basic.lean                            (既存)
    NormalState.lean                      (既存)
    Separating.lean                       (既存)
    TomitaOperator.lean                   (既存)
    NormalCPMap.lean                       (A2.1)
    NormalCPMap/
      Predual.lean                        (A2.2)
    ModularTheory/
      PolarDecomposition.lean             (A4.1)
      AutomorphismGroup.lean              (A4.2)
      RelativeModular.lean                (A4.3)
    RelativeEntropy/
      Definition.lean                     (B1.1)
      Monotonicity.lean                   (B1.2)
      Recovery.lean                       (B2.1)
```

---

## Dependency Order (Execution)

```
A0.1 CoeFun + QuantumChannel シグネチャ変更
 ↓
A0.2 Scoped Notation 定義 (Notation.lean)
 ↓
A0.3 Entropy.lean ステートメント書き換え
 ↓
A0.4 LiebConcavity.lean 記法書き換え (任意)
 ↓                                          ← A0 完了
A1.1 TraceClassState
 ↓
A1.2 FiniteDim Bridge  (スコープ限定: 型変換 + trace 一致のみ)
 ↓
A2.1 NormalCPMap (predual ベース CP/UCP/TP 定義)
 ↓
A2.2 前双対作用
 ↓
A3.1 TraceClassEntropy (定義 + 非負性 + 有限次元一致)
 ↓
A3.2 TraceClass CFC API (Tr[ρ^s σ^{1-s}] の well-definedness)
 ↓
A3.3 B(H) DPI (F_s 不等式 + 微分引数の TC 版)
 ↓
A3.4 Petz Recovery (B(H))
 ↓                                          ← M1 完了
A4.1 極分解 S = JΔ^{1/2}
 ↓
A4.2 Modular 自己同型群
 ↓
A4.3 相対 Modular 作用素 Δ_{ψ,φ}
 ↓                                          ← M2 完了
B1.1 Araki 相対エントロピー定義
 ↓
B1.2 一般論 DPI
 ↓
B2.1 Recovery (一般 vN)
 ↓
B2.2 Petz 形式接続                          ← M3 完了
```

---

## Milestones

### M1 (Short-Term)

- `B(H)` トレースクラス状態上で
  - 相対エントロピー定義
  - 単調性（DPI）
  - Petz recovery sufficient condition
  が揃う。
- ボトルネック: Task A3.2（TC 関数計算）+ A3.3（TC 版 DPI）が工数の大半を占める。

### M2 (Mid-Term)

- 一般 von Neumann 正規忠実状態で Araki 相対エントロピーの定義が完成。
- 前提: Phase A4（Modular Theory 基盤）の完成が必須。
  `S₀` closability は証明済みだが、極分解・`Δ` のスペクトル分解は未実装。

### M3 (Final)

- 一般 von Neumann 正規忠実状態 + 正規 UCP map で単調性定理を完成。
- 証明ルート: B(H) DPI + Stinespring 拡張 + 条件付き期待値。

---

## Risk Assessment

| リスク | 影響 | 緩和策 |
|--------|------|--------|
| TC 関数計算 API (A3.2) の工数膨張 | M1 遅延 | CFC の Mathlib 依存度を先に調査。必要最小限に絞る |
| `Matrix → ContinuousLinearMap` bridge (A1.2) の複雑さ | A3.1 遅延 | スコープを trace 一致のみに限定済み |
| Mathlib のスペクトル測度 API 不足 (A4.3) | M2 遅延 | 非有界自己共役作用素の CFC を独自構成する覚悟を持つ |
| Stinespring 拡張の一般 vN 版 (B1.2) | M3 遅延 | `B(H)` 版を先に固め、一般化は公理化で段階的に進める |

---

## Coding Rules for This Plan Execution

- 既存有限次元結果を再利用し、不要な再証明を避ける。
- 先に API と最小定理を固め、その後に強い一般化を入れる。
- 進捗は「実装済み / 公理化 / 未着手」を必ず明示する。
- 大規模補題は小分けにして、`lake build` を段階ごとに通す。
- 各タスク着手前に Mathlib の既存 API を `grep` / `lean_loogle` で調査し、再発明を避ける。

---

## Immediate Next Action

次の実装ステップは `QuantumSystem/State/TraceClassState.lean` の新設。
ここで「状態」の統一表現を導入し、既存 `DensityMatrix` との橋渡しを始める。
