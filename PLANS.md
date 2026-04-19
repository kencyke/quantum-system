# Plan: SegalEntropy データ構造リファクタリング — パラメータ削減

---

## 推奨プラン: proof 内で導出可能な仮定の削除

プロジェクト全体を調査し、シグネチャ上で明示されているが proof 内で導出可能、
または完全に未使用（`_` prefix）の仮定を **9 件** 特定した。

### Phase 1: 未使用パラメータの削除（安全・機械的）

| # | ファイル | 関数 | 削除対象 | 理由 |
|---|---------|------|---------|------|
| 1 | `Analysis/CFC/TraceClass/Log.lean` | `trace_mul_cfc_eq_tsum` | `_hσ_nonneg : ∀ i, 0 ≤ σ i` | 未使用。`hT_pos` + `hσ_eig` から導出可能（正作用素の固有値は非負） |
| 2 | `Analysis/Entropy/TraceClassRelativeEntropy.lean` | `trace_mul_cfc_cross_eq_tsum` | `_hρ_pos : 0 ≤ (ρ : H →L[ℂ] H)` | 未使用 |
| 3 | 同上 | 同上 | `_hμ_nonneg : ∀ j, 0 ≤ μ j` | 未使用 |
| 4 | `Analysis/CFC/Compact.lean` | `positive_compact_eq_tsum_rankOne` | `_hA_pos`, `_hA_comp` | 両方未使用。固有基底があれば正値性・コンパクト性は不要 |
| 5 | `Analysis/CFC/TraceClass/Def.lean` | `isTraceClass_absoluteValue_of_isTraceClass` | `_ι`, `_b` | 未使用。証明内で別の基底を `intro` している |
| 6 | `Analysis/Entropy/RelativeEntropy.lean` | `hasDerivAt_double_rpow_sum` (private) | `_hw : ∀ i j, 0 ≤ w i j` | 未使用 |

**作業手順**: シグネチャから削除 → 呼び出し元を grep で特定 → 対応する引数を削除 → `lake build`

### Phase 2: TypeClass から導出可能な仮定の削除

| # | ファイル | 関数 | 削除対象 | 導出方法 |
|---|---------|------|---------|---------|
| 7 | `Channel/TraceClass.lean` | `tcRelativeEntropy_condExp_le` | `hρEρ_tc : IsTraceClass (...)` | `[HasRelLogTC ρ (E.toChannel ρ)]` の `.isTraceClass` で代替可能。`hKlein` 内の `⟨..., hρEρ_tc⟩` を `⟨..., HasRelLogTC.isTraceClass⟩` に書き換え |

**注意**: `hρEσσ_tc` は `HasRelLogTC` がカバーしない式（`ρ * (log Eσ − log σ)`）なので残す。
`hKlein` と `hJensen` は Klein 不等式・作用素 Jensen 不等式という深い数学的事実であり、
現状では仮定として残すのが適切。

### Phase 3: 調査済み — 削除不可（数学的に非自明な仮定）

| # | ファイル | 関数 | 仮定 | 理由 |
|---|---------|------|------|------|
| 8 | `Algebra/VonNeumannAlgebra/SegalEntropy.lean` | `tcVonNeumannEntropy_le_zero` | `hρI_pos : 0 ≤ logDiff ρ ⟨1, hI_tc⟩` | Klein 不等式の結果。証明には別定理が必要 |
| 9 | 同上 | `segalEntropy_mono` | `hρEρ_pos : 0 ≤ logDiff ρ_tc (E.toChannel ρ_tc)` | 作用素 Jensen 不等式。同上 |

これらは将来 Klein 不等式・Jensen 不等式を定理として形式化した際に削除可能になる。

### 実施順序と検証

1. Phase 1 を一括実施 → `lake build` で検証
2. Phase 2 を実施 → `lake build` で検証
3. Phase 3 は将来課題として記録のみ

### 影響範囲の見積もり

- Phase 1: 各パラメータの呼び出し元は 0〜2 箇所（`_` prefix = 未使用なので呼び出し元でも不要な引数を渡しているだけ）
- Phase 2: `tcRelativeEntropy_condExp_le` の呼び出し元は 1 箇所（`segalEntropy_mono` 内から間接利用）

---

## 今後の検討事項

1. **`tcRelativeEntropy` の `IsTraceClass` 引数の完全 class 化 vs `if IsTraceClass then ... else ⊤`**:
   class 化を推奨（呼び出し側の可読性が大幅向上）。ただし定義変更を伴うため慎重に実施。

2. **`NormalState.extension` の abbreviation 化**: 論文表記 `ω̃` に対応するが Unicode 入力の実用性を考慮し `ω.ext` 程度が現実的。

3. **将来の Mathlib upstream**: abbreviation / class の命名規則を Mathlib convention に揃えておくと将来の contribute が容易。
