# GPU 有効化後の確認手順

devcontainer に GPU を渡す設定（`devcontainer.json` の `"runArgs": ["--gpus", "all"]`）
は**コンテナの再ビルドで初めて効く**。再ビルドすると実行中のセッションは消えるため、
この確認手順をワークスペース内に残している。**このファイルだけ読めば、GPU が正しく
使えているかを判定できる**ように書いてある。

前提: ホストは Windows + Docker Desktop（NVIDIA ランタイム同梱）、GPU は VRAM 8GB。
Windows 側に NVIDIA ドライバが入っていればよく、**WSL やコンテナの中に Linux 用
ドライバを入れてはいけない**（壊れる）。

## 1. 再ビルド

VS Code のコマンドパレット → **Dev Containers: Rebuild Container**。

`onCreateCommand` が 2 つのキャッシュ volume（`uv-cache` と `hf-models`）を
`vscode` 所有に直し、続く `postCreateCommand` が `lake exe cache get` と `uv sync`
を再実行する（`uv sync` は `pyproject.toml` の `default-groups` に従い dev と mineru の
両方を入れる。`six` も `mineru` グループに入っている ── mineru 3.4.5 の未宣言依存で、
無いと変換が `No module named 'six'` で全滅する。実測済み。torch は同じ
`pyproject.toml` で cu128 wheel に固定してある ── 理由は §3）。mineru の wheel
（torch 含む ~4GB）は `uv-cache` volume に、モデルは `hf-models` volume に
キャッシュされているので、2 回目以降の再ビルドは大幅に速い。

## 2. GPU がコンテナに見えているか

```bash
nvidia-smi
```

**期待**: GPU 名と `8192MiB` 前後のメモリ表を表示。
`command not found` や `Failed to initialize NVML` の場合は §7 へ。

## 3. torch が CUDA を認識しているか

torch は `mineru` グループの一部としてプロジェクト venv に入っている:

```bash
.venv/bin/python -c "import torch; print(torch.__version__, torch.version.cuda, torch.cuda.is_available(), torch.cuda.get_device_name(0) if torch.cuda.is_available() else '-')"
```

**期待**: `2.11.0+cu128 12.8 True <GPU 名>`。

`False` の場合、`nvidia-smi` が通っているなら torch のビルドを 2 段で疑う
（`.venv/bin/python -c "import torch; print(torch.version.cuda)"`）:

1. `None` なら CPU 版 wheel。`uv sync --group mineru --reinstall` で入れ直す。
2. 値があるのに `False` なら、**wheel の CUDA 世代がホストドライバより新しい**。
   警告に `The NVIDIA driver on your system is too old (found version 12080)` の
   ような行が出る（12080 = CUDA 12.8 = ホストの現在値）。`nvidia-smi` 右上の
   `CUDA Version` が wheel の `torch.version.cuda` より小さければこれ。実測: PyPI
   既定の `2.13.0+cu130` は driver 580 系以降を要求し、このホスト（573.22 /
   CUDA 12.8）では初期化に失敗して CPU に落ちていた。

2 を避けるため、`pyproject.toml` は torch/torchvision を **cu128 index に固定**して
いる（`[[tool.uv.index]] pytorch-cu128` と `[tool.uv.sources]`、torch は `<2.12`
── cu128 wheel は torch 2.11 で打ち止め）。ホストのドライバを 580 系以降に更新した
なら、この固定を外して既定 wheel に戻してよい。

## 4. 実 PDF の変換が GPU で速くなっているか

**arXiv の pdf URL を渡しても MinerU は通らない**: ingest.py は URL から arXiv id を
復元して rung 1（LaTeX）に落とす（仕様。そちらが厳密に良い）。GPU を測るには PDF を
ローカルに落として**パスで**渡す:

```bash
curl -L -o /tmp/paper.pdf https://arxiv.org/pdf/1702.04924
time uv run .claude/skills/math-extract/scripts/ingest.py /tmp/paper.pdf \
  --allow-mineru --pages 1-5 --cache-dir /tmp/gpu-check
```

**期待**:
- JSON に `"stage": "mineru-pipeline"`、`"ok": true`。
- 所要時間が CPU 時より短い。実測（RTX 4060 Laptop、arXiv:1702.04924 の 5 ページ、
  `--pages 1-5`、モデルはキャッシュ済み）: **GPU 22 秒 / CPU 60 秒**
  （`MINERU_DEVICE_MODE=cpu` で同じ PDF を再実行。CPU 側は 20 コアを使い切って
  user 7 分 9 秒）。モデル取得を含む初回は 1 分 17 秒。
  **倍率は 3 倍弱で、「CPU は数分」ではない** ── 従来の CPU 基準は別の文献で
  測ったものらしく、この文献では再現しなかった。GPU 判定は倍率ではなく、
  次のメモリ確認で行うのが確実。
- デバイスの直接確認は `nvidia-smi` を並走させる。ingest.py は mineru の stderr を
  捕まえて成功時には出さないので、ログで `cuda` を探すことはできない。変換中に
  `nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv,noheader` を
  数秒おきに叩き、メモリが上がることを見る（実測: 待機 1.5GB → 変換中 3.8GB）。
  WSL2 では `--query-compute-apps` はプロセスを出さないので、空でも異常ではない。

初回はモデルのダウンロード（pipeline で ~0.6GB、hybrid-engine はさらに VLM 分）が
走る。`hf-models` volume に入るので 2 回目以降は走らない。事前に落としておきたい
場合は `mineru-models-download`。

## 5.（任意）hybrid-engine を試す

精度 95%（pipeline は 86%）だが、**VRAM 8GB はこのバックエンドの最低ラインで、
しかも Windows デスクトップと共有**のため OOM しうる。試すなら:

```bash
uv run .claude/skills/math-extract/scripts/ingest.py <PDF> \
  --allow-mineru --backend hybrid-engine --effort high --cache-dir /tmp/gpu-check
```

- **成功したら**: 数式が濃い文献ではこちらを使う価値がある。VRAM に余裕を作るには
  実行前に Windows 側の GPU 消費（ブラウザのハードウェアアクセラレーション等）を
  減らす。実測（同じ 5 ページ、Windows が 1.5GB を使っている状態）: **OOM せず
  2 分 42 秒**で完了 ── pipeline の 22 秒に対し約 7 倍で、常用ではなく数式が濃い
  文献に限って選ぶ、という前提は変わらない。
- **`CUDA out of memory` で落ちたら**: `--backend` を外して pipeline に戻す（既定）。
  ingest.py の既定が pipeline なのはこのためで、設定変更は不要。

## 6. math-extract → math-review の実地確認（パイロット）

§2–4 は GPU が動くかの確認。ここは **GPU を使う唯一の実利用者である
`math-extract` が、成果物の下流（Lean 形式化と `/math-review`）まで実際に
噛み合うか**の確認で、再ビルド後に一度だけ通せばよい。

背景: `docs/math/` のノートは現在 **0 件**で、フォーマットは一度も実運用されて
いない。ノートを読む側（`math-review`、AGENTS.md *Think before coding*）の配線は
入れたが、本番ノートに対しては未検証。題材に split inclusion を選ぶのは、
`note-format.md` の雛形がこの対象で書かれており、対応する Lean
（`QuantumSystem/Algebra/VonNeumannAlgebra/SplitInclusion.lean`,
`QuantumSystem/Algebra/LocalNet/SplitProperty.lean`）が既にあるため。
主要文献 Doplicher–Longo (Invent. Math. 75, 1984) と Buchholz (CMP 36, 1974) は
arXiv にないので **PDF → MinerU 経路（§4 の rung 4）を通る**。GPU がここで効く。

### 6-1. 抽出

```bash
/math-extract split inclusion of von Neumann algebras
```

PDF が 4 本以上ならスキルは見積りを出して止まる（想定どおり）。少数なら続行。

**成果物として確認すること**（`docs/math/split-inclusion.md`）:

| 見るもの | 合格条件 |
|---|---|
| step 6 の 4 検査 | Firewall / Quote / Locator / Discipline が全通過、スキルの報告に件数が出る |
| `### Adopted general form` | **判別子の引用だけで終わっていないこと。** 環境対象・標準仮定・量化子の順序・依拠する `(A#)` を含む完結した言明が書かれているか。ここが「(D1), because (X3)…」だけなら仕様（`note-format.md`）どおりに書かれていない |
| `## Hypotheses` | `model-dependent` の各行に **名前のある witness**。無ければ `open` に落ちているか |
| `## Degeneracies` | チェックリスト全項目に行がある（効果なしの行も含む）。特に `SplitProperty.lean` の module doc が既に述べている「退化表現では自明に成り立つ」「格子領域では空領域が全てに直交する」に対応する行があるか |
| `## Not investigated` | 非空 |
| frontmatter | `implemented-as: none`（この時点では Lean を指さない）、`worst-tier` が load-bearing 行の**最小**値 |

**既存 module doc との突き合わせ**が本命の検証。`SplitInclusion.lean` /
`SplitProperty.lean` の module doc は既に文献・採用理由・model-dependent 性・
退化ケースを抱えている（ただし locator なし）。ノートがそれを **再現できるか、
locator を付けられるか、食い違うか** を見る。食い違ったらどちらが正しいかを
判断すること — ノートが勝つとは限らない。

### 6-2. レビュー

```bash
/math-review QuantumSystem/Algebra/VonNeumannAlgebra/SplitInclusion.lean
```

**配線が効いていることの確認点**:

1. レポート冒頭に `**Extraction notes**:` 行が出て、`docs/math/split-inclusion.md`
   を指している（`none matched` ならノートの解決に失敗している）。
2. perspective 3（Abstraction & literature conformance）と 5（vacuity）の
   findings または cleared 報告が、ノートの `(D#)` / `(X#)` / `## Degeneracies`
   の行を**行 id で引用**している。引用がなければ、ノートを渡しただけで読まれて
   いない。
3. ノートの tier (a)/(b) 行に依拠した主張が **(b) verified** として出ている
   （(c) 止まりなら tier 変換規則が効いていない）。
4. `docs/math/split-inclusion.md` の `implemented-as:` に宣言名が書き込まれ、
   `docs/math/README.md` の Index に行が入っている。宣言がノートの採用形と
   ずれている場合は **back-link は書かれず、perspective 3 の finding が出る**
   のが正しい挙動。
5. `## Not reviewed` に、ノートの `## Not investigated` が残した穴が引き継がれて
   いる。

### 6-3. 判定

- 6-1 の表と 6-2 の 5 点が全部通れば、成果物フォーマットは下流で使える状態。
- 6-2 の 1 が通らない → `math-review/SKILL.md` step 1 のノート解決。
- 6-2 の 2–3 が通らない → `.claude/agents/math-reviewer.md` のノート参照節と
  tier 変換表。
- 6-2 の 4 が通らない → `math-review/SKILL.md` step 4 の reconcile 段。
- 6-1 の `Adopted general form` が言明になっていない →
  `.claude/skills/math-extract/references/note-format.md` の同節。

パイロットで書かれるのは `docs/math/split-inclusion.md` と
`docs/math/README.md` の 1 行だけで、Lean には触れないので `lake build` は不要。

## 7. 失敗時の切り分け

| 症状 | 原因と対処 |
|---|---|
| 再ビルドでコンテナ自体が起動しない（`could not select device driver "" with capabilities: [[gpu]]`） | Docker Desktop → Settings → General で WSL 2 based engine を確認。Windows 側 NVIDIA ドライバが古い場合は更新。**応急処置**: `devcontainer.json` の `runArgs` 2 行を削って再ビルドすれば従来どおり CPU で動く |
| コンテナは起動するが `nvidia-smi` が無い / NVML エラー | Docker Desktop を再起動 → WSL を `wsl --shutdown` してから Docker Desktop を起動し直す。それでも駄目なら Windows 側ドライバを更新 |
| `torch.cuda.is_available()` が `False`（`nvidia-smi` は通る） | §3 の 2 段チェック。(1) `torch.version.cuda` が `None` なら CPU wheel、(2) 値があり `driver ... is too old (found version 12080)` の警告が出るなら wheel の CUDA 世代がホストドライバより新しい ── cu128 固定（現状の解）かホストドライバを 580 系へ。どちらでもないなら Docker Desktop の GPU support 設定と再起動 |
| mineru が `[Errno 13] Permission denied: '/home/vscode/.cache/huggingface/hub'` で落ちる | `hf-models` volume が root 所有のまま。`onCreateCommand` が 2 つのキャッシュを chown する（§1）が、volume を新規作成した直後に手で直すなら `sudo chown -R vscode:vscode /home/vscode/.cache/huggingface` |
| mineru がモデルダウンロードで止まる | ネットワーク。取得元は `devcontainer.json` の `containerEnv` で `huggingface` に固定してある。HuggingFace に届かない環境なら、固定を外さずそのコマンドだけ `MINERU_MODEL_SOURCE=modelscope mineru …` で上書きする |
| 変換が CPU 時と同じくらい遅い | 成功時の mineru ログは出ないので、§4 のメモリ確認で GPU を使っているかを見る。比較したいときは `MINERU_DEVICE_MODE=cpu` を付けた同じコマンドと並べる。§3 が `True` で、変換中に GPU メモリが上がらないなら issue 級なので報告を |

## 8. 確認が全部通ったら

§1–5 と §7 は以後も再ビルドのたびに使えるので消さなくてよい。§6 のパイロットは
一度通れば役目を終えるが、`math-extract` と `math-review` のノート受け渡しを
書き換えたときの回帰確認としてそのまま使える。

`math-extract` スキル側の GPU 関連の記述は
`.claude/skills/math-extract/references/ingestion.md` の Rung 4 にある。
