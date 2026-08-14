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

`onCreateCommand` が `lake exe cache get` と `uv tool install "mineru[pipeline,vlm]"`
を再実行する。mineru の wheel（torch 含む ~4GB）は `uv-cache` volume に、モデルは
`hf-models` volume にキャッシュされているので、2 回目以降の再ビルドは大幅に速い。

## 2. GPU がコンテナに見えているか

```bash
nvidia-smi
```

**期待**: GPU 名と `8192MiB` 前後のメモリ表を表示。
`command not found` や `Failed to initialize NVML` の場合は §6 へ。

## 3. torch が CUDA を認識しているか

torch は mineru の tool 環境に入っている（プロジェクト venv ではない）ので:

```bash
~/.local/share/uv/tools/mineru/bin/python -c "import torch; print(torch.cuda.is_available(), torch.cuda.get_device_name(0) if torch.cuda.is_available() else '-')"
```

**期待**: `True <GPU 名>`。
`False` の場合: `nvidia-smi` が通っているなら torch のビルド違いを疑う
（`...bin/python -c "import torch; print(torch.version.cuda)"` が `None` なら
CPU 版 wheel が入っている。`uv tool install --reinstall "mineru[pipeline,vlm]"` で
入れ直す。Linux の既定 wheel は CUDA 同梱なので通常はここに落ちない）。

## 4. 実 PDF の変換が GPU で速くなっているか

CPU での実測基準（このコンテナ、20 コア、5 ページの PDF）: **モデルロード後の
変換だけで数分**。GPU なら同じ PDF が **数十秒以内**に落ちるはず。

```bash
time uv run .claude/skills/math-extract/scripts/ingest.py <PDFのパスかURL> \
  --allow-mineru --cache-dir /tmp/gpu-check
```

**期待**:
- JSON に `"stage": "mineru-pipeline"`、`"ok": true`。
- mineru のログ（stderr）にデバイスとして `cuda` が現れる。
- 所要時間が CPU 時より明確に短い。

初回はモデルのダウンロード（~1.5GB）が走る。`hf-models` volume に入るので 2 回目
以降は走らない。事前に落としておきたい場合は `mineru-models-download`。

## 5.（任意）hybrid-engine を試す

精度 95%（pipeline は 86%）だが、**VRAM 8GB はこのバックエンドの最低ラインで、
しかも Windows デスクトップと共有**のため OOM しうる。試すなら:

```bash
uv run .claude/skills/math-extract/scripts/ingest.py <PDF> \
  --allow-mineru --backend hybrid-engine --effort high --cache-dir /tmp/gpu-check
```

- **成功したら**: 数式が濃い文献ではこちらを使う価値がある。VRAM に余裕を作るには
  実行前に Windows 側の GPU 消費（ブラウザのハードウェアアクセラレーション等）を
  減らす。
- **`CUDA out of memory` で落ちたら**: `--backend` を外して pipeline に戻す（既定）。
  ingest.py の既定が pipeline なのはこのためで、設定変更は不要。

## 6. 失敗時の切り分け

| 症状 | 原因と対処 |
|---|---|
| 再ビルドでコンテナ自体が起動しない（`could not select device driver "" with capabilities: [[gpu]]`） | Docker Desktop → Settings → General で WSL 2 based engine を確認。Windows 側 NVIDIA ドライバが古い場合は更新。**応急処置**: `devcontainer.json` の `runArgs` 2 行を削って再ビルドすれば従来どおり CPU で動く |
| コンテナは起動するが `nvidia-smi` が無い / NVML エラー | Docker Desktop を再起動 → WSL を `wsl --shutdown` してから Docker Desktop を起動し直す。それでも駄目なら Windows 側ドライバを更新 |
| `torch.cuda.is_available()` が `False`（`nvidia-smi` は通る） | §3 の CPU wheel チェック。torch が CUDA 版なら Docker Desktop の GPU support 設定と再起動 |
| mineru がモデルダウンロードで止まる | ネットワーク。`MINERU_MODEL_SOURCE=modelscope` を試す（既定 auto は HuggingFace 優先） |
| 変換が CPU 時と同じくらい遅い | mineru のログに `cpu` と出ていないか確認。§3 が `True` でこれが起きるなら issue 級なので報告を |

## 7. 確認が全部通ったら

このファイルの手順は以後も再ビルドのたびに使えるので消さなくてよい。
`math-extract` スキル側の GPU 関連の記述は
`.claude/skills/math-extract/references/ingestion.md` の Rung 4 にある。
