# Wilson の定理 Blueprint プロジェクト

このリポジトリは Lean4 の **blueprint 機能** を使って [Wilson の定理](https://en.wikipedia.org/wiki/Wilson%27s_theorem) の証明をトップダウン方式で構築するためのコードベースです。

## Wilson の定理

$$p \text{ が素数} \iff (p-1)! \equiv -1 \pmod{p}$$

## プロジェクト構成

```
lean-tutorial/
├── .github/workflows/
│   ├── ci.yml                 # CI: Lean 証明チェック
│   └── deploy-blueprint.yml  # CD: Blueprint ページ生成・デプロイ
├── blueprint/
│   ├── lean_decls             # Blueprint に登場する Lean 宣言の一覧
│   └── src/
│       ├── content.tex        # Wilson の定理の Blueprint 本文
│       ├── web.tex            # Web 版エントリーポイント
│       ├── print.tex          # PDF 版エントリーポイント
│       ├── plastex.cfg        # plasTeX 設定
│       └── macros/            # LaTeX マクロ
├── LeanTutorial/
│   └── Wilson.lean            # Wilson の定理（Lean コード）
├── LeanTutorial.lean          # メインエントリーポイント
├── lakefile.toml              # Lake ビルド設定
├── lean-toolchain             # Lean バージョン指定
└── scripts/
    └── check_proofs.sh        # ローカル証明チェックスクリプト
```

## セットアップ

### 前提条件

- [elan](https://github.com/leanprover/elan) (Lean バージョンマネージャ)
- Python 3.9 以上（Blueprint ビルド用）

### Lean のインストール

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

### 依存関係の取得

```bash
lake update
lake exe cache get
```

## 使い方

### 証明のチェック（ローカル）

```bash
./scripts/check_proofs.sh
```

または直接:

```bash
lake build
```

### Blueprint のローカルビルド

Python 環境の準備:

```bash
# graphviz 開発ライブラリのインストール（Ubuntu/Debian）
sudo apt-get install -y graphviz libgraphviz-dev

# leanblueprint のインストール
pip install leanblueprint
```

Blueprint のビルドと表示:

```bash
# PDF 版のビルド
leanblueprint pdf

# Web 版のビルド
leanblueprint web

# ローカルサーバーで表示
leanblueprint serve
```

## CI/CD

### CI (`.github/workflows/ci.yml`)

`push` または `pull_request` をトリガーに自動実行されます:

- `lake build` によって Lean プロジェクトをビルドし、型チェックを行います。
- `sorry` は警告として扱われますが、型が正しい限りビルドは成功します。

### CD (`.github/workflows/deploy-blueprint.yml`)

`main` ブランチへの `push` をトリガーに自動実行されます:

1. Lean プロジェクトのビルド
2. Blueprint PDF と Web ページの生成（leanblueprint 使用）
3. Blueprint 宣言の確認（`lean_decls` に記載された宣言が実際に存在するか検証）
4. GitHub Pages へのデプロイ

> **GitHub Pages の設定**: リポジトリの Settings → Pages → Source で `GitHub Actions` を選択してください。

## トップダウン開発の進め方

1. `blueprint/src/content.tex` で証明の構造（定理・補題の依存関係）を記述する
2. `LeanTutorial/Wilson.lean` に対応する Lean 宣言を `sorry` 付きで追加する
3. CI が型チェックを行い、構造が正しいことを確認する
4. Blueprint ページで現在の進捗（未証明・証明済み）を確認する
5. 各 `sorry` を実際の証明で埋めていく

## ライセンス

Apache 2.0