#!/usr/bin/env bash
# scripts/check_proofs.sh
# ローカルで Lean 証明をチェックするスクリプト
#
# 使い方:
#   ./scripts/check_proofs.sh
#
# 必要なもの:
#   - elan (Lean バージョンマネージャ)
#     インストール方法: curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
#   - (オプション) leanblueprint (宣言チェック用)
#     インストール方法: pip install leanblueprint

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_DIR"

echo "=== Lean 証明チェック ==="
echo "プロジェクトディレクトリ: $PROJECT_DIR"
echo ""

# elan の確認
LAKE=""
if command -v lake &>/dev/null; then
  LAKE="lake"
elif [ -f "$HOME/.elan/bin/lake" ]; then
  LAKE="$HOME/.elan/bin/lake"
else
  echo "エラー: lake が見つかりません。elan をインストールしてください。"
  echo "  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
  exit 1
fi

echo "lake: $LAKE"
echo ""

# Mathlib キャッシュの取得（失敗しても続行）
echo "--- Mathlib キャッシュの取得 ---"
$LAKE exe cache get 2>/dev/null || echo "(キャッシュ取得をスキップします)"
echo ""

# プロジェクトのビルド（証明チェック）
echo "--- lake build (証明チェック) ---"
$LAKE build
echo ""
echo "✓ ビルド成功！すべての型が正しく検査されました。"
echo ""

# leanblueprint による宣言チェック（オプション）
if command -v leanblueprint &>/dev/null; then
  echo "--- leanblueprint checkdecls (Blueprint 宣言チェック) ---"
  leanblueprint checkdecls && echo "✓ 宣言チェック成功！" || echo "! 宣言チェックで問題が見つかりました（blueprint/lean_decls を確認してください）"
else
  echo "(leanblueprint がインストールされていないため宣言チェックをスキップします)"
  echo "  インストール方法: pip install leanblueprint"
fi
