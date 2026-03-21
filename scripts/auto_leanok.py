#!/usr/bin/env python3
"""
lake build の出力から sorry を含む宣言を検出し、
sorry のない宣言に対応する \leanok を content.tex に自動挿入する。

使い方:
  lake build 2>&1 | python3 scripts/auto_leanok.py blueprint/src/content.tex
"""
import re
import sys


def get_sorry_decls(lines: list[str]) -> set[str]:
    """lake build の出力から sorry 警告のある宣言名を抽出する。"""
    sorry_decls: set[str] = set()
    # Lean の sorry 警告: "warning: declaration uses 'sorry'"
    # 直前行に宣言名が出るか、同一行に出る場合がある
    # 典型的な形式: "path/File.lean:line:col: warning: 'DeclName' uses sorry"
    # または: "warning: declaration 'DeclName' uses sorry"
    patterns = [
        re.compile(r"declaration '([^']+)' uses sorry"),
        re.compile(r"'([^']+)' uses sorry"),
    ]
    for line in lines:
        if "sorry" not in line.lower():
            continue
        for pat in patterns:
            m = pat.search(line)
            if m:
                sorry_decls.add(m.group(1))
    return sorry_decls


def insert_leanok(tex_content: str, sorry_decls: set[str]) -> str:
    """content.tex の各環境に対し、sorry のない宣言に \leanok を挿入する。

    戦略:
    - \lean{DeclName} を持つ環境 (theorem/lemma/def 等) を見つける
    - DeclName が sorry_decls に含まれなければ:
      - 環境の \end{...} 直前に \leanok を挿入
      - 直後の \begin{proof}...\end{proof} にも \leanok を挿入
    """
    lines = tex_content.split("\n")
    result: list[str] = []
    i = 0
    env_pattern = re.compile(
        r"\\begin\{(theorem|lemma|definition|proposition|corollary)\}"
    )
    end_env_pattern = re.compile(
        r"\\end\{(theorem|lemma|definition|proposition|corollary)\}"
    )
    lean_pattern = re.compile(r"\\lean\{([^}]+)\}")
    proof_begin = re.compile(r"\\begin\{proof\}")
    proof_end = re.compile(r"\\end\{proof\}")

    # まず既存の \leanok 行を全て除去
    lines = [l for l in lines if l.strip() != "\\leanok"]

    while i < len(lines):
        line = lines[i]

        # 環境の開始を検出
        if env_pattern.search(line):
            env_lines: list[str] = [line]
            i += 1

            # \lean{...} を探しながら環境の終わりまで読む
            lean_decl = None
            end_idx = None
            while i < len(lines):
                env_lines.append(lines[i])
                m = lean_pattern.search(lines[i])
                if m and lean_decl is None:
                    lean_decl = m.group(1)
                if end_env_pattern.search(lines[i]):
                    end_idx = len(env_lines) - 1
                    i += 1
                    break
                i += 1

            should_mark = lean_decl is not None and lean_decl not in sorry_decls

            # \leanok を \end{...} の直前に挿入（空行を挟まない）
            if should_mark and end_idx is not None:
                has_leanok = any("\\leanok" in l for l in env_lines)
                if not has_leanok:
                    # \end{...} 直前の空行を除去してから挿入
                    while end_idx > 0 and env_lines[end_idx - 1].strip() == "":
                        env_lines.pop(end_idx - 1)
                        end_idx -= 1
                    env_lines.insert(end_idx, "\\leanok")

            result.extend(env_lines)

            # 直後の proof 環境にも \leanok を挿入
            # 空行をスキップ
            blank_lines: list[str] = []
            while i < len(lines) and lines[i].strip() == "":
                blank_lines.append(lines[i])
                i += 1

            if i < len(lines) and proof_begin.search(lines[i]):
                result.extend(blank_lines)
                proof_lines: list[str] = [lines[i]]
                i += 1

                # \uses{...} の直後か \begin{proof} の直後に \leanok を入れる
                proof_end_idx = None
                while i < len(lines):
                    proof_lines.append(lines[i])
                    if proof_end.search(lines[i]):
                        proof_end_idx = len(proof_lines) - 1
                        i += 1
                        break
                    i += 1

                if should_mark and proof_end_idx is not None:
                    has_leanok = any("\\leanok" in l for l in proof_lines)
                    if not has_leanok:
                        # \uses{...} の直後に挿入、なければ \begin{proof} の直後
                        insert_at = 1  # default: after \begin{proof}
                        for j, pl in enumerate(proof_lines):
                            if "\\uses" in pl:
                                insert_at = j + 1
                                break
                        proof_lines.insert(insert_at, "\\leanok")

                result.extend(proof_lines)
            else:
                result.extend(blank_lines)
                # 次の行は proof でないので通常処理に戻す
                continue
        else:
            result.append(line)
            i += 1

    return "\n".join(result)


def main() -> None:
    if len(sys.argv) < 2:
        print(f"Usage: lake build 2>&1 | {sys.argv[0]} <content.tex>", file=sys.stderr)
        sys.exit(1)

    tex_path = sys.argv[1]
    build_output = sys.stdin.read().splitlines()
    sorry_decls = get_sorry_decls(build_output)

    if sorry_decls:
        print(f"sorry を含む宣言: {sorry_decls}", file=sys.stderr)
    else:
        print("sorry を含む宣言はありません。全宣言に \\leanok を付与します。", file=sys.stderr)

    with open(tex_path, "r", encoding="utf-8") as f:
        tex_content = f.read()

    new_content = insert_leanok(tex_content, sorry_decls)

    with open(tex_path, "w", encoding="utf-8") as f:
        f.write(new_content)

    print(f"{tex_path} を更新しました。", file=sys.stderr)


if __name__ == "__main__":
    main()
