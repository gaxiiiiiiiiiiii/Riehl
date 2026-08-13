# CLAUDE.md 検証テストの手順

`CLAUDE.md` だけを入力にして演習ファイルを作らせ、規定に書き落としがないかを調べる手順。結果と決定は `docs/decisions/` に残す。

## 準備

- worktree は `~/workspace/Lean/Riehl-test`、ブランチ `test/claude-md-only`
- 対象節のファイルがブランチ上にあれば削除し、`Riehl.lean` の import も外してコミットする（残っていると写せてしまう）
- `.claude/settings.local.json` の `skillOverrides` で `mathlib-exercise-maker` を `off` にする
- `lake exe cache get` と `lake build` が通る状態にしておく

## 実行

プロンプトは毎回同じ文面にする。節番号だけ変える。

> Category Theory in Context 1.5 の演習ファイルを作ってください。master ブランチには同じファイルの別バージョンがありますが、参照しないでください。

サブエージェントで回す場合は、作業ディレクトリの指定と「`mathlib-exercise-maker` スキルは使わないでください」を先頭に足す。サブエージェントには `CLAUDE.md` の自動読み込みも `skillOverrides` も効かないため。この2文以外は足さない。

## 評価

1. **コンパイル** — `lean_diagnostic_messages` でエラーが 0、警告が `sorry` だけであること
2. **`#check` の中身** — info の診断を読み、各 `#check` が実在の宣言に解決しているかを確認する。存在しない名前は `Function.comp` などに黙って解決してエラーにならない事例があった
3. **規定の照合** — `CLAUDE.md` の「ファイル構成」と「演習の作り方」の各項目を一つずつ突き合わせる
4. **報告の裏取り** — 生成側の報告を鵜呑みにしない。「リンタが警告を出すので設定を変えた」という報告が事実と違った例がある。ビルド設定の差分は必ず自分で見る
5. **割れた点の記録** — 前回と判断が分かれた箇所を挙げる。それが規定の不足箇所そのもの

## 記録

- 生成物はブランチにコミットし、ハッシュを `docs/decisions/` の該当ファイルに残す
- 決定は `docs/decisions/` に理由つきで書き、`CLAUDE.md` には規定だけを短く写す
- 同じ節で回し続けるとその節に過適合する。判断が割れなくなったら次の節へ移る
