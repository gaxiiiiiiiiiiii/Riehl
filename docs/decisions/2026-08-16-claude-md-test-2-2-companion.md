# 2026-08-16 CLAUDE.md テスト: companion-first 規約(対象 2.2)

companion-first ワークフロー(companion を先に書き、演習ファイルを後に作る)を CLAUDE.md に導入した改訂の検証。`docs/claude-md-test-procedure.md` の手順に従い、CLAUDE.md だけを入力にしたサブエージェントに §2.2 の companion(HTML)と演習ファイルを作らせ、規定の書き落としを洗い出して改訂するループを回す。

## 手順の適合(今回の差分)

- worktree は `.claude/worktrees/companion-first-conventions`、ブランチ `worktree-companion-first-conventions`(master と同一コミット 4acdc87 から分岐)
- ビルドは本体 checkout の `.lake` を symlink して `lake env lean` で検証
- 生成対象が「companion + 演習ファイル」の対になったため、固定プロンプトを次で置き換える(3文の前置きは手順書どおり):

  > Category Theory in Context 2.2 の companion と演習ファイルを作ってください。ワークフローにあるユーザーとの合意ステップは、今回は方針案を自分で確定して進めてください。

  合意ステップのスキップ指示は headless で回すための適合。最終成果物のユーザー確認がその代わりになる
- 2.1 の実物(companion の手本)は本体 checkout に untracked でありブランチからは見えない。CLAUDE.md の文面だけで companion の品質が再現できるかを見るテストとして機能する

## 評価項目

手順書の5項目に、companion 向けを足す:

6. **Companion 規約の照合** — 5部構成、書かないこと(本文の代替・証明ヒント・例の要約)、形式(自己完結 HTML・ライト/ダーク・Unicode 数式・和訳主体・読了5分)
7. **意図の照合** — 規定の字面を満たしていても、「本を開く前に読む地図」として機能するか(物語が本文を指せているか、形式化のズレが項目ごとに記録されているか、読む順序が具体的か)

## イテレーション記録

### イテレーション1(生成物: 8dc418d)

- コンパイル: エラー0、警告 `sorry` のみ。全 `#check` が `@` 付きで実在解決(`lake env lean` で裏取り)
- companion の事実(番号・ページ・逸話・演習の言い換え)は PDF と一致
- 規定照合はほぼ全項目適合。生成側の報告も事実と一致した
- 割れた点(=規定の不足)5つを CLAUDE.md に還元:
  1. `Riehl.lean` への import 追加が無規定 → ファイル構成に1文追加
  2. `my` 定義の `sorry` 範囲(1.7 の data 先渡しは章ごとの決定でしかない)→「節ごとに決めて companion に記録」を一般規則化
  3. 部分対応しかない `#check`(命題2.2.3 の `MulActionHom.End.equivMulOpposite`)の扱いが二値規定の外 →「部分対応は #check + 範囲の差を注記」を追加
  4. companion の「形式化のズレ」に難易度の示唆(「F 方向は即座」)が混入 → 書かないことに「難易度の示唆」を追加
  5. Remark の扱いが無規定(1.7 の前例からの類推で正解していた)→「例と Remark は載せない、Mathlib 対応のコメント注記のみ可」を明文化
- 生成側が保留した「章ごとの決定事項への 2.2 の追記」は、ワークフロー手順2がユーザー合意を前提とするため、テストでは正しい保留と判断

## 決定

(イテレーション2 の後に記入)
