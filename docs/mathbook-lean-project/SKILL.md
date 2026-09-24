---
name: mathbook-lean-project
description: 数学書を Lean/Mathlib の演習として読み進めるための個人プロジェクトを新規に立ち上げる。本を1冊指定すると、lake プロジェクトの土台・CLAUDE.md・節ごとの演習ファイルを書く /exercises スキル（希望すれば日本語解説を書く /exposition も）を生成する。「節ごとに本の定義と定理を statement だけ Lean に写し、証明は読者が自分で埋める」やり方を、どの数学書にも再現する。新しい本を始めるとき、空のディレクトリで呼ぶ。
disable-model-invocation: true
---

数学書を1冊、Lean/Mathlib の演習として読み進めるプロジェクトを立ち上げる。目的は**読者自身が本の定義と定理を Lean で組み直すこと**で、節ごとの演習ファイルが主成果物。日本語の解説 HTML は希望したときだけ用意する。

`templates/` のひな形を本の情報で埋めて配置し、lake プロジェクトを用意する。設計原則（副読本・statement はテキストの主張と1対1・実例を並べない・テキストとの突き合わせ検証）はひな形に入っているので、各本にそのまま伝わる。

## 手順

### 1. 本の情報を集める

不足しているものだけ尋ねる。

| 記号 | 内容 | 例 |
|---|---|---|
| `{{BOOK_TITLE}}` | 書名 | Category Theory in Context |
| `{{BOOK_AUTHOR}}` | 著者 | Emily Riehl |
| `{{BOOK_ACCESS}}` | 本文の入手先を書いた1〜数行。節の内容を参照できること | 公式 PDF の URL、手元のファイルの場所 |
| `{{SCOPE}}` | 読む範囲 | 第2章〜第4章 / 全体 |
| `{{LIB}}` | Lean ライブラリ名（ルート名前空間、英字） | Riehl |
| `{{CHAPTER_DIR_EXAMPLE}}` | 章ディレクトリの例 | `Riehl/Ch2_Yoneda/` |
| `{{BASENAME_EXAMPLE}}` | 節ファイルのベース名の例 | `S2_3_UniversalProperty` |

あわせて、**日本語の解説 HTML も作るか**を確認する。既定は作らない。

本文が手元のファイル（PDF など）なら、プロジェクト直下にコピーして、`{{BOOK_ACCESS}}` はそのコピーを指す。公開 URL で配布されている本なら、コピーせず URL を指す。

### 2. lake プロジェクトの土台を作る

空のプロジェクトディレクトリで実行する。版は焼き込まず、その時点の Mathlib と対応する toolchain を取る。

```
lake init {{LIB}} math
lake exe cache get
lake build
```

`lake init … math` がルート `{{LIB}}.lean`・`lean-toolchain`・lakefile（`lakefile.lean` または `lakefile.toml`。Mathlib 依存）を作る。`lake exe cache get` で Mathlib のビルド済みキャッシュを取り、`lake build` が通ることを確認する。

### 3. 規約ファイルを配置する

`templates/` を、集めた情報で置換しながらコピーする。

| ひな形 | 配置先 |
|---|---|
| `CLAUDE.md` | `CLAUDE.md` |
| `README.md` | `README.md`（人が読む入口。収録範囲の表は対象範囲の節で埋め、まだ無い節は「まだない」と書く） |
| `exercises.SKILL.md` | `.claude/skills/exercises/SKILL.md` |
| `cross-section.md` | `.claude/skills/exercises/cross-section.md` |
| `decisions-README.md` | `docs/decisions/README.md` |
| `exposition.SKILL.md` | `.claude/skills/exposition/SKILL.md`（解説 HTML を作るときだけ） |

解説 HTML を作らないなら、`CLAUDE.md` の解説資料に触れた段落、`README.md` の「解説」の節・収録範囲の表の解説列・「スキル」の `/exposition` の行、`docs/decisions/README.md` の `/exposition` への言及を削る。

最初の節を書いたあと、`README.md` の「演習」の節に、その演習ファイルから実際の抜粋（見出し・主張文・`#check`・`theorem … := sorry` が入る程度）を貼る。

`{{...}}` が1つも残っていないことを確認する。

### 4. 報告する

作ったもの（lake プロジェクト・CLAUDE.md・README・スキル）と `lake build` が通ったことを報告し、次は最初の節を書くこと（`/exercises <節番号>`。解説も作るなら、その節では `/exposition <節番号>` が先）を伝える。

## 原則

ひな形が担うが、運用でも守る。

- **演習が目的**。どの本でも演習 `.lean` を作る。解説 HTML は任意
- **副読本**。成果物の出典はテキスト。解説と演習は兄弟で、片方が片方の出典ではない
- **statement はテキストの主張と1対1**。変えてよいのは Mathlib の語彙と universe だけ。証明の途中形や Mathlib 宣言の型に寄せて主張の形を変えない
- **規約は規則で書く**。過去の判断を実例として並べない（局所最適を生む）。規約を変えたら `docs/decisions/` に経緯を残す
