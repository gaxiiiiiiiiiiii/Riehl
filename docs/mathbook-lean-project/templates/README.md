# {{LIB}}

数学書を Lean 4 と Mathlib で証明を書きながら読むための副読本を、Claude Code のスキルで節ごとに作ったもの。1節につき、日本語の解説と Lean の演習ファイルが1つずつある。題材は {{BOOK_AUTHOR}}, *{{BOOK_TITLE}}*。対象範囲は {{SCOPE}}。

## 成果物

### 解説

節の内容を日本語でたどる `.html`。定義・主張・証明・例・図式・節末問題を本の順に収め、それだけ読んで節がわかるようにしてある。Lean の話は出てこない。可換図式は inline SVG で描いてあり、ライト／ダークのどちらでも読める。

### 演習

本の定義と定理を statement として並べた `.lean`。証明は `sorry` で、ここを自分で埋める。

見出しは本の番号。`#check` は同じ内容の Mathlib の定理を指していて、解いたあとに見比べられる。その節が導入する定義は `my` で始まる名前で書き写してあり、定義の中に証明項があればそこも `sorry` になっている。定理は原則として Mathlib の定義のほうで述べてあるので、証明には Mathlib の補題がそのまま使える。本と Mathlib で定義が食い違う箇所や、本の問題のうち入れなかったものは、各ファイル冒頭のコメントにまとめてある。

### 収録範囲

| 節 | 題 | 解説 | 演習 |
|---|---|---|---|
| （節番号） | （節の題） | [html]({{CHAPTER_DIR_EXAMPLE}}{{BASENAME_EXAMPLE}}.html) | [lean]({{CHAPTER_DIR_EXAMPLE}}{{BASENAME_EXAMPLE}}.lean) |

解説は GitHub 上ではソースが表示されるので、clone してブラウザで開く。

## スキル

2つのスキルが節番号を引数に取り、本を読んでその節のファイルを書く。

- [`/exposition`](.claude/skills/exposition/SKILL.md) が解説を書く。
- [`/exercises`](.claude/skills/exercises/SKILL.md) が演習ファイルを書く。節をまたいで揃える書き方は [`cross-section.md`](.claude/skills/exercises/cross-section.md) にある。

1つの節は `/exposition <節番号>`、`/exercises <節番号>` の順に作る。本文を日本語で書き下せる状態にしてから、演習を設計するためである。

[`CLAUDE.md`](CLAUDE.md) は、本の所在、ファイルの置き方、そして Claude が証明を書かないことを定めている。演習を解くのは読む人で、Claude は statement を用意し、質問に答える。スキルの規約を見直したときの経緯は [`docs/decisions/`](docs/decisions/) に残す。

これらのスキルは [mathbook-lean-project](https://github.com/gaxiiiiiiiiiiii/mathbook-lean-project) が生成したもので、規約の正はそちらのテンプレートにある。

## 使い方

{{BOOK_ACCESS}}

初回は、ビルド済みの Mathlib を取得してからビルドする。

```sh
lake exe cache get
lake build
```

`lake build` が出す `sorry` の警告の数が、残っている演習の数になる。Lean と Mathlib の版は `lean-toolchain` と `lake-manifest.json` で固定してある。

本と解説でその節を読み、演習ファイルの `sorry` を上から埋めていく。
