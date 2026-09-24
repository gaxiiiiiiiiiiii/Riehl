# mathbook-lean-project

数学書を1冊、Lean 4 と Mathlib の演習として読み進めるプロジェクトを立ち上げる [Claude Code](https://code.claude.com) のスキル。

本を指定すると、次を生成する。

- Mathlib 依存の lake プロジェクトの土台
- `CLAUDE.md`（エージェント向けの方針）と `README.md`（人が読む入口）
- `/exercises` — 節ごとに、本の定義と定理を statement だけ Lean に写した演習ファイルを書くスキル。証明は `sorry` のまま読者に残す
- `/exposition`（希望したときだけ）— 節ごとに、日本語の自己完結した解説 HTML を書くスキル

「本の定義と定理を自分の手で Lean に組み直す」ことが目的で、演習ファイルが主成果物。生成される演習ファイルの規約は `templates/exercises.SKILL.md` にある。要点は、定義は `my` で始まる名前で書き写して中の証明項を `sorry` にする、statement は本の主張と1対1で形を変えない、Mathlib の対応物を `#check` で添える、の3つ。

A Claude Code skill that scaffolds a project for reading a mathematics textbook as Lean 4 / Mathlib exercises: per section, the book's definitions and theorems are transcribed as Lean statements with proofs left as `sorry`. Generated prose (skills, headers, optional expository HTML) is in Japanese.

## 前提

- Claude Code
- Lean 4 と lake（[elan](https://github.com/leanprover/elan) 経由）。生成時に `lake init … math` と `lake exe cache get` を実行するので、Mathlib のキャッシュを取れるネットワークが要る
- 本文（PDF の URL か手元のファイル）。エージェントが節の内容を参照できること
- 任意: [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp)。あれば演習ファイルの検証に使う。なければ `lake build` で代用する

## インストール

```sh
git clone https://github.com/gaxiiiiiiiiiiii/mathbook-lean-project ~/.claude/skills/mathbook-lean-project
```

更新は `git pull`。

## 使い方

新しい本のための空ディレクトリを作って、そこで Claude Code を開き、

```
/mathbook-lean-project
```

書名・著者・本文の所在・読む範囲・Lean ライブラリ名・章と節のファイル名の付け方を聞かれるので答える。日本語の解説 HTML も作るかは既定で「作らない」。

生成が終わったら、最初の節を `/exercises <節番号>` で書く。解説も作るなら、その節では `/exposition <節番号>` を先に。

## 構成

```
SKILL.md                      初期化の手順
templates/
  CLAUDE.md                   生成するプロジェクトの CLAUDE.md
  README.md                   同 README
  exercises.SKILL.md          /exercises の規約
  exposition.SKILL.md         /exposition の規約（任意）
  cross-section.md            節をまたぐ取り決めの置き場（空で生成）
  decisions-README.md         規約変更の経緯を残す場所の説明
```

テンプレート内の `{{...}}` は、生成時に本の情報で置換される。

## 制約

- 生成される文書はすべて日本語。証明支援系は Lean 4 / Mathlib に固定
- スキルは `disable-model-invocation: true` で、ユーザーが明示的に呼んだときだけ動く
- 規約は「規則」として書いてあり、過去の判断の実例は含めていない（局所最適を避けるため）。本ごとの判断は、生成されたプロジェクトの各ファイルのヘッダに記録される

## License

MIT
