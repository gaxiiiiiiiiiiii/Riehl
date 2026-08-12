# CLAUDE.md

## プロジェクトの目的

Emily Riehl, *Category Theory in Context* を読むための個人的な Lean プロジェクトです。ユーザー自身が Lean で定義と定理を再現しながら読み進めることが目的で、対象範囲は 1.5、1.7 と第2章〜第4章です。

エージェントの主な役割は、演習ファイルを用意すること、および Mathlib・Lean・数学概念についての質問に答えることです。ユーザーの学習過程を置き換えるために、証明を先回りして完成させないでください。

## 本文へのアクセス

本書は著者が公式に無料 PDF を配布しています。

- https://emilyriehl.github.io/files/context.pdf

エージェントはこの PDF を参照して、節ごとの定義・命題・節末問題を拾い、演習に落として構いません。参照した箇所は節番号・命題番号で示してください。

## ファイル構成

1節につき1ファイルとし、章ごとにディレクトリを分けます。

```
Riehl/Ch1_Categories/     -- 1.5, 1.7
Riehl/Ch2_Yoneda/         -- 2.1-2.4
Riehl/Ch3_Limits/         -- 3.1-3.8
Riehl/Ch4_Adjunctions/    -- 4.1-4.7
```

各ファイルの構成は次の3部です。

1. **ヘッダ** — その節が何を扱い、どの後続節の前提になるか。参照した Mathlib のファイル名を並べる
2. **Recap** — 演習の足場になる Mathlib 定義の写し。`namespace Recap` に隔離し、実際に演習で使うのは Mathlib のもの
3. **本体** — 本の定義・命題・節末問題を出現順に並べる。statement のみを置き、証明は `sorry`

演習が多い節（3.1、4.6 など）は Part に分割してください。

## 演習の作り方

- 演習が再現・再証明する対象の Mathlib 版は `#check` で示す。Recap には写さない
- 演習を解くのに必要だが、再現の対象ではない定義は Recap に写す
- すべての演習に、対応する Mathlib の定理・定義の `#check` を添える。対応物がない場合は `#check` の代わりに「Mathlib に対応物なし」と明記する
- 節末問題は原則すべて載せる。形式化が不自然なものは問題文をコメントで残し、言い換えれば述べられるものは言い換えたうえでズレを注記する
- 教科書の定義を自前で組み直すものは `my` で始まる名前に置く
- Hint、証明方針、道具の `#check` は書かない（証明は自力）
- コメントは1宣言あたり1〜2行。定義の動機や statement の意味に限り、証明の方向づけは書かない

## 章ごとの決定事項

- **1.5** — 本の定義（F, G, η, ε のみ、三角等式なし）を `MyEquivalence` として自前で定義する。Mathlib の `CategoryTheory.Equivalence` は三角等式込みなので、その差をコメントで明記する。定理1.5.9 は両向きを演習にする
- **1.7** — 本来の対象範囲外だが、whiskering（注意1.7.6）が 3.1 の錐の押し出しと 4.1-4.3 の三角等式で必要になるため入れる。縦合成・水平合成・whiskering は `my` で始まる名前で自前に組み直す。この節の `my` 定義は data 部分を書いて proof obligation（`naturality` など）だけを `sorry` にする。補題1.7.1・1.7.4 の数学的内容が自然性の証明そのものだから。定義1.7.8 の 2-圏は結合律・単位律を等式で課す strict なもので、Mathlib の `Bicategory` は同型で持つ弱い版。対応は `Bicategory` + `Bicategory.Strict` と注記する。演習1.7.v は 1.5 の `MyEquivalence.trans` と同じ主張だが、本文が「Prove (again)」と書き脚注43 が両者を結んでいるので両方載せる。1.7 側は `MyEquivalence` に依存させず、F, G, η, ε を仮定に展開した自己完結形にする
- **4.3** — 上の三角等式の差はここで回収する。命題4.3.5 の演習は `CategoryTheory.Equivalence.adjointifyη` の再現
- **3.7** — 補題3.7.1 は通常の演習にする。small / large / locally small の語彙は Mathlib では universe と `Small` 系のクラスに化けるので、`Mathlib.CategoryTheory.EssentiallySmall` の `LocallySmall`・`EssentiallySmall`・`ShrinkHoms` を Recap で対応づける（`LocallySmall` は注意1.7.3 のために 1.7 の Recap にも写してある）。命題3.7.3（Freyd）は Mathlib に対応物がなく証明も重いので、statement だけを注記つきで置く

## 証明コードを書かない原則

ユーザーが明示的に依頼しない限り、Lean の証明コードを書かないでください。

許可される通常対応:

- 数学的な概念を自然言語で説明する
- 証明方針を自然言語で説明する
- 関連しそうな Mathlib の定義、定理、lemma 名を挙げる
- 形式化の方針や、どの概念を Mathlib で探すべきかを説明する

避ける通常対応:

- `by ...` 以降の証明コードを完成させる
- `sorry` を埋める
- 途中まで書かれた証明ブロックを勝手に修正する
- ユーザーが頼んでいない `theorem` や `lemma` を追加して形式化を進める

明示的に依頼された場合は、その `theorem`、`lemma`、証明ブロックに限定して編集してください。許可なく宣言文やドキュメント文字列を変更しないでください。

## 検証

演習ファイルを作成・編集したら `lean_diagnostic_messages` で確認します。`sorry` の警告は想定内ですが、すべての `#check` が解決し、すべての statement が elaborate することを確認してください。証明が `sorry` のまま残っている状態を「完成」と報告しないでください。

## 環境

- toolchain `leanprover/lean4:v4.34.0-rc1`、Mathlib も同 rev
- 別プロジェクト `~/workspace/Lean/Closure` は Mathlib v4.29.1 で、定義名が動いている場合があります。そちらで確認した名前をここで使う前に再確認してください

## 説明の言語

説明は日本語で行い、`Lean`、`Mathlib`、`lake build`、定義名、定理名、tactic 名などは英語のまま使ってください。
