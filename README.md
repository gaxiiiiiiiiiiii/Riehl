# Riehl

数学書を Lean 4 と Mathlib で証明を書きながら読むための副読本を、Claude Code のスキルで節ごとに作ったもの。1節につき、日本語の解説と Lean の演習ファイルが1つずつある。題材は Emily Riehl, [*Category Theory in Context*](https://emilyriehl.github.io/files/context.pdf)（Dover, 2016）。対象範囲は 1.5、1.7 と第2章〜第4章。

## 成果物

### 解説

節の内容を日本語でたどる `.html`。定義・主張・証明・例・図式・節末問題を本の順に収め、それだけ読んで節がわかるようにしてある。Lean の話は出てこない。可換図式は inline SVG で描いてあり、ライト／ダークのどちらでも読める。

### 演習

本の定義と定理を statement として並べた `.lean`。証明は `sorry` で、ここを自分で埋める。3.1 節の補題3.1.28 はこうなっている。

```lean
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.1.28
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
極限対象への平行な射の対は、極限錐の脚との合成が等しいとき、かつそのときに限り等しい。
双対に、余極限対象からの平行な射の対は、余極限錐の脚との合成が等しいとき、かつそのときに
限り等しい。

構成: 極限と余極限のそれぞれについて、同値として述べる。
-/

#check @CategoryTheory.Limits.IsLimit.hom_ext

theorem lemma_3_1_28_limit {F : J ⥤ C} {t : Cone F} (h : IsLimit t) {X : C}
    (f g : X ⟶ t.pt) : f = g ↔ ∀ j, f ≫ t.π.app j = g ≫ t.π.app j := sorry
```

見出しは本の番号。`#check` は同じ内容の Mathlib の定理を指していて、解いたあとに見比べられる。その節が導入する定義は `my` で始まる名前で書き写してあり、定義の中に証明項があればそこも `sorry` になっている。定理は原則として Mathlib の定義のほうで述べてあるので、証明には Mathlib の補題がそのまま使える。本と Mathlib で定義が食い違う箇所や、本の問題のうち入れなかったものは、各ファイル冒頭のコメントにまとめてある。

### 収録範囲

| 節 | 題 | 解説 | 演習 |
|---|---|---|---|
| 1.5 | Equivalence of categories | — | [lean](Riehl/Ch1_Categories/S1_5_Equivalence.lean) |
| 1.7 | The 2-category of categories | — | [lean](Riehl/Ch1_Categories/S1_7_TwoCategory.lean) |
| 2.1 | Representable functors | [html](Riehl/Ch2_Yoneda/S2_1_Representable.html) | [lean](Riehl/Ch2_Yoneda/S2_1_Representable.lean) |
| 2.2 | The Yoneda lemma | [html](Riehl/Ch2_Yoneda/S2_2_Yoneda.html) | [lean](Riehl/Ch2_Yoneda/S2_2_Yoneda.lean) |
| 2.3 | Universal properties and universal elements | [html](Riehl/Ch2_Yoneda/S2_3_UniversalProperty.html) | [lean](Riehl/Ch2_Yoneda/S2_3_UniversalProperty.lean) |
| 2.4 | The category of elements | [html](Riehl/Ch2_Yoneda/S2_4_CategoryOfElements.html) | [lean](Riehl/Ch2_Yoneda/S2_4_CategoryOfElements.lean) |
| 3.1 | Limits and colimits as universal cones | [html](Riehl/Ch3_Limits/S3_1_UniversalCones.html) | [lean](Riehl/Ch3_Limits/S3_1_UniversalCones.lean) |

3.2 以降と第4章（随伴）はまだない。1.5 と 1.7 は演習ファイルだけで、解説はない。解説は GitHub 上ではソースが表示されるので、clone してブラウザで開く。

1.7 は本来の対象範囲外だが、whiskering が第3章の錐と第4章の三角等式で必要になるため入れている。

## スキル

2つのスキルが節番号を引数に取り、本の PDF を読んでその節のファイルを書く。

- [`/exposition`](.claude/skills/exposition/SKILL.md) が解説を書く。
- [`/exercises`](.claude/skills/exercises/SKILL.md) が演習ファイルを書く。節をまたいで揃える書き方は [`cross-section.md`](.claude/skills/exercises/cross-section.md) にある。

1つの節は `/exposition 2.4`、`/exercises 2.4` の順に作る。本文を日本語で書き下せる状態にしてから、演習を設計するためである。

[`CLAUDE.md`](CLAUDE.md) は、本の所在、ファイルの置き方、そして Claude が証明を書かないことを定めている。演習を解くのは読む人で、Claude は statement を用意し、質問に答える。スキルの規約を見直したときの経緯は [`docs/decisions/`](docs/decisions/) に残す。

これらのスキルは [mathbook-lean-project](https://github.com/gaxiiiiiiiiiiii/mathbook-lean-project) が生成したもので、規約の正はそちらのテンプレートにある。

## 使い方

本の PDF はリポジトリに含めていない。著者が[公式に無料配布](https://emilyriehl.github.io/files/context.pdf)している。

初回は、ビルド済みの Mathlib を取得してからビルドする。

```sh
lake exe cache get
lake build
```

`lake build` が出す `sorry` の警告の数が、残っている演習の数になる。Lean と Mathlib の版は `lean-toolchain` と `lakefile.toml` で固定してある。

本と解説でその節を読み、演習ファイルの `sorry` を上から埋めていく。
