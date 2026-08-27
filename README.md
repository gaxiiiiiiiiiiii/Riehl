# Riehl

Emily Riehl, *Category Theory in Context* を Lean 4 と Mathlib で読むための個人プロジェクトです。本を読みながら、そこに現れる定義と定理を自分で Lean に書き直し、証明を埋めていきます。対象範囲は 1.5、1.7 と第2章から第4章です。

## 本について

- Emily Riehl, *Category Theory in Context*, Dover Publications, 2016
- 著者が公式に無料 PDF を配布しています: https://emilyriehl.github.io/files/context.pdf

本文はこのリポジトリに含みません。節番号・命題番号での参照だけを書いています。

## ファイルの読み方

1節につき1ファイルで、各ファイルは3部構成です。

**ヘッダ** — その節が何を扱い、どの後続節の前提になるかを書いています。あわせて、参照した Mathlib のファイルを並べています。

**Recap** — 演習を解くのに必要な Mathlib の定義を写したものです。`namespace Recap` に隔離してあるので、演習で実際に使うのは Mathlib 側の定義です。定義の本体を見ないと問題が解けないものだけを写しています。

**本体** — 本の定義・命題・節末問題を、本に現れる順に並べています。置いてあるのは statement だけで、証明は `sorry` のままです。この `sorry` を埋めることがこのプロジェクトの中身です。

読むうえでの約束事は次のとおりです。

- 各演習の直上の `#check` は、その演習に対応する Mathlib の宣言です。「Mathlib に対応物なし」と書いてある演習は、Mathlib に相当するものが見つからなかったものです
- `my` で始まる名前は、教科書の定義を Mathlib のものとは別に自前で組み直したものです。本と Mathlib で定義の形が食い違う場合に置いています
- 節末問題は原則すべて載せています。Lean で述べるのが不自然なものは、statement を置かずに問題文だけをコメントで残しています
- 証明の方針やヒントは書きません。`#check` で原文にあたる宣言を示すところまでが、ファイルの役割です

## ディレクトリ構成

```
Riehl/
├── Ch1_Categories/     -- 1.5 圏同値, 1.7 圏の2-圏
│   ├── S1_5_Equivalence.{html,lean}
│   └── S1_7_TwoCategory.{html,lean}
├── Ch2_Yoneda/         -- 2.1-2.4 普遍性・表現可能性・米田の補題
│   ├── S2_1_Representable.{html,lean}
│   ├── S2_2_Yoneda.{html,lean}
│   └── S2_3_UniversalProperty.{html,lean}
├── Ch3_Limits/         -- 3.1-3.8 極限と余極限
└── Ch4_Adjunctions/    -- 4.1-4.7 随伴
```

1.7 は本来の対象範囲外ですが、whiskering が第3章の錐の押し出しと第4章の三角等式で必要になるため入れています。

## 環境

- toolchain: `leanprover/lean4:v4.34.0-rc1`
- Mathlib: 同 rev

## 使い方

初回はビルド済みの Mathlib を取得します。

```sh
lake exe cache get
lake build
```

`lake build` は `sorry` の警告を大量に出しますが、それが未解決の演習です。エラーが出ないことだけを確認します。
