# 2026-10-18 節をまたぐ話題の演習ファイル `Riehl/Topics/` を設け、埋め込みと部分圏の同一視を置いた

## 経緯

3.4 の命題3.4.9 で本が `ob A ↪ A` と書く包含を `obIncl : Discrete A ⥤ A` として置いていたが、`↪` が主張している「埋め込みである」を述べていなかった。埋め込み(対象に単射な忠実関手)は本が 1.5 で定義し「域を余域の部分圏と同一視する」と述べている語だが、1.5 の演習ファイルにも Mathlib にも対応する宣言がない。同一視の根拠は、埋め込みの像が部分圏をなし、域がその像と圏として同型になることで、部分圏の定義(1.1)から確かめる必要がある。

## 判断

1.5 に足すと節の内容に紛れるので、節に対応しない専用のファイルにした。1 節 1 ファイルの取り決めの外になるため、CLAUDE.md に「節をまたぐ話題の演習ファイルは `Riehl/Topics/<内容>.lean`」の 1 行を加えた。形式は節の演習ファイルと同じ。解説資料は本文の節に対応しないので作らない。

部分圏は、Mathlib では対象を絞る `ObjectProperty.FullSubcategory` と射を絞る `WideSubcategory` の 2 段で表され、一つの型がない。1.1 は対象範囲外の節なので規則上は Mathlib を使う側だが、このファイルの目的が「部分圏との同一視」の意味を確かめることなので、本の定義どおりの `Subcategory` を自前で置き、Mathlib の 2 段との往復と圏の同型 `Cat.of S ≅ Cat.of (WideSubcategory Q)` を演習にした。以後の宣言(埋め込みの像など)は自前の `Subcategory` を参照する。Mathlib 側は 2 つの型の合成で名前がなく、以後の宣言が書きにくいため。5.2 の「一致を示したら以後は Mathlib を参照する」の例外になる。

圏の同型は `Cat` の `Iso` で書く。本は 1.3 で逆関手の対として定義しているが対象範囲外で、`Cat.of S ≅ Cat.of T` がその Mathlib 表現。圏同値 `≌` と紛れるので `#check Cat.equivOfIso` を添えた。

## 内容

`Riehl/Topics/Embedding.lean`:

1. 部分圏(1.1)— `Subcategory`、`IsFull`、圏の instance、包含 `ι` とその忠実性・対象の単射性
2. Mathlib の部分圏との対応 — `objectProperty`、`morphismProperty`、`IsMultiplicative`、`ofMathlib`、`isoMathlib`、`isoFullSubcategory`
3. 演習1.3.iii — statement を置かない(例を見つける型)
4. 埋め込み(1.5)— `Embedding`、`FullEmbedding`、射の大域的単射性
5. 埋め込みの像 — `Embedding.image : Subcategory A`
6. 部分圏との同一視 — `toImage`、`isoImage : Cat.of S ≅ Cat.of (image F)`
7. 充満埋め込みの像は充満部分圏

3.4 では `obIncl` の直後に `discreteFunctorId_embedding : Embedding (Discrete.functor id)` を置いた。
