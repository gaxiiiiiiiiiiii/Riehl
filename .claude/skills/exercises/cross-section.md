# 節をまたぐ取り決め

演習ファイルを書く前に読む。

入れてよいのは、**どの成果物1つにも属さないもの**だけ。節をまたぐ取り決めか、まだ存在しないファイルへの先約。

- **`MyEquivalence` のフィールド名** — `functor`・`inverse`・`unitIso`・`counitIso`。1.5 と 1.7 で揃える
- **演習1.7.v と `MyEquivalence.trans`** — 同じ主張だが、本文が「Prove (again)」と書き脚注43 が両者を結んでいるので両方に載せる。1.7 側は `MyEquivalence` に依存させず、F, G, η, ε を仮定に展開した自己完結形にする
- **三角等式の差** — 1.5 は本の定義に従って三角等式を課さない `MyEquivalence` を自前で置いている。この差は 4.3 で回収する（命題4.3.5 の演習は `CategoryTheory.Equivalence.adjointifyη` の再現）
- **添字圏の universe** — 3.1 以降、図式の添字圏は `{J : Type v} [SmallCategory J]`、値の圏は `{C : Type u} [Category.{v} C]` に取る。J の対象と C の hom を同じ `v` に置くことで、錐の集合 Cone(c, F) が `Type v` に落ち、Cone(−, F) を `ULift` なしで `Cᵒᵖ ⥤ Type v` と書ける。本の「J は小圏、C は局所小」にあたる。特別な形の添字圏（`Discrete β`・`WalkingParallelPair`・`WalkingCospan`）は `β : Type v` または `Type 0` で、この取り決めの範囲内
- **随伴の変数名** — 第4章の演習ファイルでは、`Adjunction.CoreHomEquiv F G` と `F ⊣ G` の変数・フィールドを `σ` と書き、同じ宣言に 2 つあるときは `σ`・`τ` と書く。Mathlib の `adj` は使わない
