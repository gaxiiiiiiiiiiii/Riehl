# 未着手の証明フィールドは、省略せず `sorry` と明示する

大きな structure（`Equivalence`・`NatIso`・`Functor` など）を書き進めるとき、まだ証明して
いないフィールドはフィールドごと省略するのではなく `:= sorry` と書く。省略すると
elaboration が桁違いに遅くなることがある。本プロジェクトで実測した例では、フィールド1つの
省略が宣言の elaboration を**約95秒**にし、`sorry` の明示で**約3秒**に戻った。

検証環境: Lean `v4.34.0-rc1`、Mathlib `de5ce8a`（2026-08-27 計測）。

## 機構: フィールドの省略は「空欄」ではなく「今すぐ自動証明せよ」

Mathlib の証明系フィールドの多くは、デフォルトとして**タクティク**が登録されている。
たとえば `NatTrans`（`Mathlib/CategoryTheory/NatTrans.lean`）:

```lean
structure NatTrans (F G : C ⥤ D) : Type max u₁ v₂ where
  app (X : C) : F.obj X ⟶ G.obj X
  naturality ⦃X Y : C⦄ (f : X ⟶ Y) : F.map f ≫ app Y = app X ≫ G.map f := by cat_disch
```

末尾の `:= by cat_disch` が **autoParam**（automatic parameter）。デフォルトが値である
optParam（`x : Nat := 0`）に対し、autoParam はデフォルトがタクティクの実行になっている。
Lean Language Reference はこう明言する（§13.4 Function Application）:

> If the parameter is an automatic parameter then its associated tactic script is
> executed to construct the argument.
>
> （和訳: パラメータが automatic parameter である場合、関連付けられたタクティク
> スクリプトが実行されて、その引数が構成される）

つまり、structure インスタンスで autoParam フィールドを省略すると、その `def` の
elaboration 中にタクティクが走る。3通りの書き方はそれぞれ別のことをする:

| 書き方 | elaboration 時に起きること | コスト |
|---|---|---|
| `naturality := 証明` | 書いた項を検査するだけ | 証明の分だけ |
| 省略 | `cat_disch`（aesop）がその場で走る | 閉じれば一瞬、**閉じないと探索し尽くすまで** |
| `naturality := sorry` | `sorry` は任意の型を持つ定数。何も走らない | ほぼゼロ |

`cat_disch` は aesop ベースの探索器で、simp による正規化・ルール適用・バックトラックを
繰り返し、失敗の確定には探索空間を使い果たす必要がある。**成功は速いが、失敗が一番高くつく**。
書きかけの構造はまさに失敗コースに入りやすい:

- 他のフィールドが未完成なので、ゴールがそもそも証明不能な形をしている
- ゴールに `functor ⋙ inverse` のような合成が現れると、書いた定義全体がインライン展開
  された巨大な項になり、aesop の正規化 simp がそこで延々こねる

さらに掛け算が効く。宣言の中を1文字でも編集すると**宣言全体が再 elaborate される**ので、
失敗する autoParam は編集のたびにフルコストを払い直す。「どの行を触っても一様に重い」と
いう症状はこれで、最後に編集した行が重いように見えるのは錯覚になる。

## 実測

補題2.4.7 の演習（`F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F` を `Equivalence` として
構成する途中経過）で計測した。`functor`・`inverse` を書き終え、`unitIso.hom` の `app` まで
書いた時点。`naturality` は省略していた。

**省略のまま**（`lake env lean` + `set_option trace.profiler true`）:

```
[Elab.command] [95.36] def lemma_2_4_7 ...
  [Elab.definition.value] [94.98] ❌ lemma_2_4_7
    [Elab.step] [94.49] 💥 cat_disch            ← naturality の autoParam
      ...
        [aesop] [94.48] ⊢ ∀ ⦃X Y⦄ (f : X ⟶ Y), ...   ← functor と inverse が丸ごと展開された巨大ゴール
          [aesop] [94.42] <norm simp>            ← ここで94秒
```

```
error: could not synthesize default value for field 'naturality' of
       'CategoryTheory.NatTrans' using tactics
error: Tactic `aesop` failed, failed to prove the goal after exhaustive search.
```

95秒のうち94.5秒が、省略した `naturality` に対する `cat_disch` の失敗。エラーメッセージの
「could not synthesize **default value** ... **using tactics**」が、省略→タクティク実行
という機構をそのまま語っている。

**未着手フィールドを `sorry` に**（`naturality := sorry`・`inv := sorry`・
`hom_inv_id := sorry`・`inv_hom_id := sorry`・`counitIso := sorry`・
`functor_unitIso_comp := sorry`）:

```
$ time lake env lean Riehl/Ch2_Yoneda/S2_4_CategoryOfElements.lean
3.235 total   （エラー0、ファイル全体）
```

なお、疑われがちな「タクティクの行そのもの」は無実だった。問題の宣言内にあった1ゴールを
単独の `example` に切り出して `#count_heartbeats` で測ると、どの閉じ方でも差がない
（既定の上限は 200000）:

| 閉じ方 | heartbeats |
|---|---|
| `rfl` | 59 |
| `exact types_id_apply _ _` | 54 |
| `exact ConcreteCategory.id_apply _` | 61 |
| `simp only [ConcreteCategory.id_apply]` | 78 |
| `simp` | 80 |

## 運用

- 省略してよいのは、autoParam が実際に閉じているフィールドだけ。`Functor` の
  `map_id`・`map_comp` や `CommaMorphism` の `w` のような小さいゴールは autoParam に
  任せて問題ない（上の計測でもプロファイラの閾値に現れなかった）
- 後で自分で証明するフィールドは、その意図をそのまま `:= sorry` と書く。意味の上でも
  「証明の借用書」で正しく、速度の上でもタクティクを走らせない
- 連鎖に注意。`Iso` の `inv` を `sorry` にすると、`hom_inv_id`・`inv_hom_id` の
  autoParam は `sorry` 入りのゴールで aesop を回すことになるので、これらも一緒に
  `sorry` と明示する
- 構造が完成に近づいたら、`sorry` にしていた等式系フィールドは `:= sorry` ごと消して
  autoParam に戻すと自動で閉じることがある

## 切り分けの手順

「宣言内のどこを編集しても一様に重い」ときは、行ではなく宣言単位で測る:

- `set_option trace.profiler true in` を宣言に付けて `lake env lean <file>` で流すと、
  時間つきの木がテキストで出る。ノードが多ければ
  `set_option trace.profiler.threshold 3000 in`（ms 単位）で足切りする。
  エディタでは info メッセージとして出るが、infoview 以外のプレーンテキストの
  クライアントでは `(trace)` としか表示されないので、CLI のほうが確実
- 合計だけ見たいなら `set_option profiler true`（平文のサマリが出る）
- ゴール単体の比較には `import Mathlib.Util.CountHeartbeats` して
  `#count_heartbeats in` を宣言の前に置く

## 根拠

- **公式リファレンス**: [Lean Language Reference §13.4 Function Application](https://lean-lang.org/doc/reference/latest/Terms/Function-Application/)
  — 「automatic parameter は関連付けられたタクティクを実行して引数を構成する」の一次出典
- **autoParam ガジェットの定義**: toolchain の `src/lean/Init/Tactics.lean`（v4.34.0-rc1 では
  L2653）。docstring に「optParam に似るが、与えられたタクティクを使う。elaboration にのみ
  作用する」
- **elaborator の実装**: `src/lean/Lean/Elab/SyntheticMVars.lean`（v4.34.0-rc1 では L449–450）。
  省略されたフィールドの合成に `fieldAutoParam` という専用分岐があり、失敗時に上記の
  エラーメッセージを生成する
- **フィールド宣言の実物**: `Mathlib/CategoryTheory/NatTrans.lean` L53–57（`naturality` の
  `:= by cat_disch`）。`Iso.hom_inv_id`・`Functor.map_id` など Mathlib の証明系フィールドの
  多くが同じ形
- **実測**: 本リポジトリ `Riehl/Ch2_Yoneda/S2_4_CategoryOfElements.lean` の `lemma_2_4_7`、
  2026-08-27
