import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.Category.PartialFun
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Data.List.TFAE

/-!
# 1.5 圏同値 (Equivalence of Categories)

Riehl, *Category Theory in Context* §1.5 の定義・命題・節末問題を出現順に並べたファイル。

扱うのは、自然変換を `C × 2 ⥤ D` として書き直す補題1.5.1、圏同値の定義1.5.4、full / faithful /
essentially surjective による特徴づけ（定理1.5.9）、骨格 (skeleton) と同値不変性。

後続節との関係:

* 定義1.5.4 の `MyEquivalence` は三角等式を課していない。三角等式込みの
  `CategoryTheory.Equivalence` との差は 4.3（命題4.3.5、`Equivalence.adjointifyη`）で回収する
* 定理1.5.9 の full / faithful / essentially surjective は 2.2 以降で繰り返し使う
* 補題1.5.5 の推移律は演習1.7.v で whiskering を使って再び証明する
* essentially small は 3.7 で `Small` 系のクラスとして再登場する

参照した Mathlib のファイル:

* `Mathlib/CategoryTheory/Equivalence.lean`
* `Mathlib/CategoryTheory/Functor/FullyFaithful.lean`
* `Mathlib/CategoryTheory/EssentialImage.lean`
* `Mathlib/CategoryTheory/Products/Basic.lean`
* `Mathlib/CategoryTheory/Category/Preorder.lean`
* `Mathlib/CategoryTheory/Skeletal.lean`
* `Mathlib/CategoryTheory/EssentiallySmall.lean`
* `Mathlib/CategoryTheory/IsConnected.lean`
* `Mathlib/CategoryTheory/SingleObj.lean`
* `Mathlib/CategoryTheory/Groupoid/VertexGroup.lean`
* `Mathlib/CategoryTheory/Action.lean`
* `Mathlib/CategoryTheory/Category/PartialFun.lean`
* `Mathlib/CategoryTheory/FintypeCat.lean`
* `Mathlib/CategoryTheory/Preadditive/Mat.lean`
* `Mathlib/Algebra/Category/Grp/Basic.lean`
* `Mathlib/Algebra/Category/Ring/Basic.lean`
* `Mathlib/Algebra/Category/ModuleCat/Basic.lean`
* `Mathlib/Algebra/Category/FGModuleCat/Basic.lean`
* `Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace Riehl

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/-!
## Recap

演習を解くのに定義の中身が要る Mathlib の宣言を写したもの。実際に演習で使うのは Mathlib 側で、
ここにあるのは中身を確認するための控え。
-/

namespace Recap

/-- `CategoryTheory.Functor.Full` の写し。各 hom 集合の上で `F.map` が全射。 -/
class Full (F : C ⥤ D) : Prop where
  map_surjective {X Y : C} : Function.Surjective (F.map (X := X) (Y := Y))

/-- `CategoryTheory.Functor.Faithful` の写し。各 hom 集合の上で `F.map` が単射。 -/
class Faithful (F : C ⥤ D) : Prop where
  map_injective : ∀ {X Y : C}, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))

/-- `CategoryTheory.Functor.essImage` の写し。`F` の像と同型な `D` の対象からなる性質。 -/
def essImage (F : C ⥤ D) : ObjectProperty D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

/-- `CategoryTheory.Functor.EssSurj` の写し。`D` のすべての対象が `F` の essential image に入る。 -/
class EssSurj (F : C ⥤ D) : Prop where
  mem_essImage (Y : D) : essImage F Y

end Recap

/-!
## 補題1.5.1

自然変換は、歩く矢 (walking arrow) `2` との積からの functor として書き直せる。ここで使う記号は:

* `C`, `D` : 圏
* `F`, `G : C ⥤ D` : 平行な functor
* `Fin 2` : 対象 `0`, `1` と非恒等射 `0 ⟶ 1` だけをもつ圏（前順序 `Fin 2` の圏構造）。本文の `2`
* `myIncl i : C ⥤ C × Fin 2` : 本文の `i₀`, `i₁ : 1 ⇒ 2` にあたる包含 `c ↦ (c, i)`
* `H : C × Fin 2 ⥤ D` : 自然変換を符号化する functor
-/

/-- 本文の `i₀`, `i₁` にあたる包含 functor `c ↦ (c, i)`。 -/
def myIncl (i : Fin 2) : C ⥤ C × Fin 2 :=
  (𝟭 C).prod' ((Functor.const C).obj i)

-- Mathlib に対応物なし
/-- 補題1.5.1。自然変換 `F ⟶ G` は、`myIncl 0 ⋙ H = F` かつ `myIncl 1 ⋙ H = G` を満たす
`H : C × Fin 2 ⥤ D` と1対1に対応する。図式 (1.5.2) の可換性は functor の等号で表している。 -/
def lemma_1_5_1 (F G : C ⥤ D) :
    (F ⟶ G) ≃ { H : C × Fin 2 ⥤ D // myIncl 0 ⋙ H = F ∧ myIncl 1 ⋙ H = G } :=
  sorry

/-!
## 定義1.5.4（圏同値）
-/

#check CategoryTheory.Equivalence

variable (C D) in
/-- 定義1.5.4。本文の圏同値は functor `F : C ⥤ D`, `G : D ⥤ C` と自然同型
`η : 𝟭 C ≅ F ⋙ G`, `ε : G ⋙ F ≅ 𝟭 D` の4つ組で、三角等式を課さない。Mathlib の
`CategoryTheory.Equivalence` はこれに三角等式 `functor_unitIso_comp` を加えたもの。 -/
structure MyEquivalence where
  /-- 本文の `F : C ⥤ D`。 -/
  functor : C ⥤ D
  /-- 本文の `G : D ⥤ C`。 -/
  inverse : D ⥤ C
  /-- 本文の `η : idC ≅ GF`。 -/
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  /-- 本文の `ε : FG ≅ idD`。 -/
  counitIso : inverse ⋙ functor ≅ 𝟭 D

/-!
## 補題1.5.5（圏同値は同値関係）

証明は演習1.5.vi(ii)。推移律は演習1.7.v で whiskering を使って再び証明する。
-/

namespace MyEquivalence

#check CategoryTheory.Equivalence.refl

variable (C) in
/-- 補題1.5.5（反射律）。 -/
def refl : MyEquivalence C C :=
  sorry

#check CategoryTheory.Equivalence.symm

/-- 補題1.5.5（対称律）。 -/
def symm (e : MyEquivalence C D) : MyEquivalence D C :=
  sorry

#check CategoryTheory.Equivalence.trans

/-- 補題1.5.5（推移律）。`C ≃ D` と `D ≃ E` から `C ≃ E` を作る。 -/
def trans (e : MyEquivalence C D) (f : MyEquivalence D E) : MyEquivalence C E :=
  sorry

end MyEquivalence

/-!
## 例1.5.6（点つき集合と部分関数）

集合と部分関数の圏 `Set∂` は点つき集合の圏 `Set∗` と同値。Mathlib では `PartialFun` と `Pointed`。
-/

#check partialFunEquivPointed

/-!
## 定義1.5.7・注意1.5.8（full / faithful / essentially surjective）

本文の3条件はそれぞれ Mathlib の次の class に対応する。full と faithful は hom 集合ごとの局所的な
条件で、対象の上の単射性・全射性は含まない（注意1.5.8）。
-/

#check CategoryTheory.Functor.Full
#check CategoryTheory.Functor.Faithful
#check CategoryTheory.Functor.EssSurj

-- 注意1.5.8 の充満部分圏。Mathlib では対象の性質 `ObjectProperty` から作る。
#check CategoryTheory.ObjectProperty.FullSubcategory
#check CategoryTheory.ObjectProperty.ι

/-!
## 定理1.5.9（圏同値の特徴づけ）
-/

#check CategoryTheory.Equivalence.isEquivalence_functor

/-- 定理1.5.9（→）。圏同値をなす functor は full かつ faithful かつ essentially surjective。 -/
theorem theorem_1_5_9_forward (e : MyEquivalence C D) :
    e.functor.Full ∧ e.functor.Faithful ∧ e.functor.EssSurj :=
  sorry

#check CategoryTheory.Functor.asEquivalence

/-- 定理1.5.9（←）。選択公理のもとで、full かつ faithful かつ essentially surjective な functor は
圏同値に延びる。`e.functor = F` は「`F` がその圏同値の片割れである」ことを言っている。 -/
noncomputable def theorem_1_5_9_converse (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] :
    { e : MyEquivalence C D // e.functor = F } :=
  sorry

/-!
## 補題1.5.10

`f : a ⟶ b` と同型 `u : a ≅ a'`, `v : b ≅ b'` から `f' : a' ⟶ b'` が一意に定まる。証明は演習1.5.iii。
Mathlib にこの補題そのものはなく、4つの図式の同値は `Iso` の書き換え補題に分かれている。
-/

#check CategoryTheory.Iso.comp_inv_eq

/-- 補題1.5.10。正方形を可換にする `f' : a' ⟶ b'` がただ一つ存在する。 -/
theorem lemma_1_5_10_existsUnique {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') :
    ∃! f' : a' ⟶ b', u.hom ≫ f' = f ≫ v.hom :=
  sorry

#check CategoryTheory.Iso.eq_inv_comp

/-- 補題1.5.10（後半）。本文の4つの図式は、どれか一つが可換ならすべて可換。 -/
theorem lemma_1_5_10_tfae {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b')
    (f' : a' ⟶ b') :
    List.TFAE [u.hom ≫ f' = f ≫ v.hom, f' = u.inv ≫ f ≫ v.hom,
      f = u.hom ≫ f' ≫ v.inv, u.inv ≫ f = f' ≫ v.inv] :=
  sorry

/-!
## 例1.5.11（essential image への同値）

full かつ faithful な functor は、その essential image への同値を定める。
-/

#check CategoryTheory.Functor.toEssImage
#check CategoryTheory.Equivalence.fullyFaithfulToEssImage

/-!
## 例1.5.12（行列と有限次元ベクトル空間）

本文の `Matₖ ≃ Vectᶠᵈₖ`。Mathlib には行列の圏 `Mat` と有限生成加群の圏 `FGModuleCat` はあるが、
この同値そのものはない。
-/

#check CategoryTheory.Mat
#check FGModuleCat

/-!
## 命題1.5.13（連結亜群）

本文の「連結」は、任意の2対象が射の有限なジグザグで結べること。Mathlib の
`CategoryTheory.IsConnected` が対応する。
-/

#check CategoryTheory.IsConnected
#check CategoryTheory.Groupoid.vertexGroupIsomOfMap

-- Mathlib に対応物なし（`Groupoid.vertexGroupIsomOfMap` は頂点群同士の同型を与えるだけ）
/-- 命題1.5.13。連結な亜群 `G` は、任意の対象 `g` の自己同型群 `g ⟶ g` を1対象の圏とみなした
`SingleObj (g ⟶ g)` と同値。 -/
noncomputable def proposition_1_5_13 (G : Type u₁) [Groupoid.{v₁} G] [IsConnected G] (g : G) :
    SingleObj (g ⟶ g) ≌ G :=
  sorry

/-!
## 系1.5.14（基点の取り替え）
-/

#check FundamentalGroup.fundamentalGroupMulEquivOfPathConnected

/-- 系1.5.14。弧状連結な空間では、基点の取り方によらず基本群は同型。 -/
noncomputable def corollary_1_5_14 {X : Type u₁} [TopologicalSpace X] [PathConnectedSpace X]
    (x y : X) : FundamentalGroup X x ≃* FundamentalGroup X y :=
  sorry

/-!
## 定義1.5.16・注意1.5.17（骨格）

各同型類にちょうど一つの対象をもつ圏が skeletal で、`C` と同値な skeletal な圏が `C` の骨格。
Mathlib の `Skeleton C` は同型類の代表を選んで作った充満部分圏で、`fromSkeleton` が同値を与える。
注意1.5.17 の「2つの圏が同値 ⟺ 骨格が同型」は `Equivalence.skeletonEquiv` が対象の間の全単射として
述べている。
-/

#check CategoryTheory.Skeletal
#check CategoryTheory.Skeleton
#check CategoryTheory.fromSkeleton
#check CategoryTheory.Equivalence.skeletonEquiv

/-!
## 例1.5.18（骨格の例）

(i) 連結亜群の骨格は自己同型群（命題1.5.13）。(ii) 前順序の骨格は半順序で、Mathlib では
`ThinSkeleton` に `PartialOrder` が入る。(iii) `Vectᶠᵈₖ` の骨格は `Matₖ`（例1.5.12）。
(iv) `Finiso`（有限集合と全単射）は Mathlib にないが、有限型の圏の骨格 `FintypeCat.Skeleton` が
対象を自然数に取り替える点では対応する。
-/

#check CategoryTheory.ThinSkeleton
#check CategoryTheory.ThinSkeleton.thinSkeletonPartialOrder
#check FintypeCat.Skeleton
#check FintypeCat.Skeleton.equivalence

/-!
## 例1.5.19（軌道・固定化群定理の圏論化）

作用亜群 `X//G` の骨格は軌道で添字づけられた固定化群の直和になる。Mathlib では作用亜群が
`ActionCategory`、固定化群と自己準同型の同型が `stabilizerIsoEnd`。
-/

#check CategoryTheory.ActionCategory
#check CategoryTheory.ActionCategory.stabilizerIsoEnd

/-!
## 同値不変性

圏論的に定義された概念は圏同値で保たれる、というのが本文の指針。反対圏・積・locally small・
essentially small について Mathlib は次を持つ。
-/

#check CategoryTheory.Equivalence.op
#check CategoryTheory.Equivalence.prod
#check CategoryTheory.LocallySmall
#check CategoryTheory.locallySmall_congr
#check CategoryTheory.EssentiallySmall
#check CategoryTheory.essentiallySmall_congr

/-!
## 節末問題
-/

/-!
### 演習1.5.i

補題1.5.1 を示す。statement は上の `lemma_1_5_1`。
-/

/-!
### 演習1.5.ii

Segal の圏 `Γ`（対象は有限集合、`S` から `T` への射は `θ : S → P(T)` で `α ≠ β` なら `θ(α)` と
`θ(β)` が交わらないもの、合成は `ψ(α) = ⋃_{β ∈ θ(α)} ϕ(β)`）が、有限点つき集合の圏の反対圏
`Fin∗ᵒᵖ` と同値であることを示す。

`Γ` を Lean で組むところから始まる問題で、圏の構成そのものが答えの一部になるため statement は
置かない。Mathlib に対応物なし（`Γ` も有限点つき集合の圏もない）。
-/

/-!
### 演習1.5.iii

補題1.5.10 を示す。statement は上の `lemma_1_5_10_existsUnique` と `lemma_1_5_10_tfae`。
-/

#check CategoryTheory.isIso_of_fully_faithful

/-- 演習1.5.iv(i)。full かつ faithful な functor は同型を reflect する。 -/
theorem exercise_1_5_iv_i (F : C ⥤ D) [F.Full] [F.Faithful] {x y : C} (f : x ⟶ y)
    (hf : IsIso (F.map f)) : IsIso f :=
  sorry

#check CategoryTheory.Functor.preimageIso

/-- 演習1.5.iv(ii)。full かつ faithful な functor は同型を create する。 -/
theorem exercise_1_5_iv_ii (F : C ⥤ D) [F.Full] [F.Faithful] (x y : C)
    (h : Nonempty (F.obj x ≅ F.obj y)) : Nonempty (x ≅ y) :=
  sorry

/-!
### 演習1.5.v

full だが faithful でない、あるいは faithful だが full でない functor で、同型を reflect も create
もしないものの例を挙げる。

例を挙げる問題なので statement は置かない（Lean で書くと圏そのものを `∃` で量化することになる）。
Mathlib に対応物なし。
-/

#check CategoryTheory.Functor.Full.comp

/-- 演習1.5.vi(i)。full な functor の合成は full。 -/
theorem exercise_1_5_vi_i_full (F : C ⥤ D) (G : D ⥤ E) [F.Full] [G.Full] : (F ⋙ G).Full :=
  sorry

#check CategoryTheory.Functor.Faithful.comp

/-- 演習1.5.vi(i)。faithful な functor の合成は faithful。 -/
theorem exercise_1_5_vi_i_faithful (F : C ⥤ D) (G : D ⥤ E) [F.Faithful] [G.Faithful] :
    (F ⋙ G).Faithful :=
  sorry

#check CategoryTheory.Functor.essSurj_comp

/-- 演習1.5.vi(i)。essentially surjective な functor の合成は essentially surjective。 -/
theorem exercise_1_5_vi_i_essSurj (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] :
    (F ⋙ G).EssSurj :=
  sorry

/-!
### 演習1.5.vi(ii)

`C ≃ D` かつ `D ≃ E` なら `C ≃ E`。statement は補題1.5.5 の `MyEquivalence.trans`。
-/

/-!
### 演習1.5.vii

離散圏と同値になる圏を特徴づける。

特徴づけを答える問題で、条件を statement に書くと答えそのものになるため statement は置かない。
Mathlib に対応物なし（`Discrete` と `EssentiallySmall` はあるが essentially discrete はない）。
-/

#check CategoryTheory.Discrete

/-!
### 演習1.5.viii

アフィン平面の亜群 `Affine` が、無限遠直線を指定した射影平面の亜群 `Proj|` と同値であることを示す。
射は点と直線の全単射で、接続関係を保ち反射するもの。`Proj| → Affine` は無限遠直線とその上の点を
取り除く functor で、逆向きの同値も明示的に書く。

平面の亜群を組むところから始まる問題なので statement は置かない。Mathlib に対応物なし
（`Configuration.ProjectivePlane` はあるが、その亜群はない）。
-/

/-!
### 演習1.5.ix

`I : Ab → Group`（包含）、`I : Ring → Ab`（乗法を忘れる）、`(−)ˣ : Ring → Group`（単元群）、
`I : Ring → Rng`（包含）、`I : Field → Ring`（包含）、`U : R Mod → Ab`（忘却）のうち、どれが
full、どれが faithful、どれが essentially surjective か、また圏同値を定めるものがあるかを調べる。

どの性質が成り立つかを答える問題なので statement は置かない。Mathlib にある functor は次の3つで、
`(−)ˣ`、`Rng`、`Field` に対応する圏や functor はない。
-/

section Exercise_1_5_ix

variable (R : Type u₁) [Ring R]

#check CategoryTheory.forget₂ CommGrpCat GrpCat
#check CategoryTheory.forget₂ RingCat AddCommGrpCat
#check CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat

end Exercise_1_5_ix

end Riehl
