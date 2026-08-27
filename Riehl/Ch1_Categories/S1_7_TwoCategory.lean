import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Center.Basic

-- ═══════════════════════════════════════════════════════════════════════════
-- 概要
-- ═══════════════════════════════════════════════════════════════════════════
/-!
# 1.7 圏の2-圏

自然変換の縦合成・水平合成・whiskering を定義し、圏・関手・自然変換が 2-圏をなすことを
見る節。本来の対象範囲（1.5、2〜4章）の外だが、whiskering（注意1.7.6）が 3.1 の錐の
押し出しと 4.1〜4.3 の三角等式で必要になるため入れる。関手圏 Dᶜ は第2章以降の米田の
補題の舞台になる。

この節の `my` 定義は data 部分まで書き、proof obligation（`naturality` など）だけを
`sorry` にする。補題1.7.1・1.7.4 の数学的内容が自然性の証明そのものだからである。

ファイル構成:
  Recap: `NatTrans`（定義1.4.1）と `Small`・`LocallySmall`（注意1.7.3）の写し
  本体:
    Part A: 縦合成と関手圏（補題1.7.1・系1.7.2・注意1.7.3）
    Part B: 水平合成・whiskering・interchange（補題1.7.4・注意1.7.6・補題1.7.7）
    Part C: 定義1.7.8（2-圏）は扱わない（理由の注記のみ）
    Part D: 節末問題（演習1.7.iii は Part B に掲載）

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Functor/Category.lean`
    （`NatTrans.vcomp`・`NatTrans.hcomp`・`NatTrans.exchange`・`Functor.category`）
  - `Mathlib/CategoryTheory/Whiskering.lean`（`Functor.whiskerLeft`・`Functor.whiskerRight`）
  - `Mathlib/CategoryTheory/EssentiallySmall.lean`（`LocallySmall`）
  - `Mathlib/CategoryTheory/Functor/Currying.lean`（`Functor.curry`・`Functor.currying`）
  - `Mathlib/CategoryTheory/Center/Basic.lean`（`CatCenter`）
-/

open CategoryTheory

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C]
variable {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

-- ═══════════════════════════════════════════════════════════════════════════
-- 前提: 演習が使う Mathlib の定義
-- ═══════════════════════════════════════════════════════════════════════════

namespace Recap

variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]

-- 定義1.4.1 の自然変換。データは成分の族 `app` で、自然性の四角形が条件
structure NatTrans (F G : C ⥤ D) : Type max u₂ v₃ where
  app (X : C) : F.obj X ⟶ G.obj X
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.map f ≫ app Y = app X ≫ G.map f

-- 型が universe `w` のある型と全単射で結べること。「集合と同サイズ」の Lean での言い換え
class Small (α : Type u₁) : Prop where
  equiv_small : ∃ S : Type w, Nonempty (α ≃ S)

-- 注意1.7.3 の「locally small」。すべての hom 型が `w`-small であること
class LocallySmall (C : Type u₂) [Category.{v₂} C] : Prop where
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y)

end Recap

-- ═══════════════════════════════════════════════════════════════════════════
-- 本体
-- ═══════════════════════════════════════════════════════════════════════════

-- ── Part A: 縦合成と関手圏（補題1.7.1・系1.7.2・注意1.7.3） ─────────────────

-- 恒等自然変換 id_F。成分はすべて恒等射
#check @CategoryTheory.NatTrans.id

def myNatTransId (F : C ⥤ D) : NatTrans F F where
  app c := 𝟙 (F.obj c)
  naturality {c c'} f := by simp

-- 補題1.7.1（縦合成）。成分ごとの合成が自然変換をなすことが補題の内容。
--    本の β · α は Lean の合成順では α のち β で、Mathlib では関手圏の `≫` がこれにあたる。
#check @CategoryTheory.NatTrans.vcomp

def myVcomp {F G H : C ⥤ D} (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app c := α.app c ≫ β.app c
  naturality {c c'} f := by
    rw [<- Category.assoc, α.naturality, Category.assoc]
    rw [β.naturality]; simp

-- 系1.7.2。関手 C ⥤ D と自然変換が圏 Dᶜ をなす。合成の結合律・単位律が証明課題。
--    Mathlib の instance と衝突させない演習用の定義なので、instance 化を求める警告は切る。
#check @CategoryTheory.Functor.category

example : Category.{max u₂ v₃} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := myNatTransId F
  comp α β := myVcomp α β
  id_comp {X Y} F := by
    simp only [myVcomp]
    apply NatTrans.ext
    ext c; simp only [myNatTransId]
    simp
  comp_id {X Y} F := by
    apply NatTrans.ext; ext c
    simp [myVcomp, myNatTransId]
  assoc {X Y Z W} F G H := by
    apply NatTrans.ext; ext c
    simp  [myVcomp]

-- 注意1.7.3（関手圏のサイズ）。C・D が small なら Dᶜ も small だが、large で locally small
--    な C・D では Dᶜ が locally small とは限らない。C が small で D が locally small なら
--    十分で、これは演習1.7.i にする。サイズの語彙は Mathlib では universe と `Small` 系の
--    クラスに化ける（Recap 参照）。
#check @CategoryTheory.LocallySmall

-- ── Part B: 水平合成・whiskering・interchange（補題1.7.4〜補題1.7.7） ────────

-- 補題1.7.4（水平合成）。成分は図式(1.7.5) の対角線で、それが自然変換をなすこと
--    （可換立方体）が補題の内容。本の γ ∗ α は Mathlib では α ◫ γ と書く。
#check @CategoryTheory.NatTrans.hcomp

def myHcomp {F G : C ⥤ D} {J K : D ⥤ E} (α : F ⟶ G) (γ : J ⟶ K) :
    F ⋙ J ⟶ G ⋙ K where
  app c := γ.app (F.obj c) ≫ K.map (α.app c)
  naturality {c c'} f := by
    simp only [Functor.comp_obj, Functor.comp_map, Category.assoc]
    rw [γ.naturality_assoc (F.map f), <- K.map_comp, α.naturality ]
    simp

-- 注意1.7.6（whiskering）。関手 I を手前に挟む方。成分は α の成分を I の像の上で取る
#check @CategoryTheory.Functor.whiskerLeft

def myWhiskerLeft (I : B ⥤ C) {F G : C ⥤ D} (α : F ⟶ G) : I ⋙ F ⟶ I ⋙ G where
  app b := α.app (I.obj b)
  naturality {X Y} f := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [α.naturality]


-- 注意1.7.6 の、関手 J を後ろに挟む方。成分は α の成分の J による像
#check @CategoryTheory.Functor.whiskerRight

def myWhiskerRight {F G : C ⥤ D} (α : F ⟶ G) (J : D ⥤ E) : F ⋙ J ⟶ G ⋙ J where
  app c := J.map (α.app c)
  naturality {X Y} f := by
    dsimp
    rw [<- J.map_comp, α.naturality]; simp

-- 補題1.7.7（middle four interchange、演習1.7.iii）。縦合成してから水平合成しても、
--    水平合成してから縦合成しても同じ自然変換になる。statement は Mathlib の演算で述べる
--    （my 定義は組むこと自体が演習で、以降の演習では使わない）。
#check @CategoryTheory.NatTrans.exchange

example {F G H : C ⥤ D} {J K L : D ⥤ E}
    (α : F ⟶ G) (β : G ⟶ H) (γ : J ⟶ K) (δ : K ⟶ L) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ (β ◫ δ) := by
  ext c
  rw [NatTrans.hcomp_app]; dsimp
  rw [NatTrans.hcomp_app, NatTrans.hcomp_app]
  conv => arg 2; rw [Category.assoc, <- Category.assoc (K.map (α.app c)), δ.naturality]
  simp






-- ── Part C: 定義1.7.8（2-圏）─ 扱わない ─────────────────────────────────────
--
-- 定義1.7.8 の 2-圏はこのプロジェクトでは扱わない。本文も「この例以外の 2-圏は本書に
-- 現れない」と明言しており、後続章で使うのは Part A・B の縦合成・関手圏・whiskering・
-- interchange だけ。関連する Mathlib は `Bicategory` + `Bicategory.Strict`（strict な 2-圏）。

-- ── Part D: 節末問題 ────────────────────────────────────────────────────────

-- 演習1.7.i。C が small で D が locally small なら Dᶜ は locally small。本の問題文は
--    「自然変換の集まりから集合への単射を作れ」で、ここでは `LocallySmall` の主張に言い換えた。
#check @CategoryTheory.instLocallySmallFunctor

example {C' : Type w} [SmallCategory C'] [LocallySmall.{w} D] :
    LocallySmall.{w} (C' ⥤ D) := sorry

-- 演習1.7.ii。水平合成を whiskering と縦合成で書き直す。どちらを先に挟むかで2通りある。
#check @CategoryTheory.Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight
#check @CategoryTheory.Functor.NatTrans.hcomp_eq_whiskerRight_comp_whiskerLeft

example {F G : C ⥤ D} {J K : D ⥤ E} (α : F ⟶ G) (γ : J ⟶ K) :
    α ◫ γ = Functor.whiskerLeft F γ ≫ Functor.whiskerRight α K := by
  ext c
  rw [NatTrans.hcomp_app, NatTrans.comp_app]
  rw[Functor.whiskerLeft_app, Functor.whiskerRight_app]

example {F G : C ⥤ D} {J K : D ⥤ E} (α : F ⟶ G) (γ : J ⟶ K) :
    α ◫ γ = Functor.whiskerRight α J ≫ Functor.whiskerLeft G γ := by
  ext c
  rw [NatTrans.hcomp_app, NatTrans.comp_app]
  rw[Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [γ.naturality]



-- 演習1.7.iii は補題1.7.7 として Part B に掲載した。

-- 演習1.7.iv。恒等関手の自然自己変換の全体（圏の中心）が可換モノイドをなす。
--    Mathlib は `CatCenter C := End (𝟭 C)` に `Monoid`（`End` の instance、積は合成の逆順）と
--    可換性の `IsMulCommutative` を別々に持ち、`CommMonoid` には束ねていない。
#check @CategoryTheory.CatCenter
#check @CategoryTheory.CatCenter.instIsMulCommutative

example (C : Type u₂) [Category.{v₂} C] : CommMonoid (𝟭 C ⟶ 𝟭 C) where
  one := 𝟙 (𝟭 C)
  mul α β := α ≫ β
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  mul_comm := sorry

-- 演習1.7.v。圏同値の合成。演習1.5.vi(ii)（`MyEquivalence.trans`）と同じ主張だが、本文が
--    「Prove (again)」と書き脚注43 が両者を結んでいるため両方載せる。こちらは `MyEquivalence`
--    に依存させず、F, G, η, ε を仮定に展開した自己完結の形で、合成の単位・余単位を構成する。
#check @CategoryTheory.Equivalence.trans

example (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
    (F' : D ⥤ E) (G' : E ⥤ D) (η' : 𝟭 D ≅ F' ⋙ G') (ε' : G' ⋙ F' ≅ 𝟭 E) :
    𝟭 C ≅ (F ⋙ F') ⋙ (G' ⋙ G) := sorry

example (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
    (F' : D ⥤ E) (G' : E ⥤ D) (η' : 𝟭 D ≅ F' ⋙ G') (ε' : G' ⋙ F' ≅ 𝟭 E) :
    (G' ⋙ G) ⋙ (F ⋙ F') ≅ 𝟭 E := sorry

-- 演習1.7.vi。二変数関手 C × D ⥤ E と C ⥤ (D ⥤ E) の全単射。本の (i)(ii) の与え方が
--    ちょうど curry の data にあたる。Mathlib は全単射を圏同値 `Functor.currying` まで強めて持つ。
#check @CategoryTheory.Functor.curry
#check @CategoryTheory.Functor.uncurry
#check @CategoryTheory.Functor.currying

example : (C × D ⥤ E) ≃ (C ⥤ D ⥤ E) := sorry

-- 演習1.7.vii。定義1.3.13 の hom 二変数関手 C(−,−) : Cᵒᵖ × C ⥤ Set を演習1.7.vi の視点で
--    curry すると、各対象 c に表現関手 C(c,−) を、各射 f に例1.4.9 の前合成 f∗ を割り当てる
--    関手になる。問題文は「見直せ」という指示なので、ここでは「curry した hom 関手が
--    coyoneda と同型」に言い換えた（もう一方の変数で curry すれば `yoneda` 側になる。
--    系2.2.8 の予告）。この iso 自体の Mathlib の対応物なし。
#check @CategoryTheory.Functor.hom
#check @CategoryTheory.coyoneda
#check @CategoryTheory.yoneda

example : Functor.curry.obj (Functor.hom C) ≅ coyoneda := sorry
