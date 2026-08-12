import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

-- ═══════════════════════════════════════════════════════════════════════════
-- 概要
-- ═══════════════════════════════════════════════════════════════════════════
/-!
# 1.7 圏の2-圏

自然変換に縦合成・水平合成・whiskering という3つの演算を入れ、圏・関手・自然変換が2-圏をなす
ことを見る節。本書で扱う2-圏はこの一例だけだが、ここで作る演算は以降で繰り返し使われる。

後続節での使われ方:
  - 関手圏（系1.7.2）は §2.2–2.4 の米田の補題の舞台になる
  - whiskering（注意1.7.6）は §3.1 で錐を関手で押し出すとき、および §4.1–4.3 で三角等式の
    `Fη`・`εF`・`ηG`・`Gε` を書くときに使う

Mathlib との対応で注意する点:
  - 本の2-圏（定義1.7.8）は結合律・単位律を等式で課す strict なもの。Mathlib の `Bicategory`
    は associator と unitor を同型として持つ弱い版で、本の定義に当たるのは `Bicategory` と
    `Bicategory.Strict` の組。`Cat` には両方のインスタンスがある
  - 本の whiskering `Jα`（後合成）・`αI`（前合成）は、Mathlib ではそれぞれ `whiskerRight`・
    `whiskerLeft` になる。左右が本の記法と逆に見えるので注意

ファイル構成:
  Recap: 定義1.4.1 の自然変換と、注意1.7.3 の locally small
  本体:
    Part A（1–4）: 関手圏（補題1.7.1・系1.7.2・注意1.7.3・演習1.7.i）
    Part B（5–10）: 水平合成と whiskering（補題1.7.4・注意1.7.6・演習1.7.ii・補題1.7.7）
    Part C（11）: 2-圏（定義1.7.8）
    Part D（12–16）: 節末問題（演習1.7.iv–1.7.vii）

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/NatTrans.lean`（`NatTrans`・`vcomp`）
  - `Mathlib/CategoryTheory/Functor/Category.lean`（`Functor.category`・`hcomp`・`exchange`）
  - `Mathlib/CategoryTheory/Whiskering.lean`（`whiskerLeft`・`whiskerRight`・`whiskeringLeft`）
  - `Mathlib/CategoryTheory/Center/Basic.lean`（`CatCenter`）
  - `Mathlib/CategoryTheory/EssentiallySmall.lean`（`LocallySmall`）
  - `Mathlib/CategoryTheory/Functor/Currying.lean`（`curryObj`・`curryingEquiv`）
  - `Mathlib/CategoryTheory/Functor/Hom.lean`（`Functor.hom`）
  - `Mathlib/CategoryTheory/Yoneda.lean`（`coyoneda`）
  - `Mathlib/CategoryTheory/Category/Cat.lean`（`Cat.bicategory`・`Cat.bicategory.strict`）
-/

open CategoryTheory

universe w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- 本文の whiskering の図 B --I--> C --F,G--> D --J--> E に合わせて4つの圏を置く
variable {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C]
variable {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

-- ═══════════════════════════════════════════════════════════════════════════
-- Recap: 演習が使う Mathlib の定義
-- ═══════════════════════════════════════════════════════════════════════════

namespace Recap

variable {C : Type u₂} [Category.{v₂} C] {D : Type u₃} [Category.{v₃} D]

-- 定義1.4.1 の自然変換。本節の演習はすべてこの上に載る
structure NatTrans (F G : C ⥤ D) : Type max u₂ v₃ where
  app (X : C) : F.obj X ⟶ G.obj X
  naturality ⦃X Y : C⦄ (f : X ⟶ Y) : F.map f ≫ app Y = app X ≫ G.map f

-- 注意1.7.3 の locally small。本では hom が集合であることを指すが、Mathlib では hom の型が
-- universe `w` に縮むことで表す。同じものを §3.7 でも扱う
class LocallySmall.{w'} (C : Type u₂) [Category.{v₂} C] : Prop where
  hom_small : ∀ X Y : C, Small.{w'} (X ⟶ Y)

end Recap

-- ═══════════════════════════════════════════════════════════════════════════
-- 本体
-- ═══════════════════════════════════════════════════════════════════════════

-- ── Part A: 関手圏（補題1.7.1・系1.7.2・注意1.7.3） ─────────────────────────

-- 1. 恒等自然変換 `idF`（§1.7 冒頭）。成分がすべて恒等射であるものが自然変換になることを示す。
#check @CategoryTheory.NatTrans.id_app

def myNatTransId (F : C ⥤ D) : NatTrans F F where
  app X := 𝟙 (F.obj X)
  naturality := sorry

-- 2. 補題1.7.1（縦合成）。成分ごとの合成が再び自然変換になることを示す。
#check @CategoryTheory.NatTrans.vcomp

def myVcomp {F G H : C ⥤ D} (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app X := α.app X ≫ β.app X
  naturality := sorry

-- 3. 系1.7.2。関手と自然変換が圏 `D^C` をなすことを示す。データは 1 と 2 で作ってあるので、
--    残るのは縦合成の結合律と単位律。
#check @CategoryTheory.Functor.category

set_option warn.classDefReducibility false in
def myFunctorCategory : Category.{max u₂ v₃} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := myNatTransId F
  comp α β := myVcomp α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

-- 4. 演習1.7.i（注意1.7.3）。`C` が小さく `D` が locally small なら関手圏 `C ⥤ D` も
--    locally small。Mathlib の対応物は `EssentiallySmall.lean` 末尾の無名 instance で、
--    名前がないため `#check` は class 本体を指す。
#check @CategoryTheory.LocallySmall

example (S : Type w) [SmallCategory S] [LocallySmall.{w} D] : LocallySmall.{w} (S ⥤ D) := sorry

-- ── Part B: 水平合成と whiskering（補題1.7.4・注意1.7.6・補題1.7.7） ────────

-- 5. 補題1.7.4（水平合成）の四角形 (1.7.5) が可換であることを示す。すなわち `J α_c` のあとに
--    `γ_{Gc}` を合成したものと、`γ_{Fc}` のあとに `K α_c` を合成したものが一致する。
--    Mathlib の対応物は whiskering の言葉で述べられている。
#check @CategoryTheory.Functor.whiskerLeft_comp_whiskerRight

theorem my_hcomp_square {F G : C ⥤ D} {J K : D ⥤ E} (α : NatTrans F G) (γ : NatTrans J K)
    (X : C) : J.map (α.app X) ≫ γ.app (G.obj X) = γ.app (F.obj X) ≫ K.map (α.app X) := sorry

-- 6. 補題1.7.4。水平合成 `γ ∗ α : JF ⇒ KG` を作る。成分には 5 の等式の左辺を取る。
--    Mathlib の `hcomp` は右辺のほうを成分に取っているので、定義式そのものは一致しない。
#check @CategoryTheory.NatTrans.hcomp

def myHcomp {F G : C ⥤ D} {J K : D ⥤ E} (α : NatTrans F G) (γ : NatTrans J K) :
    NatTrans (F ⋙ J) (G ⋙ K) where
  app X := J.map (α.app X) ≫ γ.app (G.obj X)
  naturality := sorry

-- 7. 注意1.7.6 の whiskering のうち後合成 `Jα : JF ⇒ JG`。成分は `J α_c`。
--    Mathlib では左右が逆に見える名前 `whiskerRight` になる。
#check @CategoryTheory.Functor.whiskerRight

def myWhiskerRight {F G : C ⥤ D} (α : NatTrans F G) (J : D ⥤ E) :
    NatTrans (F ⋙ J) (G ⋙ J) where
  app X := J.map (α.app X)
  naturality := sorry

-- 8. 注意1.7.6 の whiskering のうち前合成 `αI : FI ⇒ GI`。成分は `α_{Ib}`。
--    本文の一般形 `JαI` は、この2つを合成して `(JαI)b = J α_{Ib}` として得られる。
#check @CategoryTheory.Functor.whiskerLeft

def myWhiskerLeft (I : B ⥤ C) {F G : C ⥤ D} (α : NatTrans F G) :
    NatTrans (I ⋙ F) (I ⋙ G) where
  app X := α.app (I.obj X)
  naturality := sorry

-- 9. 演習1.7.ii。水平合成を縦合成と whiskering で書き直す。5 の四角形の2つの道が、下の2通りの
--    書き換えに対応する。
#check @CategoryTheory.Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight

example {F G : C ⥤ D} {J K : D ⥤ E} (α : NatTrans F G) (γ : NatTrans J K) :
    myHcomp α γ = myVcomp (myWhiskerRight α J) (myWhiskerLeft G γ) := sorry

example {F G : C ⥤ D} {J K : D ⥤ E} (α : NatTrans F G) (γ : NatTrans J K) :
    myHcomp α γ = myVcomp (myWhiskerLeft F γ) (myWhiskerRight α K) := sorry

-- 10. 補題1.7.7・演習1.7.iii（middle four interchange）。先に縦に合成してから横に合成したものと、
--     先に横に合成してから縦に合成したものが一致することを示す。
#check @CategoryTheory.NatTrans.exchange

example {F G H : C ⥤ D} {J K L : D ⥤ E} (α : NatTrans F G) (β : NatTrans G H)
    (γ : NatTrans J K) (δ : NatTrans K L) :
    myHcomp (myVcomp α β) (myVcomp γ δ) = myVcomp (myHcomp α γ) (myHcomp β δ) := sorry

-- ── Part C: 2-圏（定義1.7.8） ───────────────────────────────────────────────

-- 11. 定義1.7.8。本の2-圏は1-射の結合律・単位律を等式で課すので、Mathlib では `Bicategory` と
--     `Bicategory.Strict` を合わせたものに当たる。`Cat` が strict であることを示す。
#check @CategoryTheory.Bicategory
#check @CategoryTheory.Bicategory.Strict
#check @CategoryTheory.Cat.bicategory
#check @CategoryTheory.Cat.bicategory.strict

example : Bicategory.Strict Cat.{v₂, u₂} := sorry

-- ── Part D: 節末問題 ────────────────────────────────────────────────────────

-- 12. 演習1.7.iv。恒等関手の自己自然変換の全体は可換モノイドをなし、圏の中心と呼ばれる。
--     モノイド構造は縦合成なので、非自明なのは可換性だけ。
#check @CategoryTheory.CatCenter
#check @CategoryTheory.NatTrans.id_comm

example (α β : 𝟭 C ⟶ 𝟭 C) : α ≫ β = β ≫ α := sorry

-- 13. 演習1.7.v。同値 `C ≃ D`、`D ≃ E` を与えるデータ（定義1.5.4）から、合成同値を定める
--     2つの自然同型を作る。同じ主張が `Equivalence.lean` の `MyEquivalence.trans`
--     （補題1.5.5・演習1.5.vi(ii)）にもあり、脚注43 のとおりこちらはその別証明にあたる。
#check @CategoryTheory.Equivalence.trans

example (F : C ⥤ D) (G : D ⥤ C) (F' : D ⥤ E) (G' : E ⥤ D)
    (η : 𝟭 C ≅ F ⋙ G) (_ε : G ⋙ F ≅ 𝟭 D)
    (η' : 𝟭 D ≅ F' ⋙ G') (_ε' : G' ⋙ F' ≅ 𝟭 E) :
    𝟭 C ≅ (F ⋙ F') ⋙ (G' ⋙ G) := sorry

example (F : C ⥤ D) (G : D ⥤ C) (F' : D ⥤ E) (G' : E ⥤ D)
    (_η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
    (_η' : 𝟭 D ≅ F' ⋙ G') (ε' : G' ⋙ F' ≅ 𝟭 E) :
    (G' ⋙ G) ⋙ (F ⋙ F') ≅ 𝟭 E := sorry

-- 14. 演習1.7.vi。双関手 `C × D ⥤ E` と関手 `C ⥤ D ⥤ E` が1対1に対応することを示す。
--     本の (i)(ii) は、この対応をほどいたときに何が残るかの記述にあたる。
#check @CategoryTheory.Functor.curryingEquiv

example : (C ⥤ D ⥤ E) ≃ (C × D ⥤ E) := sorry

-- 15. 演習1.7.vi の後半。積の対称性から `D ⥤ C ⥤ E` とも1対1に対応する。
#check @CategoryTheory.Functor.curryingFlipEquiv

example : (D ⥤ C ⥤ E) ≃ (C × D ⥤ E) := sorry

-- 16. 演習1.7.vii。定義1.3.13 の hom 双関手 `C^op × C ⥤ Set` を 14 の視点で見ると、curry した
--     ものが例1.4.9 の関手の族 `coyoneda` になる。系2.2.8（米田埋め込み）の予告にあたる。
--     Mathlib は `coyoneda` を `yoneda.flip` として定義しており、hom 双関手の curry と結ぶ
--     補題は置いていないので、ここでは同型として述べる。
#check @CategoryTheory.Functor.hom
#check @CategoryTheory.coyoneda

example : Functor.curryObj (Functor.hom C) ≅ coyoneda := sorry
