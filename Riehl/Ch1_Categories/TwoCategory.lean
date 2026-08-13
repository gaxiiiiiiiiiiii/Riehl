import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Bicategory.Strict.Basic

-- ============================================================================
-- Riehl, Category Theory in Context, 1.7 The 2-category of categories
--
-- 自然変換の縦合成（補題1.7.1）と水平合成（補題1.7.4）、その特別な場合である
-- whiskering（注意1.7.6）、両者をつなぐ middle four interchange（補題1.7.7）、
-- そしてこれらを公理化した 2-圏（定義1.7.8）を扱う。
--
-- whiskering は 3.1 の錐の押し出しと 4.1-4.3 の三角等式で使う。
--
-- 参照した Mathlib:
--   Mathlib/CategoryTheory/NatTrans.lean          -- NatTrans, NatTrans.vcomp
--   Mathlib/CategoryTheory/Functor/Category.lean  -- 関手圏、NatTrans.hcomp、exchange
--   Mathlib/CategoryTheory/Whiskering.lean        -- whiskerLeft, whiskerRight
--   Mathlib/CategoryTheory/EssentiallySmall.lean  -- LocallySmall
--   Mathlib/CategoryTheory/Endomorphism.lean      -- End
--   Mathlib/CategoryTheory/Equivalence.lean       -- Equivalence.trans
--   Mathlib/CategoryTheory/Functor/Currying.lean  -- curry, uncurry, curryingEquiv
--   Mathlib/CategoryTheory/Category/Cat.lean      -- Cat.bicategory
--   Mathlib/CategoryTheory/Bicategory/Strict/Basic.lean -- Bicategory.Strict
-- ============================================================================

namespace Riehl

open CategoryTheory

-- ----------------------------------------------------------------------------
-- Recap
-- 演習1.7.i と注意1.7.3 で使うサイズの語彙。本文の small / locally small は
-- Mathlib では universe と次の2つのクラスに化ける
-- ----------------------------------------------------------------------------

namespace Recap

-- Mathlib/Logic/Small/Defs.lean より。α が universe w のある型と同型なとき w-small
class Small.{w, v} (α : Type v) : Prop where
  equiv_small : ∃ S : Type w, Nonempty (α ≃ S)

-- Mathlib/CategoryTheory/EssentiallySmall.lean より。hom 型がすべて w-small な圏
class LocallySmall.{w, v, u} (C : Type u) [Category.{v} C] : Prop where
  hom_small : ∀ X Y : C, Small.{w} (X ⟶ Y)

end Recap

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

-- ----------------------------------------------------------------------------
-- 関手圏（節の導入部）
-- 対象は関手 C ⥤ D、射は自然変換。Mathlib では Functor.category がこの圏を与える
-- ----------------------------------------------------------------------------

-- 恒等自然変換 id_F。成分は D の恒等射
#check CategoryTheory.NatTrans.id
def myIdNatTrans (F : C ⥤ D) : NatTrans F F where
  app c := 𝟙 (F.obj c)
  naturality := sorry

-- 補題1.7.1 — 縦合成 β · α。成分は成分どうしの合成
#check CategoryTheory.NatTrans.vcomp
def myVcomp {F G H : C ⥤ D} (α : NatTrans F G) (β : NatTrans G H) : NatTrans F H where
  app c := α.app c ≫ β.app c
  naturality := sorry

-- 系1.7.2 — 縦合成の結合律。Mathlib ではこの3つが Functor.category の中身
#check CategoryTheory.Category.assoc
example {F G H K : C ⥤ D} (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H K) :
    myVcomp (myVcomp α β) γ = myVcomp α (myVcomp β γ) := sorry

-- 系1.7.2 — 恒等自然変換が縦合成の左単位元であること
#check CategoryTheory.Category.id_comp
example {F G : C ⥤ D} (α : NatTrans F G) : myVcomp (myIdNatTrans F) α = α := sorry

-- 系1.7.2 — 恒等自然変換が縦合成の右単位元であること
#check CategoryTheory.Category.comp_id
example {F G : C ⥤ D} (α : NatTrans F G) : myVcomp α (myIdNatTrans G) = α := sorry

-- 注意1.7.3 — 関手圏のサイズ。小さい圏どうしの関手圏はまた小さい
-- 本文のもう一方（C が小さく D が locally small なら D^C も locally small）は演習1.7.i
#check CategoryTheory.Functor.category
example (A B : Type u₁) [SmallCategory A] [SmallCategory B] : SmallCategory (A ⥤ B) := sorry

-- 補題1.7.4 — 水平合成の成分を定める四角 (1.7.5) が可換であること
#check CategoryTheory.NatTrans.naturality
example {F G : C ⥤ D} {J K : D ⥤ E} (α : NatTrans F G) (γ : NatTrans J K) (c : C) :
    J.map (α.app c) ≫ γ.app (G.obj c) = γ.app (F.obj c) ≫ K.map (α.app c) := sorry

-- 補題1.7.4 — 水平合成 γ ∗ α : JF ⇒ KG。成分は四角 (1.7.5) の対角
-- 本の JF は、合成の向きが逆の Mathlib では F ⋙ J と書く
#check CategoryTheory.NatTrans.hcomp
def myHcomp {F G : C ⥤ D} {J K : D ⥤ E} (α : NatTrans F G) (γ : NatTrans J K) :
    NatTrans (F ⋙ J) (G ⋙ K) where
  app c := J.map (α.app c) ≫ γ.app (G.obj c)
  naturality := sorry

-- 注意1.7.6 — whiskering。関手 I を前から貼りつける（本の記法で αI）
#check CategoryTheory.Functor.whiskerLeft
def myWhiskerLeft (I : C ⥤ D) {F G : D ⥤ E} (α : NatTrans F G) :
    NatTrans (I ⋙ F) (I ⋙ G) where
  app c := α.app (I.obj c)
  naturality := sorry

-- 注意1.7.6 — 関手 J を後ろから貼りつける（本の記法で Jα）
-- 本の両側 whiskering JαI は、この2つを重ねたもの
#check CategoryTheory.Functor.whiskerRight
def myWhiskerRight {F G : C ⥤ D} (α : NatTrans F G) (J : D ⥤ E) :
    NatTrans (F ⋙ J) (G ⋙ J) where
  app c := J.map (α.app c)
  naturality := sorry

-- 補題1.7.7 — middle four interchange。縦横どちらの合成を先にしても同じ
#check CategoryTheory.NatTrans.exchange
example {F G H : C ⥤ D} {J K L : D ⥤ E} (α : NatTrans F G) (β : NatTrans G H)
    (γ : NatTrans J K) (δ : NatTrans K L) :
    myHcomp (myVcomp α β) (myVcomp γ δ) = myVcomp (myHcomp α γ) (myHcomp β δ) := sorry

-- ----------------------------------------------------------------------------
-- 定義1.7.8 — 2-圏
-- 本の 2-圏は 1-射の結合律・単位律を等式で課す strict なもの。Mathlib の Bicategory は
-- それらを結合子・単位子という同型で持つ弱い版で、等式に戻すのが Bicategory.Strict。
-- したがって本の 2-圏に対応するのは Bicategory + Bicategory.Strict
-- ----------------------------------------------------------------------------

#check CategoryTheory.Bicategory
#check CategoryTheory.Bicategory.Strict

-- 圏・関手・自然変換が 2-圏をなすこと（補題1.7.1・1.7.4・1.7.7 の帰結）は、
-- Mathlib では Cat 上のこの2つのインスタンス
#check CategoryTheory.Cat.bicategory
#check CategoryTheory.Cat.bicategory.strict

-- ----------------------------------------------------------------------------
-- 節末問題
-- ----------------------------------------------------------------------------

-- 演習1.7.i — C が小さく D が locally small なら D^C も locally small
#check CategoryTheory.instLocallySmallFunctor
example (A : Type u₁) [SmallCategory A] [LocallySmall.{u₁} D] :
    LocallySmall.{u₁} (A ⥤ D) := sorry

-- 演習1.7.ii — 水平合成を whiskering と縦合成で書き直す。Jα のあと γG を縦に合成する
#check CategoryTheory.Functor.NatTrans.hcomp_eq_whiskerRight_comp_whiskerLeft
example {F G : C ⥤ D} {J K : D ⥤ E} (α : NatTrans F G) (γ : NatTrans J K) :
    myHcomp α γ = myVcomp (myWhiskerRight α J) (myWhiskerLeft G γ) := sorry

-- 演習1.7.ii — もう一方の経路。γF のあと Kα を縦に合成する
#check CategoryTheory.Functor.NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight
example {F G : C ⥤ D} {J K : D ⥤ E} (α : NatTrans F G) (γ : NatTrans J K) :
    myHcomp α γ = myVcomp (myWhiskerLeft F γ) (myWhiskerRight α K) := sorry

-- 演習1.7.iii — 補題1.7.7 を示す問題。statement は上の補題1.7.7 に置いた

-- 演習1.7.iv — 恒等関手の自然自己準同型全体（圏の中心）が可換モノイドをなすこと
#check CategoryTheory.NatTrans.id_comm
example : CommMonoid (End (𝟭 C)) := sorry

-- 演習1.7.v — 圏同値の合成。1.5 の合成と同じ主張だが、本文が Prove (again) と書き
-- 脚注43 が両者を結んでいるので 1.7 でも置く。合成同値の単位側の自然同型
#check CategoryTheory.Equivalence.trans
example (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
    (F' : D ⥤ E) (G' : E ⥤ D) (η' : 𝟭 D ≅ F' ⋙ G') (ε' : G' ⋙ F' ≅ 𝟭 E) :
    𝟭 C ≅ (F ⋙ F') ⋙ (G' ⋙ G) := sorry

-- 演習1.7.v — 合成同値の余単位側の自然同型
#check CategoryTheory.Equivalence.trans
example (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
    (F' : D ⥤ E) (G' : E ⥤ D) (η' : 𝟭 D ≅ F' ⋙ G') (ε' : G' ⋙ F' ≅ 𝟭 E) :
    (G' ⋙ G) ⋙ (F ⋙ F') ≅ 𝟭 E := sorry

-- 演習1.7.vi — 双関手 F : C × D ⥤ E から、c ごとの関手 F(c, -) と f ごとの自然変換
-- F(f, -) を集めた関手 C ⥤ D ⥤ E を作る
#check CategoryTheory.Functor.curry
def myCurry (F : C × D ⥤ E) : C ⥤ D ⥤ E := sorry

-- 演習1.7.vi — 逆向きの構成
#check CategoryTheory.Functor.uncurry
def myUncurry (F : C ⥤ D ⥤ E) : C × D ⥤ E := sorry

-- 演習1.7.vi — 2つの構成が互いに逆であること（本文の1対1対応）のうち、双関手から出る向き
#check CategoryTheory.Functor.uncurry_obj_curry_obj
example (F : C × D ⥤ E) : myUncurry (myCurry F) = F := sorry

-- 演習1.7.vi — 1対1対応のうち、C ⥤ D ⥤ E から出る向き
#check CategoryTheory.Functor.curry_obj_uncurry_obj
example (F : C ⥤ D ⥤ E) : myCurry (myUncurry F) = F := sorry

-- 演習1.7.vi — 本文最後の一文（積の対称性から D ⥤ C ⥤ E とも1対1に対応する）は、
-- C と D を入れ替えた同じ主張なので statement は置かない

-- 演習1.7.vii — 定義1.3.13 の双関手と例1.4.9 の自然変換の族を演習1.7.vi の目で見直す問題。
-- 何を示すかが定まっていないので statement は置かない（行き先は 2.2 の米田埋め込み）

end Riehl
