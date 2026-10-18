import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EqToHom

/-!
# 埋め込みと部分圏の同一視

本は対象に単射な忠実関手を埋め込みと呼び、`F : S ↪ A` と書いて S を A の部分圏と同一視する
（1.5、定義1.5.7 の後の段落）。この同一視の意味を、1.1 の部分圏の定義から確かめる。節に
対応しない話題なので解説資料はない。

Mathlib には一般の部分圏の型がなく、対象を絞る `ObjectProperty.FullSubcategory` と射を絞る
`WideSubcategory` の 2 段で表す。本の定義との往復も演習にする。
-/

open CategoryTheory

namespace Riehl

universe v u

variable {A : Type u} [Category.{v} A]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 部分圏（1.1、p.5）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏 A の部分圏とは、A の対象の集まりと射の集まりで、属する各射の域と余域、属する各対象の
恒等射、属する合成可能な射の対の合成を含むもの。部分圏が充満であるとは、属する対象の間の
A の射をすべて含むこと。
-/

structure Subcategory (A : Type u) [Category.{v} A] where
  objs : Set A
  homs {x y : A} : Set (x ⟶ y)
  dom_mem {x y : A} {f : x ⟶ y} : f ∈ homs → x ∈ objs
  cod_mem {x y : A} {f : x ⟶ y} : f ∈ homs → y ∈ objs
  id_mem {x : A} : x ∈ objs → 𝟙 x ∈ homs
  comp_mem {x y z : A} {f : x ⟶ y} {g : y ⟶ z} : f ∈ homs → g ∈ homs → f ≫ g ∈ homs

def Subcategory.IsFull (S : Subcategory A) : Prop :=
  ∀ {x y : A}, x ∈ S.objs → y ∈ S.objs → ∀ g : x ⟶ y, g ∈ S.homs

-- 部分圏はそれ自身が圏である。対象は属する対象、射は属する射。

instance : CoeSort (Subcategory A) (Type u) := ⟨fun S ↦ { x : A // x ∈ S.objs }⟩

instance Subcategory.category (S : Subcategory A) : Category.{v} S where
  Hom x y := { f : x.1 ⟶ y.1 // f ∈ S.homs }

  id x := ⟨𝟙 x.1, S.id_mem x.prop⟩
  comp f g := ⟨f.1 ≫ g.1, S.comp_mem f.prop g.prop⟩

-- 部分圏から A への包含関手。対象と射をそのまま送る。包含関手は忠実で、対象に単射である。

def Subcategory.ι (S : Subcategory A) : S ⥤ A where
  obj x := x.1
  map f := f.1


instance Subcategory.ι_faithful (S : Subcategory A) : S.ι.Faithful where
  map_injective := by
    intro ⟨x, Hx⟩ ⟨y, Hy⟩ ⟨(f : x ⟶ y), Hf⟩ ⟨(g : x ⟶ y), Hg⟩ E
    simp only [ι] at E
    apply Subtype.ext E



theorem Subcategory.ι_obj_injective (S : Subcategory A) : Function.Injective S.ι.obj := by
  intro ⟨x, Hx⟩ ⟨y, Hy⟩ (E : x = y)
  apply Subtype.ext E

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Mathlib の部分圏との対応
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
Mathlib は部分圏を 2 段で表す。対象の述語 `P : ObjectProperty A` から充満部分圏
`P.FullSubcategory` を作り、その上の射の述語 `Q : MorphismProperty P.FullSubcategory` で
射を絞って `WideSubcategory Q` を作る。`Q.IsMultiplicative` が、恒等射を含み合成で閉じる
という条件にあたる。本の `Subcategory` とこの 2 段の表現は互いに移り合い、圏として同型である。

構成: 射の述語とそれによる部分圏は Mathlib と同じ形で自前に書く(`MorphismProperty'`、
`IsMultiplicative`、`WideSubcategory'`、`wideSubcategoryInclusion'`)。以後は Mathlib のものを
使う。本の部分圏 S から述語 P, Q を取り出す向きと、P, Q から本の部分圏を作る向きを別に置き、
圏の同型 `Cat.of S ≅ Cat.of (WideSubcategory Q)` で一致を述べる。圏の同型は圏の圏 `Cat` の
同型として書く。圏同値 `≌` とは別物で、`Cat.equivOfIso` で同型から同値が得られる。
-/

section WideSubcategory

variable {C : Type u} [Category.{v} C]

-- 射の述語。各対象の対 X, Y と射 f : X ⟶ Y に命題を割り当てる。

#check MorphismProperty


def MorphismProperty' (C : Type u) [Category.{v} C] := ∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

-- 射の述語が恒等射を含み合成で閉じること。Mathlib は `ContainsIdentities` と
-- `IsStableUnderComposition` の 2 つのクラスに分けて `IsMultiplicative` で束ねる。

#check MorphismProperty.IsMultiplicative

class MorphismProperty'.IsMultiplicative (P : MorphismProperty' C) : Prop where
  id_mem (X : C) : P (𝟙 X)
  comp_mem {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : P f → P g → P (f ≫ g)

-- 射の述語 P による wide 部分圏。対象は C の対象すべて、射は P を満たす射。

#check WideSubcategory

structure WideSubcategory' (P : MorphismProperty' C) [P.IsMultiplicative] where
  obj : C

instance WideSubcategory'.category (P : MorphismProperty' C) [P.IsMultiplicative] :
    Category.{v} (WideSubcategory' P) where
  Hom X Y := { f : X.obj ⟶ Y.obj // P f }
  id X := ⟨𝟙 X.obj, sorry⟩
  comp f g := ⟨f.1 ≫ g.1, sorry⟩

#check wideSubcategoryInclusion

def wideSubcategoryInclusion' (P : MorphismProperty' C) [P.IsMultiplicative] :
    WideSubcategory' P ⥤ C where
  obj X := X.obj
  map f := f.1

end WideSubcategory

-- 本の部分圏と 2 段の表現との往復。

#check ObjectProperty
#check ObjectProperty.FullSubcategory
#check ObjectProperty.ι

def Subcategory.objectProperty (S : Subcategory A) : ObjectProperty A := sorry

def Subcategory.morphismProperty (S : Subcategory A) :
    MorphismProperty S.objectProperty.FullSubcategory := sorry

instance Subcategory.morphismProperty_isMultiplicative (S : Subcategory A) :
    S.morphismProperty.IsMultiplicative := sorry

def Subcategory.ofProperties (P : ObjectProperty A) (Q : MorphismProperty P.FullSubcategory)
    [Q.IsMultiplicative] : Subcategory A := sorry

#check Cat
#check Cat.of
#check Cat.equivOfIso

def Subcategory.isoWideSubcategory (S : Subcategory A) :
    Cat.of S ≅ Cat.of (WideSubcategory S.morphismProperty) := sorry

theorem Subcategory.isoWideSubcategory_hom_comp_inclusion (S : Subcategory A) :
    S.isoWideSubcategory.hom.toFunctor ⋙ wideSubcategoryInclusion S.morphismProperty ⋙
      S.objectProperty.ι = S.ι := sorry

-- 充満部分圏は、射の述語を省いた `P.FullSubcategory` と同型である。

def Subcategory.isoFullSubcategory (S : Subcategory A) (h : S.IsFull) :
    Cat.of S ≅ Cat.of S.objectProperty.FullSubcategory := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習 1.3.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- statement を置かない。関手の像が部分圏にならない例を見つけること自体が問いである。
-- 対象に単射でない関手では、F f と F g が合成可能でも f と g が合成可能とは限らない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 埋め込み（1.5、p.29）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
関手 F : S → A が埋め込みであるとは、忠実で対象に単射であること。充満忠実で対象に単射で
あるとき充満埋め込みという。Mathlib に対応する宣言はなく、`Functor.Faithful` と
`Function.Injective F.obj` を別に書く。
-/

variable {S : Type u} [Category.{v} S]

#check Functor.Faithful
#check Functor.Full

class Embedding (F : S ⥤ A) : Prop extends F.Faithful where
  obj_injective : Function.Injective F.obj

class FullEmbedding (F : S ⥤ A) : Prop extends Embedding F, F.Full

-- 埋め込みは射についても単射である（p.29 "faithfulness implies that the functor is
-- (globally) injective on arrows"）。

theorem Embedding.map_injective' (F : S ⥤ A) [Embedding F] {s t s' t' : S}
    (f : s ⟶ t) (f' : s' ⟶ t') (hs : F.obj s = F.obj s') (ht : F.obj t = F.obj t')
    (h : eqToHom hs ≫ F.map f' ≫ eqToHom ht.symm = F.map f) :
    HEq f f' := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 埋め込みの像
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
埋め込み F : S → A の像、すなわち F s の形の対象と F f の形の射の全体は、A の部分圏である。
恒等射は F(id_s) = id_{F s}、合成は F f ≫ F g = F (f ≫ g) で閉じる。合成が閉じるところで
対象の単射性を使う。
-/

def Embedding.image (F : S ⥤ A) [Embedding F] : Subcategory A where
  objs := Set.range F.obj
  homs := sorry
  dom_mem := sorry
  cod_mem := sorry
  id_mem := sorry
  comp_mem := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 部分圏との同一視
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
埋め込み F : S → A は S → im F → A と分解し、S → im F は圏の同型である。対象について
単射かつ像の上に全射、各 hom 集合について忠実性から単射かつ像の定義から全射であるから。
本が「S を A の部分圏と同一視する」というのはこの同型のことで、圏同値より強い。
-/

def Embedding.toImage (F : S ⥤ A) [Embedding F] : S ⥤ Embedding.image F := sorry

theorem Embedding.toImage_comp_ι (F : S ⥤ A) [Embedding F] :
    Embedding.toImage F ⋙ (Embedding.image F).ι = F := sorry

def Embedding.isoImage (F : S ⥤ A) [Embedding F] : Cat.of S ≅ Cat.of (Embedding.image F) :=
  sorry

theorem Embedding.isoImage_hom (F : S ⥤ A) [Embedding F] :
    (Embedding.isoImage F).hom.toFunctor = Embedding.toImage F := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 充満埋め込みの像
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 充満埋め込み F : S → A の像は A の充満部分圏である（p.29 最後の文）。

theorem FullEmbedding.image_isFull (F : S ⥤ A) [FullEmbedding F] :
    (Embedding.image F).IsFull := sorry

end Riehl
