import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Coequalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# 3.6 完備な圏と余完備な圏

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 例3.6.3（Top の極限・余極限の一般形、p 進ソレノイド）、例3.6.4（配置空間）、
例3.6.7（要素の圏は引き戻し）、例3.6.8（押し出しとしての Bℕ と Bℤ）、注意3.6.9（CAT は
余完備でない）、例3.6.11（核対・同値関係・像分解）、脚注17〜21 は載せない。例3.6.8 の前後で
述べられる Cat の余完備性は、証明が系4.5.15 に延期されているので載せない。
-/

open CategoryTheory Limits Opposite

namespace Riehl

universe v u

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.6.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏 Set は余完備である。

構成: 定理3.5.11 に従い、余積と余等化子を組む。余積は非交和 Σ i, A i、余等化子は関係
      f a ∼ g a が生成する同値関係による商で、どちらも本文が与える。余極限錐であることと、
      そこから従う余完備性を演習にする。
-/

-- 関係 f a ∼ g a。`Quot` はこの関係が生成する同値関係による商を与える
#check Function.Coequalizer.Rel

def CoequalizerRel {A B : Type v} (f g : A → B) (b b' : B) : Prop :=
  ∃ a, f a = b ∧ g a = b'

-- 対象の族 A の余積の候補。頂点は非交和、脚は入射
#check Cofan.mk
#check Types.coproductColimitCocone

def typesCoproductCofan {I : Type v} (A : I → Type v) : Cofan A :=
  Cofan.mk (Σ i, A i) fun i ↦ TypeCat.ofHom fun x ↦ ⟨i, x⟩

def isColimitTypesCoproductCofan {I : Type v} (A : I → Type v) :
    IsColimit (typesCoproductCofan A) :=
  sorry

-- 平行な関数の対 f, g の余等化子の候補。頂点は商集合、脚は商写像
#check Types.coequalizerColimit

def typesCoequalizerCofork {A B : Type v} (f g : A ⟶ B) : Cofork f g :=
  Cofork.ofπ (TypeCat.ofHom (Quot.mk (CoequalizerRel f g))) sorry

def isColimitTypesCoequalizerCofork {A B : Type v} (f g : A ⟶ B) :
    IsColimit (typesCoequalizerCofork f g) :=
  sorry

#check Types.hasColimitsOfSize

theorem types_hasColimits : HasColimitsOfSize.{v, v} (Type v) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.6.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
空間の圏 Top は完備かつ余完備であり、台集合関手 U : Top → Set は連続かつ余連続である。

構成: 証明に従い、積（直積位相）、等化子（部分空間位相）、余積（非交和の位相）、余等化子
      （商位相）を組む。どの位相も Mathlib の型 `∀ i, X i`・`{x // _}`・`Σ i, X i`・`Quot r`
      の instance がそのまま本文の「最も粗い位相」「最も細かい位相」なので、頂点と脚の写像を
      書き、連続性と極限錐・余極限錐であることを演習にする。完備性・余完備性は定理3.5.11、
      U の連続性・余連続性は明示的な構成から示す。
-/

-- 位相空間 X, Y と連続写像 f : X → Y を Top の対象と射にする
#check TopCat.ofHom

-- 空間の族 X の積の候補。頂点は直積空間、脚は射影
#check TopCat.piFan

def topProductFan {I : Type v} (X : I → TopCat.{v}) : Fan X :=
  Fan.mk (TopCat.of (∀ i, X i)) fun i ↦ TopCat.ofHom ⟨fun x ↦ x i, sorry⟩

def isLimitTopProductFan {I : Type v} (X : I → TopCat.{v}) : IsLimit (topProductFan X) :=
  sorry

-- 連続写像の対 f, g の等化子の候補。頂点は台集合の等化子に部分空間位相を入れたもの、脚は包含
def topEqualizerFork {X Y : TopCat.{v}} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (P := TopCat.of {x : X // f x = g x})
    (TopCat.ofHom ⟨Subtype.val, sorry⟩) sorry

def isLimitTopEqualizerFork {X Y : TopCat.{v}} (f g : X ⟶ Y) :
    IsLimit (topEqualizerFork f g) :=
  sorry

-- 空間の族 X の余積の候補。頂点は非交和、脚は入射
#check TopCat.sigmaCofan

def topCoproductCofan {I : Type v} (X : I → TopCat.{v}) : Cofan X :=
  Cofan.mk (TopCat.of (Σ i, X i)) fun i ↦ TopCat.ofHom ⟨fun x ↦ ⟨i, x⟩, sorry⟩

def isColimitTopCoproductCofan {I : Type v} (X : I → TopCat.{v}) :
    IsColimit (topCoproductCofan X) :=
  sorry

-- 連続写像の対 f, g の余等化子の候補。頂点は台集合の商に商位相を入れたもの、脚は商写像
def topCoequalizerCofork {X Y : TopCat.{v}} (f g : X ⟶ Y) : Cofork f g :=
  Cofork.ofπ (P := TopCat.of (Quot (CoequalizerRel f g)))
    (TopCat.ofHom ⟨Quot.mk (CoequalizerRel f g), sorry⟩) sorry

def isColimitTopCoequalizerCofork {X Y : TopCat.{v}} (f g : X ⟶ Y) :
    IsColimit (topCoequalizerCofork f g) :=
  sorry

#check TopCat.topCat_hasLimitsOfSize

theorem topCat_hasLimits : HasLimitsOfSize.{v, v} TopCat.{v} := sorry

#check TopCat.topCat_hasColimitsOfSize

theorem topCat_hasColimits : HasColimitsOfSize.{v, v} TopCat.{v} := sorry

#check TopCat.forget_preservesLimitsOfSize

theorem topCat_forget_preservesLimits :
    PreservesLimitsOfSize.{v, v} (forget TopCat.{v}) :=
  sorry

#check TopCat.forget_preservesColimitsOfSize

theorem topCat_forget_preservesColimits :
    PreservesColimitsOfSize.{v, v} (forget TopCat.{v}) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.6.5
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C が完備かつ余完備ならば、任意の c ∈ C について、スライス圏 c/C と C/c も完備かつ余完備である。

構成: c/C は Mathlib の `Under c`（命題3.4.8）。完備性は命題3.4.8 の創出から従う。余完備性は
      証明に従い、始対象 id_c、始対象の下の広い押し出しとしての余積（補題3.5.15 の双対）、
      連結な余極限（命題3.4.8）の順に組み、定理3.5.11 で閉じる。C/c の半分は双対なので
      置かない。
-/

-- c/C の対象 c → x を `Under.mk` で作る
#check Under.mk
#check Under.mkIdInitial

noncomputable def underMkIdInitial (c : C) : IsInitial (Under.mk (𝟙 c)) := sorry

-- 補題3.5.15 の双対：始対象 T からの射の族 (T → A i) の広い押し出しは、族 A の余積である
#check WidePushoutShape.wideSpan

def isColimitCofanOfWidePushoutInitial {I : Type v} (A : I → C) {T : C} (hT : IsInitial T)
    (c : Cocone (WidePushoutShape.wideSpan T A fun i ↦ hT.to (A i))) (hc : IsColimit c) :
    IsColimit (Cofan.mk c.pt fun i ↦ c.ι.app (some i)) :=
  sorry

#check Under.hasColimitsOfShape_of_isConnected

theorem under_hasCoproducts (c : C) [HasColimitsOfSize.{v, v} C] :
    HasCoproducts.{v} (Under c) :=
  sorry

#check Under.instHasColimitsOfSizeOfHasWidePushouts

theorem under_hasColimits (c : C) [HasColimitsOfSize.{v, v} C] :
    HasColimitsOfSize.{v, v} (Under c) :=
  sorry

#check Under.instHasLimits

theorem under_hasLimits (c : C) [HasLimitsOfSize.{v, v} C] :
    HasLimitsOfSize.{v, v} (Under c) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.6.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏 Cat と CAT は完備である。

構成: 定理3.5.11 に従い、積と等化子を組む。積は定義1.3.12 の高い項数版 ∀ i, A i（演習3.4.v の
      `CategoryTheory.pi`）で、射影は `Pi.eval`。等化子は Fc = Gc となる対象と Ff = Gf となる
      射からなる C の部分圏で、射の条件は対象の等式を `eqToHom` で運んで書く。
      CAT（`Cat.{v, u}`）は、積 ∀ i, A i の対象の宇宙が max v u に上がって `Cat.{v, u}` に
      戻らないので、Cat（`Cat.{v, v}`）だけ置く。
-/

-- 圏の族 A の積の候補。頂点は積圏、脚は射影
def catPiFan {I : Type v} (A : I → Cat.{v, v}) : Fan A :=
  Fan.mk (Cat.of (∀ i, A i)) fun i ↦ (Pi.eval (fun i ↦ (A i : Type v)) i).toCatHom

def isLimitCatPiFan {I : Type v} (A : I → Cat.{v, v}) : IsLimit (catPiFan A) := sorry

-- 平行な関手の対 F, G の等化子となる部分圏。対象は Fc = Gc となる c
structure EqualizerCat {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) where
  obj : C
  eq : F.obj obj = G.obj obj

-- 射は Ff = Gf となる f。両辺の定義域と値域を対象の等式で揃える
instance EqualizerCat.category {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) :
    Category (EqualizerCat F G) where
  Hom X Y := { f : X.obj ⟶ Y.obj // F.map f ≫ eqToHom Y.eq = eqToHom X.eq ≫ G.map f }
  id X := ⟨𝟙 X.obj, sorry⟩
  comp f g := ⟨f.1 ≫ g.1, sorry⟩

-- 部分圏の包含
def equalizerCatIncl {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) :
    EqualizerCat F G ⥤ C where
  obj X := X.obj
  map f := f.1

-- 包含と F, G の合成は一致する
theorem equalizerCatIncl_comp {C D : Type*} [Category C] [Category D] (F G : C ⥤ D) :
    equalizerCatIncl F G ⋙ F = equalizerCatIncl F G ⋙ G :=
  sorry

-- Cat における等化子の候補
def catEqualizerFork {C D : Cat.{v, v}} (F G : C ⟶ D) : Fork F G :=
  Fork.ofι (equalizerCatIncl F.toFunctor G.toFunctor).toCatHom sorry

def isLimitCatEqualizerFork {C D : Cat.{v, v}} (F G : C ⟶ D) :
    IsLimit (catEqualizerFork F G) :=
  sorry

#check Cat.instHasLimits

theorem cat_hasLimits : HasLimitsOfSize.{v, v} Cat.{v, v} := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 完備性と余完備性の同値不変性（命題3.6.10 の前）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏の完備性と余完備性は、圏同値で不変である。

構成: 極限の半分だけ置く。余極限の半分は双対である。
-/

#check Adjunction.has_limits_of_equivalence

theorem hasLimits_of_equivalence {D : Type*} [Category.{v} D] (e : C ≌ D)
    [HasLimitsOfSize.{v, v} C] : HasLimitsOfSize.{v, v} D :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.6.10
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
poset P が圏として完備かつ余完備であることと、P が完備束であること、すなわち任意の部分集合
A ⊂ P が下限と上限を両方持つことは同値である。

構成: 証明の一文目「前順序集合では図式の極限はその対象の下限である」を、錐が極限錐であることと
      頂点が対象の集合の下限であることの同値として置く。そこから、完備束なら完備であることと、
      完備なら任意の部分集合が下限を持つことを置く。余極限の半分は双対なので置かない。
      poset は `PartialOrder`、圏の構造は例2.2.1 で組んだ `Preorder.smallCategory`。
-/

-- 集合 A の下限（最大下界）
#check IsGLB

theorem nonempty_isLimit_iff_isGLB {P : Type v} [Preorder P] {F : J ⥤ P} (c : Cone F) :
    Nonempty (IsLimit c) ↔ IsGLB (Set.range F.obj) c.pt :=
  sorry

-- 任意の部分集合が下限 sInf と上限 sSup を持つ poset
#check CompleteLattice
#check CategoryTheory.Limits.CompleteLattice.hasLimits_of_completeLattice

theorem hasLimits_of_completeLattice' {P : Type v} [CompleteLattice P] :
    HasLimitsOfSize.{v, v} P :=
  sorry

theorem exists_isGLB_of_hasLimits {P : Type v} [PartialOrder P] [HasLimitsOfSize.{v, v} P]
    (A : Set P) : ∃ a, IsGLB A a :=
  sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 図式 X : BG → Set の余極限を群論の言葉で記述する問題で、statement を書くことが解答になる
-- ので置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の小図式 F : J → Set の余極限は、F の要素の圏の連結成分の集合 π₀(∫F) と同型である。
余極限錐は何か。

構成: 頂点 π₀(∫F) を持つ F 下の錐を組み、それが余極限錐であることを示す。そこから同型を得る。
      要素の圏は演習3.4.ii の `Functor.Elements`。
-/

-- 圏 J の連結成分の集合。対象を射のジグザグで結ばれるという同値関係で割った商
#check ConnectedComponents

def elementsComponentsCocone (F : J ⥤ Type v) : Cocone F where
  pt := ConnectedComponents F.Elements
  ι := sorry

def isColimitElementsComponentsCocone (F : J ⥤ Type v) :
    IsColimit (elementsComponentsCocone F) :=
  sorry

noncomputable def colimitIsoConnectedComponentsElements (F : J ⥤ Type v) :
    colimit F ≅ ConnectedComponents F.Elements :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 集合と部分関数の圏の二項余積・二項積・スマッシュ積の公式を与える問題で、statement を書く
-- ことが解答になるので置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
(i) クイバーの圏 Quiver、すなわち平行対の圏から Set への関手の圏は、完備かつ余完備である。
(ii) の積の計算と (iii) の Graph の反例は、statement を書くことが解答になるので置かない。

構成: 平行対の圏は等化子図式の添字圏 `WalkingParallelPair`（3.1）。命題3.4.9 の関手圏の
      極限から従う。
-/

#check functorCategoryHasLimitsOfSize

theorem quiver_hasLimits : HasLimitsOfSize.{v, v} (WalkingParallelPair ⥤ Type v) := sorry

#check functorCategoryHasColimitsOfSize

theorem quiver_hasColimits : HasColimitsOfSize.{v, v} (WalkingParallelPair ⥤ Type v) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.v
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 二重圏の定義を初等的なデータに展開する問題で、statement を書くことが解答になるので置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- J◁ と J▷ を Cat の押し出しとして定義する問題。Cat の押し出しの存在は本文でも系4.5.15 に
-- 延期されていて Mathlib にもないので置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.vii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 整除関係による自然数の poset の極限と余極限を記述する問題で、statement を書くことが解答に
-- なるので置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.viii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 配置空間の関手を定義し、Conf_n(X) が関手にならない理由を説明する問題。載せない例3.6.4 の
-- 上に立つので置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.6.ix
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
ファイバー空間 p : E → B を Top の射とする。
(i) ファイバー空間の写像 (g, f) : p' → p は、点 b ∈ B' 上のファイバーから f(b) ∈ B 上の
    ファイバーへの標準的な写像を誘導する。
(ii) ファイバー空間の積のファイバーは、ファイバーの積である。
(iii) 自明なファイバー空間 B × F → B のファイバーは F と同型である。
(v) B 上のファイバー空間にその連続切断の集合を対応させる割り当ては関手 Π_B : Top/B → Set を
    定める。
(vi) 射を引き戻しの四角形に限った部分圏 Top^𝟚_pb について、同じ割り当ては関手
    Π : (Top^𝟚_pb)^op → Set を定める。
(iv) の同型射の特徴づけと (vii) の整合性の記述は、statement を書くことが解答になるので置かない。

構成: 点 b ∈ B は一点空間からの射 b : ∗ → B、b 上のファイバーは (3.1.17) のとおり p の b に
      沿った引き戻し `pullback p b`。B 上のファイバー空間 p, q の積は Top/B の積、すなわち
      引き戻し E ×_B E' から B への射（命題3.4.8）。Top/B は `Over B`、ファイバー空間の圏
      Top^𝟚 は `Arrow TopCat`、Top^𝟚_pb は引き戻しの四角形を射の性質 `MorphismProperty` と
      して `WideSubcategory` で切り出す（どちらも Topics/Embedding）。
-/

-- (i)
def fiberMap {E E' B B' : TopCat.{v}} (p : E ⟶ B) (p' : E' ⟶ B') (g : E' ⟶ E) (f : B' ⟶ B)
    (w : g ≫ p = p' ≫ f) (b : TopCat.of PUnit.{v + 1} ⟶ B') :
    pullback p' b ⟶ pullback p (b ≫ f) :=
  sorry

-- (ii)
def fiberPullbackIso {E E' B : TopCat.{v}} (p : E ⟶ B) (q : E' ⟶ B)
    (b : TopCat.of PUnit.{v + 1} ⟶ B) :
    pullback (pullback.fst p q ≫ p) b ≅ pullback p b ⨯ pullback q b :=
  sorry

-- (iii) 自明なファイバー空間は直積空間からの射影
def trivialFiberSpace (B F : TopCat.{v}) : TopCat.of (B × F) ⟶ B :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

def fiberTrivialIso (B F : TopCat.{v}) (b : TopCat.of PUnit.{v + 1} ⟶ B) :
    pullback (trivialFiberSpace B F) b ≅ F :=
  sorry

-- (v) B 上のファイバー空間 p : E → B の連続切断 s : B → E は p ∘ s = id_B を満たす連続写像
#check Over

def sectionsFunctorOver (B : TopCat.{v}) : Over B ⥤ Type v := sorry

-- (vi) 射が引き戻しの四角形であるという、Top^𝟚 の射の性質
def IsPullbackSquare : MorphismProperty (Arrow TopCat.{v}) :=
  fun {p q} sq ↦ IsPullback sq.left p.hom q.hom sq.right

instance : IsPullbackSquare.IsMultiplicative where
  id_mem := sorry
  comp_mem := sorry

def sectionsFunctorPullbackSquares :
    (WideSubcategory IsPullbackSquare.{v})ᵒᵖ ⥤ Type v :=
  sorry

end Riehl
