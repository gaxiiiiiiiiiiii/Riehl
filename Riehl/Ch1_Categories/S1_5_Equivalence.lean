-- ---------------------------------------------------------------------------
-- Riehl, Category Theory in Context
-- §1.5 Equivalence of categories
--
-- 圏同値を扱う節。自然変換を C × 2 → D なる関手として言い換える補題1.5.1 から
-- 始め、同値の定義1.5.4、full・faithful・essentially surjective による特徴づけ
-- （定理1.5.9）、そして骨格（定義1.5.16）までを扱う。
--
-- 後続節との関係:
--   1.7 -- 演習1.7.v が本節の MyEquivalence.trans を別証明で再演する
--   3.7 -- 骨格と essentially small の語彙をここから引き継ぐ
--   4.3 -- 命題4.3.5 で、本の同値と Mathlib の三角等式込みの同値の差を回収する
--
-- 参照した Mathlib のファイル:
--   Mathlib/CategoryTheory/Equivalence.lean
--   Mathlib/CategoryTheory/Functor/FullyFaithful.lean
--   Mathlib/CategoryTheory/EssentialImage.lean
--   Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean
--   Mathlib/CategoryTheory/Iso.lean
--   Mathlib/CategoryTheory/Products/Basic.lean
--   Mathlib/CategoryTheory/Category/Preorder.lean
--   Mathlib/CategoryTheory/Discrete/Basic.lean
--   Mathlib/CategoryTheory/IsConnected.lean
--   Mathlib/CategoryTheory/SingleObj.lean
--   Mathlib/CategoryTheory/Groupoid/VertexGroup.lean
--   Mathlib/CategoryTheory/Skeletal.lean
--   Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean
--   Mathlib/Algebra/Category/Grp/Adjunctions.lean
--   Mathlib/Algebra/Category/Ring/Basic.lean
--   Mathlib/Algebra/Category/ModuleCat/Basic.lean
-- ---------------------------------------------------------------------------

import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.Skeletal
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.List.TFAE

namespace Riehl

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

-- ---------------------------------------------------------------------------
-- Recap
--
-- 本節の演習で道具として使う Mathlib の定義の写し。実際の演習で使うのは
-- Mathlib のもので、ここにあるのは中身を見るための控え
-- ---------------------------------------------------------------------------

namespace Recap

-- 本文の「連結」（任意の2対象が射の有限なジグザグで結ばれる）に対応する
-- Mathlib の語彙。Zag は向きを問わない射1本、Zigzag はその反射推移閉包
def Zag {J : Type u₁} [Category.{v₁} J] (j₁ j₂ : J) : Prop :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

def Zigzag {J : Type u₁} [Category.{v₁} J] : J → J → Prop :=
  Relation.ReflTransGen Zag

-- Mathlib の連結性は「discrete 圏への関手がつねに定数」で定義され、
-- Zigzag による特徴づけと同値であることが別に示されている
class IsPreconnected (J : Type u₁) [Category.{v₁} J] : Prop where
  iso_constant : ∀ {α : Type u₁} (F : J ⥤ Discrete α) (j : J),
    Nonempty (F ≅ (Functor.const J).obj (F.obj j))

class IsConnected (J : Type u₁) [Category.{v₁} J] : Prop extends IsPreconnected J where
  [is_nonempty : Nonempty J]

-- 定義1.5.16 の skeletal が使う「同型である」という対象間の関係
def IsIsomorphic (X Y : C) : Prop :=
  Nonempty (X ≅ Y)

end Recap

-- ---------------------------------------------------------------------------
-- 補題1.5.1（証明は演習1.5.i）
--
-- 平行な関手 F, G : C ⇒ D に対し、自然変換 α : F ⇒ G は、C × 2 → D であって
-- i₀, i₁ に沿った制限が F, G になる関手 H と1対1に対応する。
-- 2 は walking arrow（対象 0, 1 と非恒等射 0 → 1 だけを持つ圏）で、Lean では
-- preorder Fin 2 から誘導される圏として実現する
-- ---------------------------------------------------------------------------

-- c ↦ (c, j) という包含。本の i₀, i₁ : 1 ⇒ 2 を C 倍したものにあたる
def myWalkingArrowIncl (C : Type u₁) [Category.{v₁} C] (j : Fin 2) : C ⥤ C × Fin 2 :=
  Functor.prod' (𝟭 C) ((Functor.const C).obj j)

-- 補題1.5.1。制限は本の図式どおり関手の等号として課す
-- Mathlib に対応物なし（walking arrow 圏そのものが Mathlib にない）
example (F G : C ⥤ D) :
    (F ⟶ G) ≃ { H : C × Fin 2 ⥤ D //
      myWalkingArrowIncl C 0 ⋙ H = F ∧ myWalkingArrowIncl C 1 ⋙ H = G } :=
  sorry

-- ---------------------------------------------------------------------------
-- 定義1.5.4
--
-- 圏同値とは、関手 F : C ⇄ D : G と自然同型 η : id_C ≅ GF、ε : FG ≅ id_D の組。
-- Mathlib の CategoryTheory.Equivalence はこれに加えて三角等式
-- functor_unitIso_comp を要求する（つまり adjoint equivalence）。本の定義には
-- 三角等式がないので、ここでは自前の MyEquivalence を置く。三角等式は η を
-- 取り替えれば必ず満たせて両者は一致するが、それは命題4.3.5 で扱う
-- ---------------------------------------------------------------------------

structure MyEquivalence (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] where
  functor : C ⥤ D
  inverse : D ⥤ C
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  counitIso : inverse ⋙ functor ≅ 𝟭 D

#check @CategoryTheory.Equivalence

-- ---------------------------------------------------------------------------
-- 補題1.5.5（証明は演習1.5.vi）
--
-- 圏同値は同値関係を定める。結論ごとに反射律・対称律・推移律に分ける。
-- 推移律だけは 1.7 の演習1.7.v から参照するので名前を付ける
-- ---------------------------------------------------------------------------

-- 補題1.5.5 のうち反射律
example (C : Type u₁) [Category.{v₁} C] : MyEquivalence C C :=
  sorry

#check @CategoryTheory.Equivalence.refl

-- 補題1.5.5 のうち対称律
example (e : MyEquivalence C D) : MyEquivalence D C :=
  sorry

#check @CategoryTheory.Equivalence.symm

-- 補題1.5.5 のうち推移律（演習1.5.vi(ii) でもある）
def MyEquivalence.trans (e : MyEquivalence C D) (f : MyEquivalence D E) :
    MyEquivalence C E :=
  sorry

#check @CategoryTheory.Equivalence.trans

-- ---------------------------------------------------------------------------
-- 定義1.5.7
--
-- full は C(x,y) → D(Fx,Fy) が全射、faithful は単射、essentially surjective on
-- objects は任意の d ∈ D にある c ∈ C で d ≅ Fc となること。full と faithful は
-- 局所的な条件で、大域的な全射性・単射性ではない（注意1.5.8）
-- ---------------------------------------------------------------------------

#check @CategoryTheory.Functor.Full
#check @CategoryTheory.Functor.Faithful
#check @CategoryTheory.Functor.EssSurj

-- ---------------------------------------------------------------------------
-- 定理1.5.9（圏同値の特徴づけ）
--
-- 順方向は、同値の一部をなす関手が full かつ faithful かつ essentially
-- surjective であること。逆方向は、選択公理のもとでその逆が成り立つこと。
-- 結論ごとに演習を分ける
-- ---------------------------------------------------------------------------

-- 定理1.5.9 の順方向のうち faithful
example (e : MyEquivalence C D) : e.functor.Faithful :=
  sorry

#check @CategoryTheory.Equivalence.faithful_functor

-- 定理1.5.9 の順方向のうち full
example (e : MyEquivalence C D) : e.functor.Full :=
  sorry

#check @CategoryTheory.Equivalence.full_functor

-- 定理1.5.9 の順方向のうち essentially surjective
example (e : MyEquivalence C D) : e.functor.EssSurj :=
  sorry

#check @CategoryTheory.Equivalence.essSurj_functor

-- 定理1.5.9 の逆方向。選択公理を使うので、得られる同値は F ごとに一意ではなく
-- 存在の主張として述べる
example (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] :
    ∃ e : MyEquivalence C D, e.functor = F :=
  sorry

#check @CategoryTheory.Functor.IsEquivalence
#check @CategoryTheory.Functor.asEquivalence

-- ---------------------------------------------------------------------------
-- 補題1.5.10
--
-- 射 f : a ⟶ b と同型 u : a ≅ a'、v : b ≅ b' に対し、正方形を可換にする
-- f' : a' ⟶ b' がただ一つ定まる。4つの図式が互いに同値であることは演習1.5.iii
-- ---------------------------------------------------------------------------

-- 補題1.5.10 の存在と一意性の部分
-- Mathlib に対応物なし（一意性込みの補題はない）
example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') :
    ∃! f' : a' ⟶ b', u.hom ≫ f' = f ≫ v.hom :=
  sorry

-- ---------------------------------------------------------------------------
-- 命題1.5.13
--
-- 連結な groupoid は、その任意の対象の自己同型群と（1対象圏とみなして）同値。
-- SingleObj M は本の BM（対象が1つで自己射のモノイドが M である圏）、
-- vertexGroup は groupoid の自己射 G(g,g) に群構造を与える。どちらも
-- Category / Group インスタンスの証明を伴うので Recap には写さない
-- ---------------------------------------------------------------------------

#check @CategoryTheory.SingleObj
#check @CategoryTheory.Groupoid.vertexGroup

-- 命題1.5.13
-- Mathlib に対応物なし
example (G : Type u₁) [Groupoid.{v₁} G] [IsConnected G] (g : G) :
    Nonempty (G ≌ SingleObj (g ⟶ g)) :=
  sorry

-- ---------------------------------------------------------------------------
-- 系1.5.14
--
-- 弧状連結空間では、基本群は基点の取り方によらず同型。命題1.5.13 を基本亜群に
-- 適用して得られる
-- ---------------------------------------------------------------------------

example (X : Type u₁) [TopologicalSpace X] [PathConnectedSpace X] (x y : X) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup X y) :=
  sorry

#check @FundamentalGroup.fundamentalGroupMulEquivOfPathConnected

-- ---------------------------------------------------------------------------
-- 定義1.5.16
--
-- 圏が skeletal とは、各同型類にちょうど1つずつ対象を持つこと。C の骨格 skC は
-- C と同値な skeletal 圏で、同型を除いて一意に定まる。Mathlib では Skeleton C
-- として構成され、skeleton_isSkeleton がその2条件を与える
-- ---------------------------------------------------------------------------

#check @CategoryTheory.Skeletal
#check @CategoryTheory.Skeleton
#check @CategoryTheory.IsSkeletonOf
#check @CategoryTheory.skeleton_isSkeleton

-- ---------------------------------------------------------------------------
-- 節末問題
-- ---------------------------------------------------------------------------

-- 演習1.5.i は補題1.5.1 の証明そのものなので、上の補題1.5.1 の example を解く

-- 演習1.5.ii
-- Segal の圏 Γ（対象は有限集合、S から T への射は θ : S → P(T) であって α ≠ β
-- なら θ(α) と θ(β) が交わらないもの、合成は ψ(α) = ⋃_{β ∈ θ(α)} φ(β)）が
-- 有限点付き集合の圏の反対圏 Fin_*^op と同値であることを示す問題。
-- Γ と Fin_* の双方を圏として自前で組む必要があり、1.5 の主題から離れるため
-- 問題文のみを残す。Mathlib に対応物なし（Segal の Γ も Fin_* も Mathlib には
-- 圏として用意されていない）

-- 演習1.5.iii（補題1.5.10 の4つの図式が互いに同値であること）
example {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') (u : a ≅ a') (v : b ≅ b') :
    List.TFAE
      [u.hom ≫ f' = f ≫ v.hom,
       f' ≫ v.inv = u.inv ≫ f,
       u.hom ≫ f' ≫ v.inv = f,
       u.inv ≫ f ≫ v.hom = f'] :=
  sorry

#check @CategoryTheory.Iso.inv_comp_eq
#check @CategoryTheory.Iso.eq_inv_comp
#check @CategoryTheory.Iso.comp_inv_eq
#check @CategoryTheory.Iso.eq_comp_inv

-- 演習1.5.iv・1.5.v で使う「同型を create する」。Mathlib の
-- Functor.ReflectsIsomorphisms は (i) の reflect にあたるもので、
-- 対象についての create にあたるクラスは Mathlib にないので自前で置く
def myCreatesIsomorphisms (F : C ⥤ D) : Prop :=
  ∀ x y : C, Nonempty (F.obj x ≅ F.obj y) → Nonempty (x ≅ y)

-- 演習1.5.iv(i)：full かつ faithful な関手は同型を reflect する
example (F : C ⥤ D) [F.Full] [F.Faithful] {x y : C} (f : x ⟶ y) [IsIso (F.map f)] :
    IsIso f :=
  sorry

#check @CategoryTheory.isIso_of_fully_faithful

-- 演習1.5.iv(ii)：full かつ faithful な関手は同型を create する
example (F : C ⥤ D) [F.Full] [F.Faithful] : myCreatesIsomorphisms F :=
  sorry

#check @CategoryTheory.Functor.preimageIso

-- 演習1.5.v は反例の構成を問う問題なので、以下の4つとも Mathlib に対応物なし

-- 演習1.5.v のうち、full だが faithful でない関手で同型を reflect しないもの
example : ∃ (C : Type) (_ : SmallCategory C) (D : Type) (_ : SmallCategory D)
    (F : C ⥤ D), F.Full ∧ ¬ F.Faithful ∧ ¬ F.ReflectsIsomorphisms :=
  sorry

-- 演習1.5.v のうち、full だが faithful でない関手で同型を create しないもの
example : ∃ (C : Type) (_ : SmallCategory C) (D : Type) (_ : SmallCategory D)
    (F : C ⥤ D), F.Full ∧ ¬ F.Faithful ∧ ¬ myCreatesIsomorphisms F :=
  sorry

-- 演習1.5.v のうち、faithful だが full でない関手で同型を reflect しないもの
example : ∃ (C : Type) (_ : SmallCategory C) (D : Type) (_ : SmallCategory D)
    (F : C ⥤ D), F.Faithful ∧ ¬ F.Full ∧ ¬ F.ReflectsIsomorphisms :=
  sorry

-- 演習1.5.v のうち、faithful だが full でない関手で同型を create しないもの
example : ∃ (C : Type) (_ : SmallCategory C) (D : Type) (_ : SmallCategory D)
    (F : C ⥤ D), F.Faithful ∧ ¬ F.Full ∧ ¬ myCreatesIsomorphisms F :=
  sorry

-- 演習1.5.vi(i) のうち full の合成
example (F : C ⥤ D) (G : D ⥤ E) [F.Full] [G.Full] : (F ⋙ G).Full :=
  sorry

#check @CategoryTheory.Functor.Full.comp

-- 演習1.5.vi(i) のうち faithful の合成
example (F : C ⥤ D) (G : D ⥤ E) [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful :=
  sorry

#check @CategoryTheory.Functor.Faithful.comp

-- 演習1.5.vi(i) のうち essentially surjective の合成
example (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] : (F ⋙ G).EssSurj :=
  sorry

#check @CategoryTheory.Functor.essSurj_comp

-- 演習1.5.vi(ii) は補題1.5.5 の推移律なので、上の MyEquivalence.trans を解く

-- 演習1.5.vii：discrete 圏と同値な圏の特徴づけ。
-- 「すべての射が同型で、かつ平行な射がつねに等しい」と言い換えて述べる。
-- Discrete α の射は α と同じ宇宙に住むので、対象と射の宇宙を揃えてある
-- Mathlib に対応物なし
example {A : Type u₁} [Category.{u₁} A] :
    (∃ α : Type u₁, Nonempty (A ≌ Discrete α)) ↔
      ((∀ (x y : A) (f : x ⟶ y), IsIso f) ∧ ∀ (x y : A) (f g : x ⟶ y), f = g) :=
  sorry

#check @CategoryTheory.Discrete

-- 演習1.5.viii
-- アフィン平面の groupoid Affine が、無限遠直線を指定した射影平面の groupoid
-- Proj| と同値であることを示し、逆向きの同値を明示せよという問題。
-- 射はいずれも点と直線の全単射で接続関係を保ち反射するもの。入射幾何の対象を
-- 圏として組むところから始めることになるため問題文のみを残す。
-- Mathlib に対応物なし（Affine も Proj| も圏としては用意されていない）

-- 演習1.5.ix
-- 以下の関手のうちどれが full か、どれが faithful か、どれが essentially
-- surjective か、そして圏同値を定めるものがあるかを判定する問題。
-- 判定結果そのものが答えなので statement は置かず、対象の関手だけを挙げる

-- I : Ab → Group。本の Ab は加法的なアーベル群の圏だが、Mathlib で GrpCat への
-- 忘却関手が用意されているのは乗法的な CommGrpCat からのもの
#check CategoryTheory.forget₂ CommGrpCat GrpCat

-- I : Ring → Ab（乗法を忘れる）
#check CategoryTheory.forget₂ RingCat AddCommGrpCat

-- (−)ˣ : Ring → Group。Mathlib にあるのはモノイドの単元群を取る関手で、
-- Ring からはこれに忘却関手を合成して得る
#check MonCat.units

-- U : R Mod → Ab
#check fun (R : Type) [Ring R] => CategoryTheory.forget₂ (ModuleCat R) AddCommGrpCat

-- I : Ring → Rng と I : Field → Ring は Mathlib に対応物なし
-- （単位元を持たない環の圏 Rng も、体の圏 Field も Mathlib にはない）

end Riehl
