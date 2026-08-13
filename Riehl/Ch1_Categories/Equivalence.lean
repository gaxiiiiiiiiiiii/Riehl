import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

-- ----------------------------------------------------------------------------
-- 1.5 圏同値
--
-- 圏の「同じさ」を圏同型より緩く捉える節。自然同型 η : 1_C ≅ GF と ε : FG ≅ 1_D をもつ
-- 関手の組として圏同値を定め、圏同値をなす関手を「充満・忠実・本質的全射」で特徴づける
-- （定理1.5.9）。後半は骨格と、圏論的な概念が同値で不変であることの確認。
--
-- 後続節の前提: 1.7（演習1.7.v で推移律を組み直す）、2.4・3章（同値不変性）、
-- 4.3（三角等式を課した随伴同値。本節の定義と Mathlib の定義の差はそこで回収する）。
--
-- 参照した Mathlib のファイル:
--   Mathlib/CategoryTheory/Equivalence.lean
--   Mathlib/CategoryTheory/EssentialImage.lean
--   Mathlib/CategoryTheory/Functor/FullyFaithful.lean
--   Mathlib/CategoryTheory/HomCongr.lean
--   Mathlib/CategoryTheory/IsConnected.lean
--   Mathlib/CategoryTheory/SingleObj.lean
--   Mathlib/CategoryTheory/Skeletal.lean
--   Mathlib/CategoryTheory/IsomorphismClasses.lean
--   Mathlib/CategoryTheory/Groupoid.lean
--   Mathlib/CategoryTheory/Opposites.lean
--   Mathlib/CategoryTheory/Products/Basic.lean
--   Mathlib/CategoryTheory/Endomorphism.lean
--   Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean
-- ----------------------------------------------------------------------------

-- Mathlib のヘッダリンタは著作権ブロックとモジュール docstring を要求するので、
-- 行コメントで書くこのファイルとは噛み合わない。切っておく
set_option linter.style.header false

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Riehl

open CategoryTheory

-- ----------------------------------------------------------------------------
-- Recap
-- 本節の演習は Mathlib 側の定義で書いてあるので、中身を見ないと手が出ないものだけ写す。
-- ----------------------------------------------------------------------------

namespace Recap

-- CategoryTheory.Functor.essImage
-- Mathlib の EssSurj は「本質的像が全対象を覆う」という形で述べられている
def essImage {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) : D → Prop := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

-- CategoryTheory.IsIsomorphic
-- Mathlib の Skeletal はこれを使って述べられている
def IsIsomorphic {C : Type u₁} [Category.{v₁} C] : C → C → Prop := fun X Y => Nonempty (X ≅ Y)

-- CategoryTheory.Zag / CategoryTheory.Zigzag
def Zag {J : Type u₁} [Category.{v₁} J] (j₁ j₂ : J) : Prop :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

def Zigzag {J : Type u₁} [Category.{v₁} J] : J → J → Prop := Relation.ReflTransGen Zag

-- CategoryTheory.IsPreconnected / CategoryTheory.IsConnected
-- Mathlib の連結性は「離散圏へのどの関手も定数」という形で、本の「ジグザグで結べる」とは
-- 見た目が違う。空圏を連結と認めない点も本とずれる
class IsPreconnected (J : Type u₁) [Category.{v₁} J] : Prop where
  iso_constant : ∀ {α : Type u₁} (F : J ⥤ Discrete α) (j : J),
    Nonempty (F ≅ (Functor.const J).obj (F.obj j))

class IsConnected (J : Type u₁) [Category.{v₁} J] : Prop extends IsPreconnected J where
  [is_nonempty : Nonempty J]

-- CategoryTheory.SingleObj: モノイド M を1対象の圏とみなしたもの。合成は積の逆順
def SingleObj (_M : Type u₁) : Type := PUnit

instance {M : Type u₁} [One M] [Mul M] : CategoryStruct (SingleObj M) where
  Hom _ _ := M
  comp x y := y * x
  id _ := 1

-- CategoryTheory.Aut: 対象の自己同型のなす群。積は f * g = g ≪≫ f で、合成とは逆順
def Aut {C : Type u₁} [Category.{v₁} C] (X : C) := X ≅ X

end Recap

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

-- ----------------------------------------------------------------------------
-- 補題1.5.1
-- ----------------------------------------------------------------------------

-- 補題1.5.1: 自然変換 α : F ⇒ G は、i₀ と i₁ に沿った制限が F と G になる関手
-- H : C × 2 → D と1対1に対応する。歩く矢圏 2 は前順序 Fin 2 の圏で取った。
-- 図式 (1.5.2) の可換性は Lean では関手どうしの等式になる
-- Mathlib に対応物なし
example (F G : C ⥤ D) :
    (F ⟶ G) ≃
      { H : C × Fin 2 ⥤ D //
        (𝟭 C).prod' ((Functor.const C).obj (0 : Fin 2)) ⋙ H = F ∧
        (𝟭 C).prod' ((Functor.const C).obj (1 : Fin 2)) ⋙ H = G } :=
  sorry

-- ----------------------------------------------------------------------------
-- 定義1.5.4
-- ----------------------------------------------------------------------------

-- 定義1.5.4: 圏同値は関手 F : C ⇄ D : G と自然同型 η : 1_C ≅ GF, ε : FG ≅ 1_D の組。
-- Mathlib の CategoryTheory.Equivalence は三角等式 F η ≫ ε F = 1 を追加で課した
-- 半随伴同値なので、本の定義よりデータが多い。この差は 4.3（命題4.3.5）で回収する
structure MyEquivalence (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] where
  functor : C ⥤ D
  inverse : D ⥤ C
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  counitIso : inverse ⋙ functor ≅ 𝟭 D

-- 定義1.5.4 の後半: 関手 F が圏同値をなすとは、F を前向きの関手とする圏同値があること
def MyDefinesEquivalence (F : C ⥤ D) : Prop := ∃ e : MyEquivalence C D, e.functor = F

-- ----------------------------------------------------------------------------
-- 補題1.5.5（証明は演習1.5.vi(ii)）
-- ----------------------------------------------------------------------------

-- 補題1.5.5 の反射律
#check CategoryTheory.Equivalence.refl
def MyEquivalence.refl (C : Type u₁) [Category.{v₁} C] : MyEquivalence C C := sorry

-- 補題1.5.5 の対称律
#check CategoryTheory.Equivalence.symm
def MyEquivalence.symm (e : MyEquivalence C D) : MyEquivalence D C := sorry

-- 補題1.5.5 の推移律。演習1.7.v で、この定義に依らない形の再証明を置く
#check CategoryTheory.Equivalence.trans
def MyEquivalence.trans (e : MyEquivalence C D) (f : MyEquivalence D E) : MyEquivalence C E := sorry

-- ----------------------------------------------------------------------------
-- 定義1.5.7・注意1.5.8
-- ----------------------------------------------------------------------------

-- 定義1.5.7 の充満性: hom 集合の間に誘導される写像が全射（Mathlib では Functor.Full）
def myFull (F : C ⥤ D) : Prop :=
  ∀ x y : C, Function.Surjective (F.map : (x ⟶ y) → (F.obj x ⟶ F.obj y))

-- 定義1.5.7 の忠実性: hom 集合の間に誘導される写像が単射（Mathlib では Functor.Faithful）
def myFaithful (F : C ⥤ D) : Prop :=
  ∀ x y : C, Function.Injective (F.map : (x ⟶ y) → (F.obj x ⟶ F.obj y))

-- 定義1.5.7 の本質的全射性: 行き先の各対象が像の対象と同型（Mathlib では Functor.EssSurj）
def myEssSurj (F : C ⥤ D) : Prop := ∀ d : D, ∃ c : C, Nonempty (F.obj c ≅ d)

-- 注意1.5.8: 充満性・忠実性は hom 集合ごとの局所的な条件で、射全体の上での全射性・単射性
-- ではない。忠実かつ対象上単射な関手が埋め込み、充満忠実で対象上単射なものが充満埋め込み、
-- その像が充満部分圏（Mathlib では ObjectProperty.FullSubcategory）にあたる

-- ----------------------------------------------------------------------------
-- 定理1.5.9
-- ----------------------------------------------------------------------------

-- 定理1.5.9 の順方向のうち充満性
#check CategoryTheory.Functor.IsEquivalence.full
example (e : MyEquivalence C D) : e.functor.Full := sorry

-- 定理1.5.9 の順方向のうち忠実性
#check CategoryTheory.Functor.IsEquivalence.faithful
example (e : MyEquivalence C D) : e.functor.Faithful := sorry

-- 定理1.5.9 の順方向のうち本質的全射性
#check CategoryTheory.Functor.IsEquivalence.essSurj
example (e : MyEquivalence C D) : e.functor.EssSurj := sorry

-- 定理1.5.9 の逆方向。選択公理を使う
#check CategoryTheory.Functor.asEquivalence
example (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] : MyDefinesEquivalence F := sorry

-- ----------------------------------------------------------------------------
-- 補題1.5.10（四つの図式が同値であることは演習1.5.iii）
-- ----------------------------------------------------------------------------

-- 補題1.5.10: 射 f : a → b と同型 u : a ≅ a', v : b ≅ b' に対し、四角形を可換にする
-- f' : a' → b' がただ一つ定まる
#check CategoryTheory.Iso.homCongr
theorem lemma_1_5_10 {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') :
    ∃! f' : a' ⟶ b', u.hom ≫ f' = f ≫ v.hom := sorry

-- ----------------------------------------------------------------------------
-- 命題1.5.13・系1.5.14
-- ----------------------------------------------------------------------------

-- 連結性（節中で番号なしに導入される）: 任意の2対象が射の有限なジグザグで結べること
def myConnected (C : Type u₁) [Category.{v₁} C] : Prop :=
  ∀ X Y : C, Relation.ReflTransGen (fun A B : C => Nonempty (A ⟶ B) ∨ Nonempty (B ⟶ A)) X Y

-- 命題1.5.13: 連結な亜群は、その任意の対象の自己同型群を1対象の圏とみたものと同値
-- Mathlib に対応物なし
example (G : Type u₃) [Groupoid.{v₃} G] [IsConnected G] (g : G) :
    MyEquivalence (SingleObj (Aut g)) G := sorry

-- 系1.5.14: 弧状連結な空間では、基点の取り方によらず基本群が同型になる
#check FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
example (X : Type u₁) [TopologicalSpace X] [PathConnectedSpace X] (x y : X) :
    FundamentalGroup X x ≃* FundamentalGroup X y := sorry

-- ----------------------------------------------------------------------------
-- 定義1.5.16・注意1.5.17
-- ----------------------------------------------------------------------------

-- 定義1.5.16: 骨格的とは、同型類ごとに対象がちょうど一つしかないこと（Mathlib では
-- Skeletal）。骨格 skC のほうは Mathlib では CategoryTheory.Skeleton として構成される
def mySkeletal (C : Type u₁) [Category.{v₁} C] : Prop := ∀ X Y : C, Nonempty (X ≅ Y) → X = Y

-- 注意1.5.17: 骨格的な圏どうしの同値は圏同型になる。Mathlib には「圏の同型」を束ねた
-- 定義がないので、前向きの関手が対象上全単射であることとして述べる
-- Mathlib に対応物なし
example (hC : Skeletal C) (hD : Skeletal D) (e : MyEquivalence C D) :
    Function.Bijective e.functor.obj := sorry

-- 注意1.5.17 の「二つの圏が同値 ⟺ 骨格が同型」のうち、対象の水準に落とした向き
#check CategoryTheory.Equivalence.skeletonEquiv
example (e : MyEquivalence C D) : Nonempty (Skeleton C ≃ Skeleton D) := sorry

-- ----------------------------------------------------------------------------
-- 同値不変性（節末、番号なし）
-- ----------------------------------------------------------------------------

-- 射が同型であること・対象が同型であることが同値のもとで保たれ、かつ反映されることは、
-- 演習1.5.iv に含まれる

-- 局所小性が同値で保たれること: 小ささの語彙と Mathlib の universe / Small 系クラスとの
-- 対応づけは 3.7 でまとめて行うので、ここでは statement を置かない

-- 亜群であることが同値で保たれる
-- Mathlib に対応物なし
example (e : MyEquivalence C D) [IsGroupoid C] : IsGroupoid D := sorry

-- C ≃ D ならば Cᵒᵖ ≃ Dᵒᵖ
#check CategoryTheory.Equivalence.op
example (e : MyEquivalence C D) : MyEquivalence Cᵒᵖ Dᵒᵖ := sorry

-- 積圏は、同値な圏の組の積と同値
#check CategoryTheory.Equivalence.prod
example {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
    (e : MyEquivalence C D) (e' : MyEquivalence C' D') :
    MyEquivalence (C × C') (D × D') := sorry

-- 節の最後に出る「本質的に小さい」は Mathlib の EssentiallySmall にあたり 3.7 で扱う。
-- 「本質的に離散」は演習1.5.vii の主題

-- ----------------------------------------------------------------------------
-- 節末問題
-- ----------------------------------------------------------------------------

-- 演習1.5.i: 補題1.5.1 を証明せよ。statement は上の補題1.5.1

-- 演習1.5.ii: Segal の圏 Γ（対象は有限集合、S から T への射は θ : S → P(T) であって
-- α ≠ β なら θ(α) と θ(β) が交わらないもの、合成は ψ(α) = ⋃_{β ∈ θ(α)} φ(β)）が、
-- 有限点付き集合の圏の反対圏 Fin∗ᵒᵖ と同値であることを示せ。
-- Mathlib には Γ も Fin∗ もなく、両方の圏を組むところから始まるので statement は置かない

-- 演習1.5.iii: 補題1.5.10 の四つの図式が同値であること。f : a → b, f' : a' → b',
-- u : a ≅ a', v : b ≅ b' に対し
--   (1) u.hom ≫ f' = f ≫ v.hom      (2) f' = u.inv ≫ f ≫ v.hom
--   (3) f = u.hom ≫ f' ≫ v.inv      (4) u.inv ≫ f = f' ≫ v.inv

-- 演習1.5.iii の (1) ⟺ (2)
#check CategoryTheory.Iso.eq_inv_comp
example {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') (u : a ≅ a') (v : b ≅ b') :
    u.hom ≫ f' = f ≫ v.hom ↔ f' = u.inv ≫ f ≫ v.hom := sorry

-- 演習1.5.iii の (1) ⟺ (3)
#check CategoryTheory.Iso.eq_comp_inv
example {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') (u : a ≅ a') (v : b ≅ b') :
    u.hom ≫ f' = f ≫ v.hom ↔ f = u.hom ≫ f' ≫ v.inv := sorry

-- 演習1.5.iii の (1) ⟺ (4)
#check CategoryTheory.Iso.inv_comp_eq
example {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') (u : a ≅ a') (v : b ≅ b') :
    u.hom ≫ f' = f ≫ v.hom ↔ u.inv ≫ f = f' ≫ v.inv := sorry

-- 演習1.5.iv(i): 充満忠実な関手は同型を反映する
#check CategoryTheory.isIso_of_fully_faithful
example (F : C ⥤ D) [F.Full] [F.Faithful] {x y : C} (f : x ⟶ y) (hf : IsIso (F.map f)) :
    IsIso f := sorry

-- 演習1.5.iv(ii): 充満忠実な関手は同型を生成する
#check CategoryTheory.Functor.preimageIso
example (F : C ⥤ D) [F.Full] [F.Faithful] (x y : C) (h : Nonempty (F.obj x ≅ F.obj y)) :
    Nonempty (x ≅ y) := sorry

-- 演習1.5.v: 充満だが忠実でない関手、忠実だが充満でない関手であって、同型を反映も生成も
-- しないものの例を挙げよ。反例を探す問題なので statement は置かない

-- 演習1.5.vi(i): 充満な関手の合成は充満
#check CategoryTheory.Functor.Full.comp
example (F : C ⥤ D) (G : D ⥤ E) [F.Full] [G.Full] : (F ⋙ G).Full := sorry

-- 演習1.5.vi(i): 忠実な関手の合成は忠実
#check CategoryTheory.Functor.Faithful.comp
example (F : C ⥤ D) (G : D ⥤ E) [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful := sorry

-- 演習1.5.vi(i): 本質的全射な関手の合成は本質的全射
#check CategoryTheory.Functor.essSurj_comp
example (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] : (F ⋙ G).EssSurj := sorry

-- 演習1.5.vi(ii): 圏同値の推移律。statement は上の MyEquivalence.trans

-- 演習1.5.vii: 離散圏と同値になる圏を特徴づけよ。何を特徴づけとして立てるかが問題の中身
-- なので statement は置かない

-- 演習1.5.viii: アフィン平面の亜群 Affine が、無限遠直線を指定した射影平面の亜群 Proj|
-- と同値であることを示し、逆向きの同値を具体的に書け。射は点と直線の両方の上の全単射で
-- 接続関係を保ち反映するもの。Mathlib には Affine も Proj| もないので statement は置かない

-- 演習1.5.ix: I : Ab → Group, I : Ring → Ab（乗法を忘れる）, (−)× : Ring → Group,
-- I : Ring → Rng, I : Field → Ring, U : R-Mod → Ab のそれぞれについて、充満・忠実・
-- 本質的全射のどれが成り立つか、圏同値をなすものがあるかを判定せよ。
-- 研究水準の問いを含むと本文が注意しているので statement は置かない

end Riehl
