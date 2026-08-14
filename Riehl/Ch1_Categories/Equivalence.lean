import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Category.PartialFun
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Skeletal
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Data.List.TFAE

-- ============================================================================
-- Riehl, Category Theory in Context, 1.5 Equivalence of categories
--
-- 自然変換をシリンダー C × 2 ⥤ D として捉え直す補題1.5.1 から始め、圏同値
-- （定義1.5.4）、充満・忠実・本質的全射（定義1.5.7）、その3条件による圏同値の
-- 特徴づけ（定理1.5.9）、鍵になる補題1.5.10、骨格（定義1.5.16）を扱う。
--
-- 本の圏同値は F, G, η, ε のみで三角等式を課さない。Mathlib の Equivalence との
-- 差は 4.3（命題4.3.5, Equivalence.adjointifyη）で回収する。MyEquivalence.trans は
-- 演習1.7.v が自己完結形で再演する（脚注43）。essentially small の語彙は 3.7 で扱う。
--
-- 参照した Mathlib:
--   Mathlib/CategoryTheory/Equivalence.lean       -- Equivalence, Functor.IsEquivalence
--   Mathlib/CategoryTheory/Functor/FullyFaithful.lean -- Functor.Full, Functor.Faithful
--   Mathlib/CategoryTheory/EssentialImage.lean    -- Functor.EssSurj, Functor.essImage
--   Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean -- ReflectsIsomorphisms
--   Mathlib/CategoryTheory/HomCongr.lean          -- Iso.homCongr
--   Mathlib/CategoryTheory/Products/Basic.lean    -- 積圏、Prod.sectL
--   Mathlib/CategoryTheory/Category/Preorder.lean -- Preorder.smallCategory, homOfLE
--   Mathlib/CategoryTheory/Category/PartialFun.lean -- partialFunEquivPointed
--   Mathlib/CategoryTheory/IsConnected.lean       -- Zag, Zigzag
--   Mathlib/CategoryTheory/Groupoid.lean          -- Groupoid
--   Mathlib/CategoryTheory/SingleObj.lean         -- SingleObj（本の BG）
--   Mathlib/CategoryTheory/Endomorphism.lean      -- Aut
--   Mathlib/CategoryTheory/Skeletal.lean          -- Skeletal, Skeleton, skeletonEquivalence
--   Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean -- FundamentalGroup
--   Mathlib/Data/List/TFAE.lean                   -- List.TFAE
-- ============================================================================

namespace Riehl

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

-- ----------------------------------------------------------------------------
-- Recap
-- 演習の足場になる Mathlib 定義の写し。実際の演習では Mathlib のものを使う
-- ----------------------------------------------------------------------------

namespace Recap

-- Mathlib/CategoryTheory/Iso.lean より（autoparam は省略）。定義1.5.4 の η, ε は
-- 関手圏における Iso
structure Iso {C : Type u₁} [Category.{v₁} C] (X Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X
  inv_hom_id : inv ≫ hom = 𝟙 Y

-- Mathlib/CategoryTheory/Iso.lean より。逆射の存在だけを主張する Prop 版。演習1.5.iv で使う
class IsIso {C : Type u₁} [Category.{v₁} C] {X Y : C} (f : X ⟶ Y) : Prop where
  out : ∃ inv : Y ⟶ X, f ≫ inv = 𝟙 X ∧ inv ≫ f = 𝟙 Y

-- Mathlib/CategoryTheory/Products/Basic.lean より。対象 Z を固定した積圏への切断。
-- 補題1.5.1 の i₀, i₁ は sectL C 0, sectL C 1
def Prod.sectL (C : Type u₁) [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (Z : D) :
    C ⥤ C × D where
  obj X := (X, Z)
  map f := (f, 𝟙 Z)

-- Mathlib/CategoryTheory/IsConnected.lean より。命題1.5.13 の「連結」は
-- Zag（どちらか向きの射がある）の反射推移閉包 Zigzag で述べる
def Zag {J : Type u₁} [Category.{v₁} J] (j₁ j₂ : J) : Prop :=
  Nonempty (j₁ ⟶ j₂) ∨ Nonempty (j₂ ⟶ j₁)

def Zigzag {J : Type u₁} [Category.{v₁} J] : J → J → Prop :=
  Relation.ReflTransGen Zag

-- Mathlib/CategoryTheory/SingleObj.lean より。1点型に M を hom として圏構造を入れる。
-- 本の BG に相当し、M が群なら亜群になる
def SingleObj (_ : Type u₁) : Type := Unit

-- Mathlib/CategoryTheory/Endomorphism.lean より。対象 X の自己同型群（群構造は Aut.group）
def Aut {C : Type u₁} [Category.{v₁} C] (X : C) := X ≅ X

end Recap

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

-- ----------------------------------------------------------------------------
-- 補題1.5.1 — 自然変換のシリンダー表示
-- 歩く矢印 2 は Fin 2 に Preorder.smallCategory で入る圏（0 ⟶ 1 は homOfLE）
-- ----------------------------------------------------------------------------

-- 補題1.5.1 — α : F ⇒ G と、i₀, i₁ に沿って F, G に制限する関手 H : C × 2 ⥤ D は
-- 1対1に対応する。全単射の構成が演習1.5.i。Mathlib に対応物なし
def myNatTransEquivCylinder (F G : C ⥤ D) :
    (F ⟶ G) ≃ { H : C × Fin 2 ⥤ D //
      Prod.sectL C (0 : Fin 2) ⋙ H = F ∧ Prod.sectL C (1 : Fin 2) ⋙ H = G } := sorry

-- 2 を「歩く同型」I に置き換えると同じ対応が自然同型を与える、という本文の注意が
-- 定義1.5.4 の動機（圏同値 = I をシリンダーとするホモトピー同値）

-- ----------------------------------------------------------------------------
-- 定義1.5.4 — 圏同値
-- ----------------------------------------------------------------------------

section
variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

-- 定義1.5.4 — 本の圏同値は F, G, η : id_C ≅ GF, ε : FG ≅ id_D の4つ組で、三角等式を
-- 課さない。Mathlib の Equivalence はさらに functor_unitIso_comp（三角等式）を要求する。
-- この差は 4.3 の命題4.3.5（Equivalence.adjointifyη の再現）で回収する。
-- 本の GF は合成の向きが逆の Mathlib では F ⋙ G と書く
#check CategoryTheory.Equivalence
structure MyEquivalence where
  F : C ⥤ D
  G : D ⥤ C
  η : 𝟭 C ≅ F ⋙ G
  ε : G ⋙ F ≅ 𝟭 D

-- 定義1.5.4 — 圏 C と D が同値であること（本の C ≃ D）
def MyEquivalent : Prop := Nonempty (MyEquivalence C D)

end

-- 定義1.5.4 — 関手 F が圏同値を定めること（圏同値の F 成分に拡張できること）
#check CategoryTheory.Functor.IsEquivalence
def myDefinesEquivalence (F : C ⥤ D) : Prop := ∃ e : MyEquivalence C D, e.F = F

-- ----------------------------------------------------------------------------
-- 補題1.5.5 — 圏同値は同値関係をなす
-- 以下の3構成が反射律・対称律・推移律。証明（構成）は演習1.5.vi(ii)
-- ----------------------------------------------------------------------------

-- 反射律。恒等関手と恒等自然同型でよい
#check CategoryTheory.Equivalence.refl
def MyEquivalence.refl : MyEquivalence C C := sorry

-- 対称律。η と ε の役割を入れ替える。Mathlib 版は三角等式の付け替えも必要になる
#check CategoryTheory.Equivalence.symm
def MyEquivalence.symm (e : MyEquivalence C D) : MyEquivalence D C := sorry

-- 推移律。演習1.7.v が同じ主張を F, G, η, ε に展開した自己完結形で再演する（脚注43）
#check CategoryTheory.Equivalence.trans
def MyEquivalence.trans (e : MyEquivalence C D) (e' : MyEquivalence D E) :
    MyEquivalence C E := sorry

-- 例1.5.6 — 点つき集合の圏 Set∗ と、集合と部分関数の圏 Set∂ の同値。
-- Mathlib では PartialFun ≌ Pointed として構成済み
#check partialFunEquivPointed

-- ----------------------------------------------------------------------------
-- 定義1.5.7 — 充満・忠実・本質的全射
-- ----------------------------------------------------------------------------

-- 定義1.5.7 — 充満:各 hom 集合上で f ↦ F.map f が全射。Mathlib は Prop 値クラス
#check CategoryTheory.Functor.Full
def myFull (F : C ⥤ D) : Prop :=
  ∀ ⦃x y : C⦄, Function.Surjective (F.map : (x ⟶ y) → (F.obj x ⟶ F.obj y))

-- 定義1.5.7 — 忠実:各 hom 集合上で f ↦ F.map f が単射
#check CategoryTheory.Functor.Faithful
def myFaithful (F : C ⥤ D) : Prop :=
  ∀ ⦃x y : C⦄, Function.Injective (F.map : (x ⟶ y) → (F.obj x ⟶ F.obj y))

-- 定義1.5.7 — 本質的全射:各 d ∈ D がある Fc と同型。Mathlib は essImage で述べる
#check CategoryTheory.Functor.EssSurj
def myEssSurj (F : C ⥤ D) : Prop := ∀ d : D, ∃ c : C, Nonempty (F.obj c ≅ d)

-- 注意1.5.8 — 充満・忠実は hom ごとの局所条件で、射の上の大域的な全射・単射とは別物。
-- 対象単射な忠実関手が embedding、さらに充満なら full embedding（充満部分圏を定める）。
-- Mathlib は充満かつ忠実のデータ版 Functor.FullyFaithful も持つ
#check CategoryTheory.Functor.FullyFaithful

-- ----------------------------------------------------------------------------
-- 定理1.5.9 — 圏同値の特徴づけ
-- ----------------------------------------------------------------------------

-- 定理1.5.9（順方向） — 圏同値をなす関手は充満
#check CategoryTheory.Equivalence.full_functor
example (e : MyEquivalence C D) : myFull e.F := sorry

-- 定理1.5.9（順方向） — 圏同値をなす関手は忠実
#check CategoryTheory.Equivalence.faithful_functor
example (e : MyEquivalence C D) : myFaithful e.F := sorry

-- 定理1.5.9（順方向） — 圏同値をなす関手は本質的全射
#check CategoryTheory.Equivalence.essSurj_functor
example (e : MyEquivalence C D) : myEssSurj e.F := sorry

-- 定理1.5.9（逆方向） — 3条件を満たす関手は圏同値を定める。G の構成に選択公理を使う。
-- Mathlib は IsEquivalence をこの3条件で「定義」し、同値データの構成が asEquivalence
#check CategoryTheory.Functor.asEquivalence
example (F : C ⥤ D) (h₁ : myFull F) (h₂ : myFaithful F) (h₃ : myEssSurj F) :
    myDefinesEquivalence F := sorry

-- ----------------------------------------------------------------------------
-- 補題1.5.10 — 同型で移した射の一意な対応
-- ----------------------------------------------------------------------------

-- 補題1.5.10 — f : a ⟶ b と同型 u : a ≅ a', v : b ≅ b' は、四角を可換にする
-- f' : a' ⟶ b' を一意に定める。Mathlib は対応 f ↦ u.inv ≫ f ≫ v.hom を Equiv として持つ
#check CategoryTheory.Iso.homCongr
example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') :
    ∃! f' : a' ⟶ b', u.hom ≫ f' = f ≫ v.hom := sorry

-- 補題1.5.10 — 「どれか1つが可換なら4つすべて可換」。4条件の同値。証明は演習1.5.iii
#check CategoryTheory.Iso.homCongr
example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') (f' : a' ⟶ b') :
    List.TFAE [f' = u.inv ≫ f ≫ v.hom,
      u.hom ≫ f' = f ≫ v.hom,
      f' ≫ v.inv = u.inv ≫ f,
      u.hom ≫ f' ≫ v.inv = f] := sorry

-- 例1.5.11 — 充満忠実関手は essential image（Fc と同型な対象のなす充満部分圏）への
-- 圏同値を定める。Mathlib では toEssImage と fullyFaithfulToEssImage
#check CategoryTheory.Functor.essImage
#check CategoryTheory.Functor.toEssImage

-- 例1.5.12 — 行列の圏 Mat_k と有限次元ベクトル空間の圏 Vect^fd_k の同値。基底つき
-- ベクトル空間の圏を経由し、定理1.5.9 か直接構成で示される。Mathlib に直接の対応物なし

-- ----------------------------------------------------------------------------
-- 命題1.5.13 — 連結亜群と自己同型群
-- ----------------------------------------------------------------------------

-- 命題1.5.13 — 連結（任意の2対象が有限 zig-zag で結べる）亜群は、任意の対象の
-- 自己同型群を1対象圏とみたもの（本の BG = Mathlib の SingleObj）と圏同値。
-- Mathlib に対応物なし（関連: CategoryTheory.Groupoid.vertexGroup）
example {G : Type u₁} [Groupoid G] (conn : ∀ x y : G, Zigzag x y) (g : G) :
    MyEquivalent (SingleObj (Aut g)) G := sorry

-- 系1.5.14 — 弧状連結空間では基点のとり方によらず基本群が同型。本は命題1.5.13 を
-- 基本亜群 Π₁X に適用して示す。ここでは結論を群同型の存在として述べる
#check FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
example {X : Type u₁} [TopologicalSpace X] [PathConnectedSpace X] (x y : X) :
    Nonempty (FundamentalGroup X x ≃* FundamentalGroup X y) := sorry

-- 注意1.5.15 — 圏同値の片方向は標準的に定義できても、逆向きは選択公理頼みで自然性を
-- 失うことがある（Π₁X → π₁(X, x) は各点から基点への道の選択が要る）。statement は置かない

-- ----------------------------------------------------------------------------
-- 定義1.5.16 — 骨格
-- ----------------------------------------------------------------------------

section
variable (C : Type u₁) [Category.{v₁} C]

-- 定義1.5.16 — 骨格的:各同型類に対象がちょうど1つ。Mathlib の IsIsomorphic X Y は
-- Nonempty (X ≅ Y) の別名
#check CategoryTheory.Skeletal
def mySkeletal : Prop := ∀ ⦃x y : C⦄, Nonempty (x ≅ y) → x = y

end

-- 注意1.5.17 — 骨格 skC は各同型類から対象を1つ選んだ充満部分圏として作れ、包含が
-- 定理1.5.9 により圏同値になる。Mathlib は同型類の商として Skeleton C を構成する。
-- sk(−) が CAT 上の関手にならない話（脚注42 の pseudofunctor）は Mathlib 対応物なし
#check CategoryTheory.Skeleton
#check CategoryTheory.skeletonEquivalence

-- 例1.5.18・例1.5.19 — 骨格の具体例（連結亜群、preorder と poset、Mat_k、Fin_iso、
-- 軌道・固定化群定理の圏化）。statement は置かない

-- ----------------------------------------------------------------------------
-- 節末問題
-- ----------------------------------------------------------------------------

-- 演習1.5.i — 補題1.5.1 を示す問題。statement は上の myNatTransEquivCylinder に置いた

-- 演習1.5.ii — Segal の圏 Γ（対象は有限集合、射 S → T は θ : S → P(T) で像が互いに
-- 素なもの）が有限点つき集合の圏の逆圏 Fin∗^op と同値であることを示す問題。
-- Γ 圏そのものの構成が大掛かりなので statement は置かない。Mathlib に対応物なし

-- 演習1.5.iii — 補題1.5.10 の4条件の同値を示す問題。statement は上の List.TFAE に置いた

-- 演習1.5.iv(i) — 充満忠実関手は同型を反映する:F.map f が同型なら f も同型
#check CategoryTheory.reflectsIsomorphisms_of_full_and_faithful
example (F : C ⥤ D) (h₁ : myFull F) (h₂ : myFaithful F) {x y : C} (f : x ⟶ y)
    (hf : IsIso (F.map f)) : IsIso f := sorry

-- 演習1.5.iv(ii) — 充満忠実関手は同型を作り出す:Fx ≅ Fy なら x ≅ y。
-- 補題1.3.8 より、逆向きは任意の関手で成り立つ
#check CategoryTheory.Functor.preimageIso
example (F : C ⥤ D) (h₁ : myFull F) (h₂ : myFaithful F) {x y : C}
    (h : Nonempty (F.obj x ≅ F.obj y)) : Nonempty (x ≅ y) := sorry

-- 演習1.5.v — 充満か忠実の片方しか持たない関手は同型を反映も創出もしないことがある、
-- という反例探し。反例の選択自体が問題なので statement は置かない。Mathlib に対応物なし

-- 演習1.5.vi(i) — 充満関手の合成は充満
#check CategoryTheory.Functor.Full.comp
example {F : C ⥤ D} {G : D ⥤ E} (hF : myFull F) (hG : myFull G) : myFull (F ⋙ G) := sorry

-- 演習1.5.vi(i) — 忠実関手の合成は忠実
#check CategoryTheory.Functor.Faithful.comp
example {F : C ⥤ D} {G : D ⥤ E} (hF : myFaithful F) (hG : myFaithful G) :
    myFaithful (F ⋙ G) := sorry

-- 演習1.5.vi(i) — 本質的全射の合成は本質的全射
#check CategoryTheory.Functor.essSurj_comp
example {F : C ⥤ D} {G : D ⥤ E} (hF : myEssSurj F) (hG : myEssSurj G) :
    myEssSurj (F ⋙ G) := sorry

-- 演習1.5.vi(ii) — 圏同値の合成。statement は上の MyEquivalence.trans に置いた
-- （反射律・対称律とあわせて補題1.5.5 の同値関係が出る）

-- 演習1.5.vii — 離散圏と圏同値になる圏（本文の essentially discrete）を特徴づける問題。
-- 特徴づけを自分で見つけて statement に起こすところまでが演習なので置かない。
-- Mathlib に対応物なし

-- 演習1.5.viii — アフィン平面の亜群 Affine と、無限遠直線つき射影平面の亜群 Proj| の
-- 圏同値（Klein の Erlangen プログラム）。接続構造の定式化が大掛かりなので statement は
-- 置かない。Mathlib に対応物なし（関連: Configuration.ProjectivePlane）

-- 演習1.5.ix — 包含 Ab → Group、忘却 Ring → Ab、単数群 (−)^× : Ring → Group、
-- 包含 Ring → Rng、包含 Field → Ring、忘却 R-Mod → Ab のそれぞれについて充満・忠実・
-- 本質的全射を判定する問題。判定自体が問題（一部は研究レベルの警告つき）なので
-- statement は置かない。Mathlib の対応する圏は CommGrp, Grp, RingCat, ModuleCat など

end Riehl
