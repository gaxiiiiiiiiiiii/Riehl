import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# 3.5 極限と余極限の表現可能性

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 例3.5.4（冪）、例3.5.7（余積）、例3.5.8（余冪）、例3.5.9（押し出し）、
注意3.5.14（一般化された要素）は載せない。
-/

open CategoryTheory Limits Opposite

universe v u

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 錐の集合としての lim C(X, F−)（定理3.5.2 の前）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の図式 F : J → C と対象 X ∈ C について、Set の図式 C(X, F−) の極限の要素は頂点 X を持つ
F 上の錐にほかならず、lim_J C(X, F−) ≅ Cone(X, F) である。
-/

#check Types.limitEquivSections
#check Limits.coneOfSectionCompCoyoneda
#print Functor.cones

noncomputable def myLimitHomEquivCone (F : J ⥤ C) (X : Cᵒᵖ) :
    limit (F ⋙ coyoneda.obj X) ≃ F.cones.obj X := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
極限が存在する任意の図式 F : J → C について、極限錐が誘導する標準的な写像は、各 X ∈ C に
ついて自然な同型 C(X, lim_J F) ≅ lim_J C(X, F−) を定める。したがって共変表現可能関手
C(X, −) : C → Set は、C に存在する任意の極限を保存する。
-/

#check coyoneda_preservesLimit

theorem thm_3_5_2_iso (F : J ⥤ C) [HasLimit F] (X : Cᵒᵖ) :
    IsIso (limit.post F (coyoneda.obj X)) := sorry

noncomputable def thm_3_5_2_natIso (F : J ⥤ C) [HasLimit F] :
    yoneda.obj (limit F) ≅ coyoneda ⋙ (Functor.whiskeringLeft J C (Type v)).obj F ⋙ lim := sorry

theorem thm_3_5_2_preserves (F : J ⥤ C) (X : Cᵒᵖ) :
    PreservesLimit F (coyoneda.obj X) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.5
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C を任意の局所小圏とする。(i) 共変表現可能関手 C(X, −) は C に存在するすべての極限を保存する。
(ii) 共変米田埋め込み よ : C ↪ Set^{C^op} は極限を保存し、かつ反映する。
-/

#check coyoneda_preservesLimits

theorem thm_3_5_5_i (X : Cᵒᵖ) : PreservesLimitsOfSize.{v, v} (coyoneda.obj X) := sorry

#check yonedaFunctor_preservesLimits

theorem thm_3_5_5_ii_preserves : PreservesLimitsOfSize.{v, v} (yoneda : C ⥤ Cᵒᵖ ⥤ Type v) := sorry

#check yonedaFunctor_reflectsLimits

theorem thm_3_5_5_ii_reflects : ReflectsLimitsOfSize.{v, v} (yoneda : C ⥤ Cᵒᵖ ⥤ Type v) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
余極限が存在する任意の図式 F : J → C について、余極限錐が誘導する標準的な写像は、各 X ∈ C
について自然な同型 C(colim_J F, X) ≅ lim_{J^op} C(F−, X) を定める。したがって反変表現可能
関手 C(−, X) : C^op → Set は、C に存在する任意の余極限を Set の極限に写す。

構成: C(colim_J F, X) は `limit F.op` に `yoneda.obj X` を適用した値として書く。
-/

#check limitOpIsoOpColimit
#check yoneda_preservesLimit

theorem thm_3_5_6_iso (F : J ⥤ C) [HasColimit F] (X : C) :
    IsIso (limit.post F.op (yoneda.obj X)) := sorry

theorem thm_3_5_6_preserves (F : J ⥤ C) (X : C) :
    PreservesLimit F.op (yoneda.obj X) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.10
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C を任意の局所小圏とする。(i) 反変表現可能関手 C(−, X) は C の余極限を Set の極限に写す。
(ii) 反変米田埋め込み よ : C^op ↪ Set^C は C^op の極限を保存し、かつ反映する。
-/

#check yoneda_preservesLimits

theorem thm_3_5_10_i (X : C) : PreservesLimitsOfSize.{v, v} (yoneda.obj X) := sorry

#check coyonedaFunctor_preservesLimits

theorem thm_3_5_10_ii_preserves :
    PreservesLimitsOfSize.{v, v} (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v) := sorry

#check coyonedaFunctor_reflectsLimits

theorem thm_3_5_10_ii_reflects :
    ReflectsLimitsOfSize.{v, v} (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.11
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の小図式 F : J → C の余極限は、J の射で添字づけられた余積から J の対象で添字づけられた
余積への射の対 d, c の余等化子として表せる。ただし、これらの余極限が存在するとする。
特に、小さな余積と余等化子を持つ任意の圏は余完備である。双対に、任意の小図式の極限は積の間の
射の対の等化子として表せ、小さな積と等化子を持つ任意の圏は完備である。
-/

#check Sigma.ι
#check Sigma.desc

noncomputable def myCoproductD (F : J ⥤ C) [HasCoproducts.{v} C] :
    ∐ (fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.1) ⟶ ∐ F.obj :=
  Sigma.desc fun f ↦ Sigma.ι F.obj f.1.1

noncomputable def myCoproductC (F : J ⥤ C) [HasCoproducts.{v} C] :
    ∐ (fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.1) ⟶ ∐ F.obj :=
  Sigma.desc fun f ↦ F.map f.2 ≫ Sigma.ι F.obj f.1.2

#check HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit

noncomputable def thm_3_5_11_cocone (F : J ⥤ C) [HasCoproducts.{v} C] [HasCoequalizers C] :
    Cocone F where
  pt := coequalizer (myCoproductD F) (myCoproductC F)
  ι := {
    app j := Sigma.ι F.obj j ≫ coequalizer.π (myCoproductD F) (myCoproductC F)
    naturality := sorry
  }

#check HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit

noncomputable def thm_3_5_11_isColimit (F : J ⥤ C) [HasCoproducts.{v} C] [HasCoequalizers C] :
    IsColimit (thm_3_5_11_cocone F) := sorry

#check has_colimits_of_hasCoequalizers_and_coproducts

theorem thm_3_5_11_cocomplete [HasCoproducts.{v} C] [HasCoequalizers C] :
    HasColimitsOfSize.{v, v} C := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.5.15
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
終対象 ∗ を持つ任意の圏において、A → ∗ ← B の引き戻しは A と B の積 A × B である。より一般に、
I で添字づけられた対象の族 (A_i) の積は、射の族 (! : A_i → ∗) の広い引き戻しとして構成できる。
したがって、引き戻しと終対象を持つ任意の圏はすべての有限積を持つ。
-/

#check isProductOfIsTerminalIsPullback

def lemma_3_5_15 {P A B T : C} (hT : IsTerminal T) (f : P ⟶ A) (g : P ⟶ B)
    (h : IsLimit (PullbackCone.mk f g (hT.hom_ext (f ≫ hT.from A) (g ≫ hT.from B)))) :
    IsLimit (BinaryFan.mk f g) := sorry

#print WidePullbackShape
#check WidePullbackShape.wideCospan

def lemma_3_5_15_wide {I : Type v} (A : I → C) {T : C} (hT : IsTerminal T)
    (c : Cone (WidePullbackShape.wideCospan T A fun i ↦ hT.from (A i))) (hc : IsLimit c) :
    IsLimit (Fan.mk c.pt fun i ↦ c.π.app (some i)) := sorry

#check hasBinaryProducts_of_hasTerminal_and_pullbacks
#check hasFiniteProducts_of_has_binary_and_terminal

theorem lemma_3_5_15_finiteProducts [HasTerminal C] [HasPullbacks C] :
    HasFiniteProducts C := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.5.16
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
二項積を持つ任意の圏において、(f, g) : A → B × B と対角射 (id_B, id_B) : B → B × B の引き戻し
E → A は、平行な対 f, g : A ⇉ B の等化子である。

構成: `Fork.ofι` が条件 e ≫ f = e ≫ g を要求するので、条件を `lemma_3_5_16_condition` として
先に立て、等化子であること `lemma_3_5_16` はそれを参照する。
-/

#check HasEqualizersOfHasPullbacksAndBinaryProducts.equalizerConeIsLimit

theorem lemma_3_5_16_condition {A B E : C} [HasBinaryProduct B B] {f g : A ⟶ B}
    {e : E ⟶ A} {l : E ⟶ B} (w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B)) :
    e ≫ f = e ≫ g := sorry

def lemma_3_5_16 {A B E : C} [HasBinaryProduct B B] {f g : A ⟶ B}
    {e : E ⟶ A} {l : E ⟶ B} (w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B))
    (h : IsLimit (PullbackCone.mk e l w)) :
    IsLimit (Fork.ofι e (lemma_3_5_16_condition w)) := sorry

#check hasEqualizers_of_hasPullbacks_and_binary_products

theorem lemma_3_5_16_equalizers [HasBinaryProducts C] [HasPullbacks C] :
    HasEqualizers C := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.17
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
図式が有限であるとは、その添字圏の射が有限個であることをいう。引き戻しと終対象を持つ任意の圏は、
すべての有限極限を持つ。双対に、押し出しと始対象を持つ任意の圏は、すべての有限余極限を持つ。
-/

#print FinCategory

class MyFiniteCategory (J : Type v) [SmallCategory J] : Prop where
  finite_mor : Finite (Σ p : J × J, p.1 ⟶ p.2)

theorem myFiniteCategory_iff (J : Type v) [SmallCategory J] :
    MyFiniteCategory J ↔ Nonempty (FinCategory J) := sorry

#print HasFiniteLimits
#check hasFiniteLimits_of_hasTerminal_and_pullbacks

theorem thm_3_5_17 [HasTerminal C] [HasPullbacks C] : HasFiniteLimits C := sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習 3.5.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 同型 (3.5.1) lim_J C(X, F−) ≅ Cone(X, F) は X について自然である。

#check NatIso.ofComponents

noncomputable def ex_3_5_i (F : J ⥤ C) :
    coyoneda ⋙ (Functor.whiskeringLeft J C (Type v)).obj F ⋙ lim ≅ F.cones :=
  NatIso.ofComponents (fun X ↦ (myLimitHomEquivCone F X).toIso) sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習 3.5.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- statement を置かない。「自分の言葉で説明せよ」型で、反例を見つけること自体が問いである。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習 3.5.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- statement を置かない。モノ射・エピ射の表現可能な定義を書くこと自体が解答になる。
