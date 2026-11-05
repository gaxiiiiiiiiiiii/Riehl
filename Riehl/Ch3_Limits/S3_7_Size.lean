import Mathlib.CategoryTheory.Limits.SmallComplete
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# 3.7 大きさの問題

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 例3.7.4（すべての集合の積は存在し、空でないすべての集合の積は存在しない）は
載せない。命題3.7.3 の直後の、余冪についての双対の主張と、命題3.6.10 の再述も載せない。
-/

open CategoryTheory Limits

namespace Riehl

universe v u

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

section Lemma_3_7_1

variable {C : Type u} [Category.{v} C]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.7.1 (i)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の圏 C について、恒等関手 id_C 上の任意の錐 λ の頂点 ℓ は、すべての対象 c ∈ C へ少なくとも
1 本の射を持つ。さらに、頂点 ℓ で添字づけられた脚 λ_ℓ が恒等射ならば、λ は極限錐であり、
ℓ は C の始対象である。

構成: 3 つの結論を、弱始対象であること、極限錐であること、始対象であることの 3 つの宣言に
      分ける。脚 λ_ℓ は `c.π.app c.pt`。
-/

theorem nonempty_hom_of_cone_id (c : Cone (𝟭 C)) (X : C) :
    Nonempty (c.pt ⟶ X) := ⟨c.π.app X⟩


def isLimitOfConeIdAppPtEqId (c : Cone (𝟭 C)) (h : c.π.app c.pt = 𝟙 c.pt) :
    IsLimit c where
  lift s := s.π.app c.pt
  fac s i := s.w (c.π.app i)
  uniq s m w := by
    rw [<- Category.comp_id m, <- h, w]


def isInitialOfConeIdAppPtEqId (c : Cone (𝟭 C)) (h : c.π.app c.pt = 𝟙 c.pt) :
    IsInitial c.pt := by
  apply IsInitial.ofUniqueHom c.π.app ?_
  intro x m
  rw [<- c.w m, h]; simp


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.7.1 (ii)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 任意の圏 C について、恒等関手 id_C が極限を持つことと、C が始対象を持つことは同値である。

-- 圏が始対象を持つこと
#check HasInitial
-- 逆方向の Mathlib の対応物：添字圏が始対象を持てば、その上の任意の図式は極限を持つ
#check hasLimit_of_domain_hasInitial

theorem hasLimit_id_iff_hasInitial : HasLimit (𝟭 C) ↔ HasInitial C where
  mp H := by
    apply IsInitial.hasInitial (X := limit (Functor.id C))
    apply IsInitial.ofUniqueHom (limit.π (Functor.id C))
    intro x m
    rw [<- limit.w (F := Functor.id C) m]
    simp only [Functor.id_obj, Functor.id_map]
    have : limit.π (𝟭 C) (limit (𝟭 C)) = 𝟙 _ := by
      apply limit.hom_ext
      intro y; simp only [Functor.id_obj, Category.id_comp]
      exact limit.w (F := Functor.id C) (limit.π (𝟭 C) y)
    rw [this]; simp
  mpr H := ⟨⟨{
    cone := {
      pt := initial C
      π := {
        app x := initial.to x
        naturality {x y} f:= initial.hom_ext _ _
      }
    }
    isLimit := {
      lift s := s.π.app (initial C)
      fac s x := s.w (initial.to x)
      uniq s m w := by
        simp only [Functor.id_obj] at m w
        rw [<- w]
        have : initial.to (⊥_ C) = 𝟙 (⊥_ C) := initial.hom_ext _ _
        rw [this]; simp
    }
  }⟩⟩






end Lemma_3_7_1

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.7.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小圏 C の濃度とは、C の射全体の集合 mor C の濃度である。

構成: mor C は、始域と終域の対象と、その間の射の組の型 Σ X Y : C, X ⟶ Y。小さな図式の濃度
      （添字圏の濃度）は、この定義を添字圏に当てはめたものなので置かない。
-/

-- 型の濃度
#print Cardinal.mk

def cardinality (C : Type v) [SmallCategory C] : Cardinal.{v} :=
  Cardinal.mk (Σ X Y : C, X ⟶ Y)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.7.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小圏 C が、濃度が C の濃度に等しい任意の集合 I で添字づけられた対象の族の積を持つならば、C は
前順序である。すなわち、任意の対象 X, Y ∈ C について、X から Y への射は高々 1 本である。

構成: 前順序であることは、Mathlib の `Quiver.IsThin`（各 hom 型が高々 1 要素）で書く。
      Mathlib の対応物 `instIsThin` は、濃度を問わずすべての小さな積 `HasProducts` を仮定する。
-/

-- 圏の各 hom 型が高々 1 要素であること
#check Quiver.IsThin
-- 圏が I で添字づけられた任意の対象の族の積を持つこと
#check HasProductsOfShape
#check instIsThin

theorem isThin_of_hasProductsOfShape {C : Type v} [SmallCategory C] (I : Type v)
    (hI : Cardinal.mk I = cardinality C) [HasProductsOfShape I C] : Quiver.IsThin C := by classical
  simp only [cardinality] at hI
  rw [Cardinal.eq] at hI
  obtain ⟨σ⟩ := hI
  intro x y
  by_contra h
  rw [not_subsingleton_iff_nontrivial, nontrivial_iff] at h
  obtain ⟨f, g, F⟩ := h
  let Y := ∏ᶜ (fun _ : I => y)
  apply  Function.cantor_injective (fun (S : Set I) =>
    σ.symm ⟨x, Y, Pi.lift (fun i => if i ∈ S then f else g)⟩
  )
  intro S T H
  simp only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and] at H
  ext i
  have E := congr_arg (fun x => x ≫ Pi.π _ i) H
  rw [Pi.lift_comp_π, Pi.lift_comp_π] at E
  split_ifs at E with HS HT
  · aesop
  · contradiction
  · symm at E; contradiction
  · aesop



-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.7.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 大きさの制限なしにすべての極限を保存するが始対象を保存しない関手が、補題3.7.1 と矛盾しない
-- 理由を説明する問題で、主張を持たないので置かない。

end Riehl
