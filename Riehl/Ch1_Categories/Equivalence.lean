import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Products.Basic

-- ═══════════════════════════════════════════════════════════════════════════
-- 概要
-- ═══════════════════════════════════════════════════════════════════════════
/-!
# 1.5 圏同値

圏の「同じさ」を同型ではなく同値で測る節。中心は定理1.5.9（同値 ⟺ 充満・忠実・本質的全射）
で、以降の章で圏を同型ではなく同値の意味で扱う根拠になる。

本節の定義1.5.4 は関手 F, G と自然同型 η, ε だけを要求し、三角等式を課さない。Mathlib の
`CategoryTheory.Equivalence` は三角等式 (`functor_unitIso_comp`) を含むため、本の定義とは
一致しない。この差は本書では命題4.3.5（随伴同値への格上げ）で埋められる。ここでは本の定義を
`MyEquivalence` として自前で置き、Mathlib のものは対応先として `#check` で示す。

ファイル構成:
  前提パート: 定義1.5.7（充満・忠実・本質的全射）に対応する Mathlib の定義の写し
  本体:
    Part A（1–4）: 定義1.5.4 と補題1.5.5
    Part B（5–9）: 定理1.5.9 とその補題1.5.10
    Part C（10–13）: 骨格と同値不変性
    Part D: Lean で述べにくい節末問題

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Equivalence.lean`（`Equivalence`・`IsEquivalence`・`asEquivalence`）
  - `Mathlib/CategoryTheory/Functor/FullyFaithful.lean`（`Full`・`Faithful`・`FullyFaithful`）
  - `Mathlib/CategoryTheory/EssentialImage.lean`（`essImage`・`EssSurj`）
  - `Mathlib/CategoryTheory/Skeletal.lean`（`Skeletal`・`Skeleton`・`skeletonEquivalence`）
  - `Mathlib/CategoryTheory/SingleObj.lean`（`SingleObj`）
-/

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

-- ═══════════════════════════════════════════════════════════════════════════
-- 前提: 演習が使う Mathlib の定義
-- ═══════════════════════════════════════════════════════════════════════════

namespace Recap

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- 定義1.5.7 の「充満」。本では射集合の写像 `C(x,y) → D(Fx,Fy)` の全射性として述べられる
class Full (F : C ⥤ D) : Prop where
  map_surjective {X Y : C} : Function.Surjective (F.map (X := X) (Y := Y))

-- 定義1.5.7 の「忠実」。同じ写像の単射性
class Faithful (F : C ⥤ D) : Prop where
  map_injective : ∀ {X Y : C}, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))

-- 本質的像。`F` の像と同型になる対象の集まりで、対象の等式ではなく同型を使うのが要点
def essImage (F : C ⥤ D) : ObjectProperty D := fun Y => ∃ X : C, Nonempty (F.obj X ≅ Y)

-- 定義1.5.7 の「対象について本質的全射」。すべての対象が本質的像に入ること
class EssSurj (F : C ⥤ D) : Prop where
  mem_essImage (F) (Y : D) : essImage F Y

end Recap

-- ═══════════════════════════════════════════════════════════════════════════
-- 本体
-- ═══════════════════════════════════════════════════════════════════════════

-- ── Part A: 圏同値の定義（定義1.5.4・補題1.5.5） ─────────────────────────────

-- 定義1.5.4。本の定義そのままで、三角等式は課さない。
-- Mathlib の `Equivalence` は三角等式 `functor_unitIso_comp` を持つ点だけが異なる。
#check @CategoryTheory.Equivalence

structure MyEquivalence (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] where
  functor : C ⥤ D
  inverse : D ⥤ C
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  counitIso : inverse ⋙ functor ≅ 𝟭 D

-- 1. 恒等関手が同値を定めることを示す（補題1.5.5 の反射律）。
#check @CategoryTheory.Equivalence.refl

def MyEquivalence.refl : MyEquivalence C C := {
  functor := Functor.id C
  inverse := Functor.id C
  unitIso := by rw [Functor.id_comp]
  counitIso := by rw [Functor.id_comp]
}

-- 2. 同値の向きを逆にしたものが同値であることを示す（補題1.5.5 の対称律）。
#check @CategoryTheory.Equivalence.symm

def MyEquivalence.symm (e : MyEquivalence C D) : MyEquivalence D C := {
  functor := e.inverse
  inverse := e.functor
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm
}

-- 3. 同値の合成が同値であることを示す（補題1.5.5 の推移律、演習1.5.vi(ii)）。
#check @CategoryTheory.Equivalence.trans

def MyEquivalence.trans (e : MyEquivalence C D) (f : MyEquivalence D E) :
    MyEquivalence C E := {
    functor := e.functor ⋙ f.functor
    inverse := f.inverse ⋙ e.inverse
    unitIso := by
      rw [e.functor.assoc, <- f.functor.assoc]
      have σ := e.inverse.leftUnitor.symm.trans (Functor.isoWhiskerRight f.unitIso e.inverse)
      have μ := Functor.isoWhiskerLeft e.functor σ
      apply e.unitIso.trans μ
    counitIso := by
      rw [f.inverse.assoc, <- e.inverse.assoc]
      have σ :=  (Functor.isoWhiskerRight e.counitIso f.functor).trans f.functor.leftUnitor
      have μ := Functor.isoWhiskerLeft f.inverse σ
      apply μ.trans f.counitIso
  }

-- 4. 補題1.5.1 の一方向を作る。自然変換 α : F ⟶ G から関手 H : C × 2 → D を構成する。
--    ここで 2 は `Fin 2` を preorder として圏とみたもの、`incl j` は `X ↦ (X, j)` である。
--    本の主張は両向きの対応が全単射であることだが、それを述べるには関手の等式を条件に持つ
--    部分型が必要になるため、ここでは両向きの構成と制限の等式に分けて置く。
--    Mathlib に対応物なし。
def incl (j : Fin 2) : C ⥤ C × Fin 2 where
  obj X := (X, j)
  map f := (f, 𝟙 j)

def myCylinder {F G : C ⥤ D} (α : F ⟶ G) : C × Fin 2 ⥤ D := sorry

theorem myCylinder_incl_zero {F G : C ⥤ D} (α : F ⟶ G) :
    incl 0 ⋙ myCylinder α = F := sorry

theorem myCylinder_incl_one {F G : C ⥤ D} (α : F ⟶ G) :
    incl 1 ⋙ myCylinder α = G := sorry

def myNatTransOfFunctor {F G : C ⥤ D} (H : C × Fin 2 ⥤ D)
    (h₀ : incl 0 ⋙ H = F) (h₁ : incl 1 ⋙ H = G) : F ⟶ G := sorry

-- ── Part B: 定理1.5.9 とその周辺 ────────────────────────────────────────────

-- 5. 同値を定める関手が忠実であることを示す（定理1.5.9 の順方向）。
#check @CategoryTheory.Functor.IsEquivalence.faithful

theorem myFaithful_of_myEquivalence (e : MyEquivalence C D) : e.functor.Faithful := sorry

-- 6. 同値を定める関手が充満であることを示す（定理1.5.9 の順方向）。
#check @CategoryTheory.Functor.IsEquivalence.full

theorem myFull_of_myEquivalence (e : MyEquivalence C D) : e.functor.Full := sorry

-- 7. 同値を定める関手が対象について本質的全射であることを示す（定理1.5.9 の順方向）。
#check @CategoryTheory.Functor.IsEquivalence.essSurj

theorem myEssSurj_of_myEquivalence (e : MyEquivalence C D) : e.functor.EssSurj := sorry

-- 8. 充満・忠実・本質的全射な関手から同値を構成する（定理1.5.9 の逆方向）。
--    逆関手の対象への値を選ぶ箇所で選択公理を使うため `noncomputable` になる。
#check @CategoryTheory.Functor.asEquivalence

noncomputable def myEquivalenceOfProperties (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] :
    MyEquivalence C D := sorry

-- 9. 補題1.5.10。射 f : a ⟶ b と同型 u : a ≅ a'、v : b ≅ b' に対し、左の図式を可換にする
--    f' が一意に定まり、その条件が残り3つの図式の可換性と同値であることを示す（演習1.5.iii）。
#check @CategoryTheory.Iso.inv_comp_eq
#check @CategoryTheory.Iso.comp_inv_eq
#check @CategoryTheory.Iso.eq_inv_comp
#check @CategoryTheory.Iso.eq_comp_inv

example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') :
    ∃! f' : a' ⟶ b', u.hom ≫ f' = f ≫ v.hom := sorry

example {a b a' b' : C} (f : a ⟶ b) (f' : a' ⟶ b') (u : a ≅ a') (v : b ≅ b') :
    u.hom ≫ f' = f ≫ v.hom ↔ f' = u.inv ≫ f ≫ v.hom := sorry

-- ── Part C: 充満忠実性の帰結・骨格・同値不変性 ──────────────────────────────

-- 10. 充満忠実な関手が同型を反映することを示す（演習1.5.iv(i)）。
#check @CategoryTheory.isIso_of_fully_faithful

example (F : C ⥤ D) [F.Full] [F.Faithful] {x y : C} (f : x ⟶ y) [IsIso (F.map f)] :
    IsIso f := sorry

-- 11. 充満忠実な関手が同型を創出することを示す（演習1.5.iv(ii)）。
#check @CategoryTheory.Functor.FullyFaithful.preimageIso

example (F : C ⥤ D) [F.Full] [F.Faithful] {x y : C} (e : F.obj x ≅ F.obj y) : x ≅ y := sorry

-- 12. 充満・忠実・本質的全射がそれぞれ合成で保たれることを示す（演習1.5.vi(i)）。
#check @CategoryTheory.Functor.Full.comp
#check @CategoryTheory.Functor.Faithful.comp
#check @CategoryTheory.Functor.essSurj_comp

example (F : C ⥤ D) (G : D ⥤ E) [F.Full] [G.Full] : (F ⋙ G).Full := sorry

example (F : C ⥤ D) (G : D ⥤ E) [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful := sorry

example (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] : (F ⋙ G).EssSurj := sorry

-- 13. 骨格が元の圏と同値であることを示す（定義1.5.16・注意1.5.17）。
--     `Skeleton C` は各同型類から対象を一つ選んで作った充満部分圏である。
#check @CategoryTheory.Skeletal
#check @CategoryTheory.skeletonEquivalence

example : Skeleton C ≌ C := sorry

-- 14. 同値が反対圏に移ることを示す（同値不変性の例）。
#check @CategoryTheory.Equivalence.op

example (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ := sorry

-- 15. 連結亜圏が、その任意の対象の自己同型群と同値であることを示す（命題1.5.13）。
--     Mathlib に対応物なし。
example {G : Type u₁} [Groupoid.{v₁} G] [IsConnected G] (g : G) :
    SingleObj (Aut g) ≌ G := sorry

-- ── Part D: Lean で述べにくい節末問題 ───────────────────────────────────────
--
-- 以下は statement を置かず、問題文だけを残す。
--
-- 演習1.5.ii: Segal の圏 Γ（対象は有限集合、射 S → T は θ : S → P(T) で α ≠ β のとき
--   θ(α) と θ(β) が交わらないもの）が、有限点付き集合の圏の反対圏 Fin∗^op と同値であることを
--   示す。Mathlib に Γ の定義がなく、圏の構成から始めることになる。
--
-- 演習1.5.v: 充満または忠実だが両方ではない関手で、同型を反映も創出もしないものの例を挙げる。
--   反例の構成が課題であり、統一した statement の形にならない。
--
-- 演習1.5.vii: 離散圏と同値な圏を特徴づける（本文の言葉では「本質的離散」)。特徴づけの主張の
--   形自体が答えの一部になるため、statement を置くと問題が成立しない。
--
-- 演習1.5.viii: アフィン平面の亜圏 Affine が、無限遠直線を指定した射影平面の亜圏 Proj| と
--   同値であることを示す。Mathlib に対応する幾何的な圏がない。
--
-- 演習1.5.ix: I : Ab → Group、I : Ring → Ab、(−)× : Ring → Group、I : Ring → Rng、
--   I : Field → Ring、U : R-Mod → Ab について、充満・忠実・本質的全射のどれが成り立つかを
--   判定し、同値を定めるものがあるかを問う。個々の圏（`RingCat` など）ごとに別の演習になるため、
--   扱うなら独立したファイルに分ける。
