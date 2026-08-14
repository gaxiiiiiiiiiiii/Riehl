import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.HomCongr
import Mathlib.Tactic.FinCases

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
    Part A: 定義1.5.4 と補題1.5.5・補題1.5.1
    Part B: 定理1.5.9 とその補題1.5.10
    Part C: 骨格と同値不変性
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

-- 補題1.5.5 の反射律。恒等関手が同値を定めることを示す。
#check @CategoryTheory.Equivalence.refl

def MyEquivalence.refl : MyEquivalence C C := {
  functor := Functor.id C
  inverse := Functor.id C
  unitIso := by rw [Functor.id_comp]
  counitIso := by rw [Functor.id_comp]
}

-- 補題1.5.5 の対称律。同値の向きを逆にしたものが同値であることを示す。
#check @CategoryTheory.Equivalence.symm

def MyEquivalence.symm (e : MyEquivalence C D) : MyEquivalence D C := {
  functor := e.inverse
  inverse := e.functor
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm
}

-- 補題1.5.5 の推移律（演習1.5.vi(ii)）。同値の合成が同値であることを示す。
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

-- 補題1.5.1 の一方向を作る。自然変換 α : F ⟶ G から関手 H : C × 2 → D を構成する。
--    ここで 2 は `Fin 2` を preorder として圏とみたもの、`incl j` は `X ↦ (X, j)` である。
--    本の主張は両向きの対応が全単射であることだが、それを述べるには関手の等式を条件に持つ
--    部分型が必要になるため、ここでは両向きの構成と制限の等式に分けて置く。
--    Mathlib に対応物なし。
def incl (j : Fin 2) : C ⥤ C × Fin 2 where
  obj X := (X, j)
  map f := (f, 𝟙 j)

def myCylinder {F G : C ⥤ D} (α : F ⟶ G) : C × Fin 2 ⥤ D where
  obj
  | ⟨c, 0⟩ => F.obj c
  | ⟨c, 1⟩ => G.obj c
  map {X Y} f := match X, Y, f with
  | (p, 0), (q, 0), (f, _) => F.map f
  | (p, 0), (q, 1), (f, _) => α.app p ≫ G.map f
  | (p, 1), (q, 1), (f, _) => G.map f
  | (p, 1), (q, 0), (_, ⟨⟨(h : 1 ≤ 0)⟩⟩) => nomatch h
  map_id
  | ⟨x, 0⟩
  | ⟨x, 1⟩ => by simp
  map_comp  {X Y Z} f g := match X, Y, Z, f, g with
  | (x, 0), (y, 0), (z, 0), (f, _), (g, _)
  | (x, 0), (y, 0), (z, 1), (f, _), (g, _)
  | (x, 0), (y, 1), (z, 1), (f, _), (g, _)
  | (x, 1), (y, 1), (z, 1), (f, _), (g, _) => by simp

theorem myCylinder_incl_zero {F G : C ⥤ D} (α : F ⟶ G) :
    incl 0 ⋙ myCylinder α = F := by
  apply CategoryTheory.Functor.ext ?_ ?_
  · intro x;
    rw [CategoryTheory.Functor.comp_obj]
    simp only [incl, myCylinder]
  · intro x y f
    exact Functor.congr_hom rfl f


theorem myCylinder_incl_one {F G : C ⥤ D} (α : F ⟶ G) :
    incl 1 ⋙ myCylinder α = G := by
  apply CategoryTheory.Functor.ext ?_ ?_
  · intro x; rw [CategoryTheory.Functor.comp_obj]
    simp only [incl, myCylinder]
  · intro x y f
    exact Functor.congr_hom rfl f



def myNatTransOfFunctor {F G : C ⥤ D} (H : C × Fin 2 ⥤ D)
    (h₀ : incl 0 ⋙ H = F) (h₁ : incl 1 ⋙ H = G) : F ⟶ G
where
  app c := (eqToHom h₀.symm).app c ≫  H.map (Prod.mkHom (𝟙 c)  (homOfLE (Fin.zero_le 1))) ≫ (eqToHom h₁).app c
  naturality {x y} f := by
    subst h₁ h₀
    simp only [eqToHom_refl, NatTrans.id_app]
    dsimp only [incl, Functor.comp_obj, Functor.comp_map]
    simp only [Category.comp_id, Category.id_comp, ← H.map_comp]
    congr 1
    ext<;> simp



-- ── Part B: 定理1.5.9 とその周辺 ────────────────────────────────────────────


-- 同型は合成の左から消去できる。本文には現れないが、定理1.5.9 以降で同型を挟んだ等式を
-- 整理するのに繰り返し使うため、ここで演習にしておく。
#check @CategoryTheory.Iso.cancel_iso_hom_left

example {X Y Z : C} (f : X ≅ Y) (g g' : Y ⟶ Z) :
    f.hom ≫ g = f.hom ≫ g' ↔ g = g' := by
  constructor<;> intro H
  · rw [<- Category.id_comp g, <- f.inv_hom_id, Category.assoc]
    rw [H, <- Category.assoc, f.inv_hom_id, Category.id_comp]
  · subst H; rfl

-- 同じことを右から。
#check @CategoryTheory.Iso.cancel_iso_hom_right

example {X Y Z : C} (f f' : X ⟶ Y) (g : Y ≅ Z) :
    f ≫ g.hom = f' ≫ g.hom ↔ f = f' := by
  constructor<;> intro H; swap; subst H; rfl
  rw [<- Category.comp_id f, <- g.hom_inv_id, <- Category.assoc, H]
  rw [Category.assoc, g.hom_inv_id]; simp


-- 自然同型 `α : F ≅ G` から `Iso.app` で取り出した各点の同型の `hom` は、`α.hom` の成分と
-- 一致する。`Iso` の言葉と `NatTrans` の言葉を往復するのに要る。
#check @CategoryTheory.Iso.app_hom

example {F G : C ⥤ D} (α : F ≅ G) (X : C) : (α.app X).hom = α.hom.app X := by rfl


-- 定理1.5.9 の順方向のうち忠実性。同値を定める関手が忠実であることを示す。
#check @CategoryTheory.Functor.IsEquivalence.faithful

theorem myFaithful_of_myEquivalence (e : MyEquivalence C D) : e.functor.Faithful where
  map_injective := by
    intro x y f g H
    have Hf := e.unitIso.hom.naturality f
    have Hg := e.unitIso.hom.naturality g
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at Hf Hg
    rw [H] at Hf
    have E := Hf.trans Hg.symm
    have Hy := NatTrans.congr_app e.unitIso.hom_inv_id y
    rw [NatTrans.comp_app, NatTrans.id_app] at Hy
    have := Functor.id_obj y
    change _ = 𝟙 y at Hy
    rw [<- Category.comp_id f, <- Hy, <- Category.assoc, E]
    rw [Category.assoc, <- NatTrans.comp_app, e.unitIso.hom_inv_id]
    simp


-- 定理1.5.9 の順方向のうち充満性。同値を定める関手が充満であることを示す。
#check @CategoryTheory.Functor.IsEquivalence.full

theorem myFull_of_myEquivalence (e : MyEquivalence C D) : e.functor.Full where
  map_surjective := by
    intro x y f
    use e.unitIso.hom.app x ≫ e.inverse.map f ≫ e.unitIso.inv.app y
    set g : x ⟶ y := e.unitIso.hom.app x ≫ e.inverse.map f ≫ e.unitIso.inv.app y
    have Hg := e.unitIso.hom.naturality g
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at Hg
    conv at Hg =>
      arg 1; simp only [Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id, g]
    rw [<- e.unitIso.app_hom x, (e.unitIso.app x).cancel_iso_hom_left] at Hg
    have E :  e.inverse.Faithful := (myFaithful_of_myEquivalence e.symm)
    apply E.map_injective
    rw [Hg]


-- 定理1.5.9 の順方向のうち本質的全射性。同値を定める関手が対象について本質的全射であることを示す。
#check @CategoryTheory.Functor.IsEquivalence.essSurj

theorem myEssSurj_of_myEquivalence (e : MyEquivalence C D) : e.functor.EssSurj where
  mem_essImage y := by
    unfold Functor.essImage
    use e.inverse.obj y; constructor
    refine {
      hom := e.counitIso.hom.app y
      inv := e.counitIso.inv.app y
      hom_inv_id := by
        rw [e.counitIso.hom_inv_id_app]; rfl
      inv_hom_id := by rw [e.counitIso.inv_hom_id_app]; rfl
    }





-- Recap: `Functor.objPreimage`・`Functor.preimage` の実装確認。定理1.5.9 の逆方向で使う
-- 2つの選択が何をどう選んでいるかを見る。実際の構成では Mathlib のものを使う。
namespace Recap

-- 本質的像に入っているという証明から、対象と同型を取り出す。選択公理を使うのはこの2つだけ
noncomputable def essImageWitness {F : C ⥤ D} {Y : D} (h : F.essImage Y) : C :=
  h.choose

noncomputable def essImageGetIso {F : C ⥤ D} {Y : D} (h : F.essImage Y) :
    F.obj (essImageWitness h) ≅ Y :=
  Classical.choice h.choose_spec

#check @CategoryTheory.Functor.objPreimage
#check @CategoryTheory.Functor.objObjPreimageIso

noncomputable def objPreimage (F : C ⥤ D) [F.EssSurj] (Y : D) : C :=
  essImageWitness (Functor.EssSurj.mem_essImage F Y)

noncomputable def objObjPreimageIso (F : C ⥤ D) [F.EssSurj] (Y : D) :
    F.obj (objPreimage F Y) ≅ Y :=
  essImageGetIso _

#check @CategoryTheory.Functor.preimage
#check @CategoryTheory.Functor.map_preimage

noncomputable def preimage (F : C ⥤ D) [F.Full] {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  (F.map_surjective f).choose

theorem map_preimage (F : C ⥤ D) [F.Full] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
    F.map (preimage F f) = f :=
  (F.map_surjective f).choose_spec

end Recap

-- 逆関手の射への作用。Mathlib に単独の対応物がないため自前で置く。`myInverseMap_spec` が
-- `F.map` で送り返したときの値を決めており、以降の証明はこの1本だけで回る。
noncomputable def myInverseMap (F : C ⥤ D) [F.Full] [F.EssSurj] {d d' : D} (f : d ⟶ d') :
    F.objPreimage d ⟶ F.objPreimage d' :=
  F.preimage ((F.objObjPreimageIso d).hom ≫ f ≫ (F.objObjPreimageIso d').inv)

@[simp]
lemma myInverseMap_spec (F : C ⥤ D) [F.Full] [F.EssSurj] {d d' : D} (f : d ⟶ d') :
    F.map (myInverseMap F f)
      = (F.objObjPreimageIso d).hom ≫ f ≫ (F.objObjPreimageIso d').inv :=
  F.map_preimage _

-- 定理1.5.9 の逆方向。充満・忠実・本質的全射な関手から同値を構成する。
--    逆関手の対象への値を選ぶ箇所で選択公理を使うため `noncomputable` になる。
#check @CategoryTheory.Functor.asEquivalence

noncomputable def myEquivalenceOfProperties (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj] :
    MyEquivalence C D
  where
    functor := F
    inverse := {
      obj := F.objPreimage
      map := myInverseMap F
      map_id d := by apply F.map_injective; simp
      map_comp f g := by apply F.map_injective; simp
    }

    unitIso := {
      hom := {
        app c := F.preimage (F.objObjPreimageIso (F.obj c)).inv
        naturality {c c'} f:= by
          simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
          apply F.map_injective
          simp only [F.map_comp]
          erw [F.map_preimage, F.map_preimage, myInverseMap_spec]
          erw [<- Category.assoc, Iso.inv_hom_id, Category.id_comp]
      }
      inv := {
        app c := F.preimage (F.objObjPreimageIso (F.obj c)).hom
        naturality {c c'} f := by
          simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map]
          apply F.map_injective
          simp only [F.map_comp]
          erw [F.map_preimage, F.map_preimage, F.map_preimage]
          erw [Category.assoc, Category.assoc]
          erw [Iso.inv_hom_id, Category.comp_id]
      }
      hom_inv_id := by
        ext c
        simp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, NatTrans.id_app]
        apply F.map_injective
        erw [F.map_comp, F.map_preimage, F.map_preimage]
        erw [Iso.inv_hom_id]; simp
      inv_hom_id := by
        ext c; simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, NatTrans.id_app]
        apply F.map_injective
        erw [F.map_comp, F.map_preimage, F.map_preimage]
        erw [(F.objObjPreimageIso (F.obj c)).hom_inv_id]
        rw [F.map_id]
    }

    counitIso := {
      hom := {
        app d := (F.objObjPreimageIso d).hom
        naturality {d d'} f:= by
          simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, myInverseMap_spec, Functor.id_map]
          erw [Category.assoc, Category.assoc, Iso.inv_hom_id]
          simp
      }
      inv := {
        app d := (F.objObjPreimageIso d).inv
        naturality {d d'} f:= by
          simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map, myInverseMap_spec]
          erw [<- Category.assoc, <- Category.assoc, Iso.inv_hom_id]
          simp only [Category.id_comp]
      }
      hom_inv_id := by ext d; simp
      inv_hom_id := by ext d; simp
    }

-- 補題1.5.10（演習1.5.iii）。f' の構成は Mathlib では homCongr（本の図式1を定義に採用したもの）。
-- 残り3つの図式の可換性は、それぞれ「f' が homCongr の値であること」と同値。
#check @CategoryTheory.Iso.homCongr

-- Recap: `Iso.homCongr` の実装確認。データ部分は図式1・図式4 の式そのもので、そこに
-- 「互いに逆」の証明が付く。一意性はこの Equiv 構造に含意される。演習では Mathlib のものを使う。
namespace Recap

def homCongr {a b a' b' : C} (u : a ≅ a') (v : b ≅ b') : (a ⟶ b) ≃ (a' ⟶ b') where
  toFun f := u.inv ≫ f ≫ v.hom
  invFun f' := u.hom ≫ f' ≫ v.inv
  left_inv f :=
    show u.hom ≫ (u.inv ≫ f ≫ v.hom) ≫ v.inv = f by
      rw [Category.assoc, Category.assoc, v.hom_inv_id, u.hom_inv_id_assoc, Category.comp_id]
  right_inv f' :=
    show u.inv ≫ (u.hom ≫ f' ≫ v.inv) ≫ v.hom = f' by
      rw [Category.assoc, Category.assoc, v.inv_hom_id, u.inv_hom_id_assoc, Category.comp_id]

end Recap

-- 図式1: homCongr の定義そのもの
#check @CategoryTheory.Iso.homCongr_apply
example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') :
    u.homCongr v f = u.inv ≫ f ≫ v.hom := by rfl

-- 図式2
#check @CategoryTheory.Iso.eq_inv_comp
example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') (f' : a' ⟶ b') :
    f' = u.homCongr v f ↔ u.hom ≫ f' = f ≫ v.hom := by
  simp only [Iso.homCongr_apply]
  constructor<;> intro H
  · rw [H, <- Category.assoc, u.hom_inv_id, Category.id_comp]
  · rw [<- u.cancel_iso_hom_left, H]; simp


-- 図式3
#check @CategoryTheory.Iso.comp_inv_eq
example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') (f' : a' ⟶ b') :
    f' = u.homCongr v f ↔ f' ≫ v.inv = u.inv ≫ f := by
  simp only [Iso.homCongr_apply]; constructor<;> intro H
  · rw [H]; simp
  · rw [<- Category.assoc, <- H]; simp

-- 図式4
#check @CategoryTheory.Iso.eq_comp_inv
example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') (f' : a' ⟶ b') :
    f' = u.homCongr v f ↔ f = u.hom ≫ f' ≫ v.inv := by
  simp only [Iso.homCongr_apply]; constructor<;> intro H
  · rw [H]; simp
  · rw [H]; simp


-- 一意性。本の「determine a unique morphism」の形。Mathlib に対応物なし
-- （homCongr が Equiv であることに含意される）。
example {a b a' b' : C} (f : a ⟶ b) (u : a ≅ a') (v : b ≅ b') :
    ∃! f' : a' ⟶ b', u.hom ≫ f' = f ≫ v.hom := by
  use u.homCongr v f
  simp only [Iso.homCongr_apply, Iso.hom_inv_id_assoc, true_and]
  intro f' Hf
  rw [<- Hf]; simp

-- ── Part C: 充満忠実性の帰結・骨格・同値不変性 ──────────────────────────────

-- 演習1.5.iv(i)。充満忠実な関手が同型を反映することを示す。
#check @CategoryTheory.isIso_of_fully_faithful

example (F : C ⥤ D) [F.Full] [F.Faithful] {x y : C} (f : x ⟶ y) [IsIso (F.map f)] :
  IsIso f
where
  out := by
    have Hf := F.map_surjective (inv (F.map f))
    have Hg := Hf.choose_spec
    set g := Hf.choose
    use g
    constructor<;> apply F.map_injective<;>
    rw [F.map_comp, Hg]<;> simp





-- 演習1.5.iv(ii)。充満忠実な関手が同型を創出することを示す。
#check @CategoryTheory.Functor.preimageIso

noncomputable example (F : C ⥤ D) [F.Full] [F.Faithful] {x y : C} (e : F.obj x ≅ F.obj y) :
  x ≅ y
where
  hom := F.preimage e.hom
  inv := F.preimage e.inv
  hom_inv_id := by
    apply F.map_injective
    rw [F.map_comp, F.map_preimage, F.map_preimage]
    simp
  inv_hom_id := by
    apply F.map_injective
    rw [F.map_comp, F.map_preimage, F.map_preimage]
    simp






-- 演習1.5.vi(i)。充満・忠実・本質的全射がそれぞれ合成で保たれることを示す。
#check @CategoryTheory.Functor.Full.comp
#check @CategoryTheory.Functor.Faithful.comp
#check @CategoryTheory.Functor.essSurj_comp

example (F : C ⥤ D) (G : D ⥤ E) [F.Full] [G.Full] : (F ⋙ G).Full where
  map_surjective {X Y} f := by
    have hf := G.map_surjective f
    have Hg := hf.choose_spec
    set g := hf.choose
    have hg := F.map_surjective g
    have Hh := hg.choose_spec
    set h := hg.choose
    use h
    rw [Functor.comp_map, Hh, Hg]


example (F : C ⥤ D) (G : D ⥤ E) [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful where
  map_injective {X Y} f g H := by
    apply F.map_injective
    apply G.map_injective
    exact H

example (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] : (F ⋙ G).EssSurj where
  mem_essImage e := by
    use F.objPreimage (G.objPreimage e)
    constructor
    rw [Functor.comp_obj]
    exact (G.mapIso (F.objObjPreimageIso (G.objPreimage e))).trans (G.objObjPreimageIso e)


-- 定義1.5.16・注意1.5.17。骨格が元の圏と同値であることを示す。
--     `Skeleton C` は各同型類から対象を一つ選んで作った充満部分圏である。
--     以下の Recap で実装を確認する。再現対象の `skeletonEquivalence` 本体は写さない。
#check @CategoryTheory.isIsomorphicSetoid
#check @CategoryTheory.Skeletal
#check @CategoryTheory.Skeleton
#check @CategoryTheory.fromSkeleton

-- Recap: `Skeletal`・`Skeleton`・`fromSkeleton` の実装確認。「各同型類から対象を一つ選ぶ」
-- 選択がどの層で起きるかを見る。演習では Mathlib のものを使う。
namespace Recap

-- 同型を同値関係と見る。骨格の対象はこれによる商
def isIsomorphicSetoid (C : Type u₁) [Category.{v₁} C] : Setoid C where
  r X Y := Nonempty (X ≅ Y)
  iseqv := ⟨fun X => ⟨Iso.refl X⟩, fun ⟨α⟩ => ⟨α.symm⟩, fun ⟨α⟩ ⟨β⟩ => ⟨α.trans β⟩⟩

-- 定義1.5.16 の「骨格的」: 同型な対象は等しい
def Skeletal (C : Type u₁) [Category.{v₁} C] : Prop :=
  ∀ ⦃X Y : C⦄, IsIsomorphic X Y → X = Y

-- 各同型類から代表を一つ選ぶ。選択公理を使うのはここ（`Quotient.out` の実体）
noncomputable def quotOut {α : Sort*} {r : α → α → Prop} (q : Quot r) : α :=
  Classical.choose q.exists_rep

-- 骨格: 対象は同型類の商、射は選んだ代表の間の C の射（`InducedCategory` が付け替える）
def Skeleton (C : Type u₁) [Category.{v₁} C] : Type u₁ :=
  InducedCategory (C := Quotient (isIsomorphicSetoid C)) C Quotient.out

noncomputable instance (C : Type u₁) [Category.{v₁} C] : Category (Skeleton C) :=
  inferInstanceAs (Category (InducedCategory _ Quotient.out))

-- 骨格から元の圏への包含。充満・忠実・本質的全射のインスタンスが Mathlib に登録済み
noncomputable def fromSkeleton (C : Type u₁) [Category.{v₁} C] : Skeleton C ⥤ C :=
  inducedFunctor _

end Recap

#check @CategoryTheory.skeletonEquivalence




example : Skeleton C ≌ C where
  functor := fromSkeleton
  inverse := {
    obj c := ⟦c⟧
    map {c c'} f := by
      #check Quotient.mk_out c
      apply InducedCategory.homMk

  }



-- 同値が反対圏に移ることを示す（同値不変性の例、本の番号なし）。
#check @CategoryTheory.Equivalence.op

example (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ := sorry

-- 命題1.5.13。連結亜圏が、その任意の対象の自己同型群と同値であることを示す。
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
