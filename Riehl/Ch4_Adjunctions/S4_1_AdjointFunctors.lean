import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Category.Cat.Adjunction
import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# 4.1 随伴関手

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 第4章の導入（自由ベクトル空間。Mathlib の `ModuleCat.adj`）、
記法4.1.5（Mathlib では `F ⊣ G` が `Adjunction F G` の記法）、例4.1.6（離散位相と密着位相。
`TopCat.adj₁`・`TopCat.adj₂`）、例4.1.7（天井と床。`Int.gc_ceil_coe`・`Int.gc_coe_floor`）、
例4.1.8（順像・逆像。`Set.image_preimage`・`Set.preimage_kernImage`）、例4.1.9（量化子）、
例4.1.10（自由 ⊣ 忘却。`MonCat.adj`・`AddCommGrpCat.adj`・`ModuleCat.adj`・`CommRingCat.adj`・
`GrpCat.adj`・`ModuleCat.extendRestrictScalarsAdj`）、例4.1.11（フロベニウス相互律）、
例4.1.12（体の忘却関手）、例4.1.13（箙上の自由圏。`Quiv.adj`）、例4.1.14（順序数の圏）、
例4.1.15（亜群の圏の包含。右随伴は `CategoryTheory.Core`）、脚注1〜4 は載せない。
演習4.1.iv（自由 R-加群の関手性）は例4.1.10(v) の構成の話なので載せない（`ModuleCat.free`）。
-/

open CategoryTheory Opposite

namespace Riehl

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義4.1.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
随伴とは、一対の関手 F : C → D と G : D → C に、各 c ∈ C と d ∈ D について指定された同型
Hom(Fc, d) ≅ Hom(c, Gd) であって、両変数について自然なものを添えたものである。

自然性は、Mathlib の `Adjunction.CoreHomEquiv` と同じ 2 つの射の等式で書く。f♯ : Fc → d と
k : d → d' について (k ∘ f♯)♭ = Gk ∘ f♭、h : c' → c と g♭ : c → Gd について
(g♭ ∘ h)♯ = g♯ ∘ Fh である。本文は後者を ♭ の向きの (f♯ ∘ Fh)♭ = f♭ ∘ h で書いている。
-/

#print Adjunction.CoreHomEquiv


-- 随伴 : c,d について自然な全単射 Hom(Fc, d) ≅ Hom(c, Gd)
structure Adjunction' (F : C ⥤ D) (G : D ⥤ C) where
  homEquiv : ∀ c d, (F.obj c ⟶ d) ≃ (c ⟶ G.obj d)
  homEquiv_naturality_left_symm : ∀ {c' c d} (h : c' ⟶ c) (g : c ⟶ G.obj d),
    (homEquiv c' d).symm (h ≫ g) = F.map h ≫ (homEquiv c d).symm g
  homEquiv_naturality_right : ∀ {c d d'} (f : F.obj c ⟶ d) (k : d ⟶ d'),
    homEquiv c d' (f ≫ k) = homEquiv c d f ≫ G.map k


-- c についての自然性を `e` の式で仮定し、`(e _ _).symm` の式で得る
theorem homEquiv_naturality_left_symm_of_naturality_left {F : C ⥤ D} {G : D ⥤ C}
    (e : ∀ c d, (F.obj c ⟶ d) ≃ (c ⟶ G.obj d))
    (he : ∀ {c' c d} (h : c' ⟶ c) (f : F.obj c ⟶ d), e c' d (F.map h ≫ f) = h ≫ e c d f)
    {c' c d} (h : c' ⟶ c) (g : c ⟶ G.obj d) :
    (e c' d).symm (h ≫ g) = F.map h ≫ (e c d).symm g := by
  rw [Equiv.symm_apply_eq]
  symm
  nth_rw 2 [<- Equiv.apply_symm_apply (e c d) g]
  apply he

-- d についての自然性を `e` の式で仮定し、`(e _ _).symm` の式で得る
theorem homEquiv_naturality_right_symm_of_naturality_right {F : C ⥤ D} {G : D ⥤ C}
    (e : ∀ c d, (F.obj c ⟶ d) ≃ (c ⟶ G.obj d))
    (he : ∀ {c d d'} (f : F.obj c ⟶ d) (k : d ⟶ d'), e c d' (f ≫ k) = e c d f ≫ G.map k)
    {c d d'} (g : c ⟶ G.obj d) (k : d ⟶ d') :
    (e c d').symm (g ≫ G.map k) = (e c d).symm g ≫ k := by
  rw [Equiv.symm_apply_eq]
  symm
  nth_rw 2 [<- Equiv.apply_symm_apply (e c d) g]
  apply he


-- 随伴の別の定義。自然同型 Hom(F-, -) ≅ Hom(-, G-)
def AdjunctionNatIso (F : C ⥤ D) (G : D ⥤ C) : Type _ :=
  F.op ⋙ coyoneda ≅ (G ⋙ yoneda).flip

-- 随伴の 2 つの定義の同値
def coreHomEquivEquivAdjunctionNatIso (F : C ⥤ D) (G : D ⥤ C) :
    Adjunction.CoreHomEquiv F G ≃ AdjunctionNatIso F G where
  toFun σ := {
    hom := {
      app c' := {
        app d := TypeCat.ofHom ((σ.homEquiv c'.unop d).toFun)
        naturality {d d'} f := by
          ext g; exact σ.homEquiv_naturality_right g f
      }
      naturality {c c'} f := by
        ext d g
        exact σ.homEquiv_naturality_left f.unop g
    }

    inv := {
      app c' := {
        app d := TypeCat.ofHom ((σ.homEquiv c'.unop d).invFun)
        naturality {d d'} f := by
          ext g
          simp only [Functor.comp_obj, Functor.op_obj, Functor.flip_obj_obj, yoneda_obj_obj,
            Functor.flip_obj_map, Functor.comp_map, yoneda_map_app, Equiv.invFun_as_coe,
            TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
            Adjunction.CoreHomEquiv.homEquiv_naturality_left_symm]
          rw [<- (σ.homEquiv c'.unop d').left_inv (F.map g ≫ (σ.homEquiv (G.obj d) d').symm (G.map f))]
          dsimp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe]
          rw [σ.homEquiv_naturality_left, Equiv.apply_symm_apply]
          rw [σ.homEquiv_naturality_right_symm]
      }
      naturality {c c'} f := by
        ext d g
        exact σ.homEquiv_naturality_left_symm f.unop g
    }
    hom_inv_id := by
      ext c d f; simp
    inv_hom_id := by
      ext c d f; simp
  }
  invFun σ := {
    homEquiv c d := {
      toFun f := ((σ.hom.app (Opposite.op c)).app d).hom f
      invFun g := ((σ.inv.app (Opposite.op c)).app d).hom g
      left_inv := by
        intro f
        dsimp only [Functor.flip_obj_obj, Functor.comp_obj, yoneda_obj_obj, Functor.op_obj]
        have E := σ.hom_inv_id_app (Opposite.op c)
        rw [<- comp_apply, <- NatTrans.comp_app, congr_app E d]
        simp
      right_inv := by
        intro g
        dsimp only [Functor.comp_obj, Functor.op_obj, Functor.flip_obj_obj, yoneda_obj_obj]
        have E :=  σ.inv_hom_id_app (Opposite.op c)
        rw [<- comp_apply, <- NatTrans.comp_app, congr_app E d]
        simp
    }
    homEquiv_naturality_left_symm {c' c d } f g:= by
      have E := σ.inv.naturality_app d f.op
      have := congr_arg (fun x => x.hom g) E
      erw [this]; simp

    homEquiv_naturality_right {c d d'} f g := by
      have E := (σ.hom.app (op c)).naturality g
      have := congr_arg (fun x => x.hom f) E
      erw [this]; simp
  }
  left_inv := by
    intro σ; rfl
  right_inv := by
    intro σ; rfl



#print Functor.hom
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題4.1.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
一対の関手 F : C → D, G : D → C と、すべての c ∈ C, d ∈ D について指定された同型
Hom(Fc, d) ≅ Hom(c, Gd) について、この同型の族が自然であることは、次と同値である。
任意の h : c → c', k : d → d', f♯ : Fc → d, g♯ : Fc' → d' について、四角形
k ∘ f♯ = g♯ ∘ Fh が D で可換であることと、転置した四角形 Gk ∘ f♭ = g♭ ∘ h が C で可換である
ことが同値である。

同値の 2 つの向きを別の宣言にする。証明は演習4.1.i である。
-/

#check Adjunction.homEquiv_naturality_left_square_iff

-- D の四角形の可換性と、転置した C の四角形の可換性が対応する
theorem Adjunction.CoreHomEquiv.homEquiv_naturality_left_square_iff {F : C ⥤ D} {G : D ⥤ C}
    (σ : Adjunction.CoreHomEquiv F G) {c c' : C} {d d' : D}
    (h : c ⟶ c') (k : d ⟶ d') (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d') :
     (F.map h ≫ g = f ≫ k) ↔ (h ≫ σ.homEquiv c' d' g = σ.homEquiv c d f ≫ G.map k) where
  mp H := by
    apply (σ.homEquiv c d').symm.injective
    rw [σ.homEquiv_naturality_left_symm, σ.homEquiv_naturality_right_symm]
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, H]
  mpr H := by
    apply (σ.homEquiv c d').injective
    rw [σ.homEquiv_naturality_left, H, σ.homEquiv_naturality_right]




-- 四角形の可換性が対応する全単射の族は、随伴をなす
def coreHomEquivOfSquareIff {F : C ⥤ D} {G : D ⥤ C}
    (e : ∀ c d, (F.obj c ⟶ d) ≃ (c ⟶ G.obj d))
    (he : ∀ {c c' d d'} (h : c ⟶ c') (k : d ⟶ d') (f : F.obj c ⟶ d) (g : F.obj c' ⟶ d'),
      (h ≫ e c' d' g = e c d f ≫ G.map k) ↔ (F.map h ≫ g = f ≫ k)) :
    Adjunction.CoreHomEquiv F G where
  homEquiv := e
  homEquiv_naturality_left_symm {c c' d} h g := by
    symm
    rw [<- Category.comp_id ((e c d).symm (h ≫ g)), <- he]
    rw [Equiv.apply_symm_apply, G.map_id, Category.comp_id, Equiv.apply_symm_apply]
  homEquiv_naturality_right {c d d'} f k := by
    rw [<- Category.id_comp ((e c d') (f≫ k)), he]
    simp



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 随伴三つ組
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
3 つの関手 F, G, H が一対の随伴 F ⊣ G と G ⊣ H を定めるとき、このデータを随伴三つ組と呼ぶ。

Mathlib の `Adjunction.Triple` は 2 つの随伴を 4.2 の形の `Adjunction` で持つ。ここでは
`Adjunction.CoreHomEquiv` で持つ。
-/

#print Adjunction.Triple

-- 随伴三つ組 F ⊣ G ⊣ H
structure AdjointTriple (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ D) where
  σ : Adjunction.CoreHomEquiv F G
  τ : Adjunction.CoreHomEquiv G H

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ガロア接続
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
前順序集合 A, B の間の随伴 F ⊣ G をガロア接続と呼ぶ。随伴 F ⊣ G は、すべての a ∈ A と b ∈ B に
ついて Fa ≤ b ⇔ a ≤ Gb が成り立つことを主張する。

前順序集合は圏、順序を保つ写像は関手である（演習1.3.ii。Mathlib の `Monotone.functor`）。
Mathlib の `GaloisConnection l u` は ∀ a b, l a ≤ b ↔ a ≤ u b である。
-/

section
variable {A : Type u₁} {B : Type u₂} [Preorder A] [Preorder B]

#check Monotone.functor
#check GaloisConnection
#check Adjunction.gc

-- 前順序集合の間の随伴はガロア接続である
theorem galoisConnection_of_coreHomEquiv {F : A ⥤ B} {G : B ⥤ A}
    (σ : Adjunction.CoreHomEquiv F G) : GaloisConnection F.obj G.obj :=
  sorry

#check GaloisConnection.adjunction

-- ガロア接続は前順序集合の間の随伴である
def coreHomEquivOfGaloisConnection {f : A → B} {g : B → A} (hf : Monotone f) (hg : Monotone g)
    (gc : GaloisConnection f g) : Adjunction.CoreHomEquiv hf.functor hg.functor :=
  sorry

end

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.1.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題4.1.3 を証明せよ。宣言は補題4.1.3 のセクションの
-- `Adjunction.CoreHomEquiv.homEquiv_naturality_left_square_iff` と `coreHomEquivOfSquareIff` である。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.1.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
(i) ob : Cat → Set と (ii) V : Quiver → Set の左随伴と右随伴を定めよ。V : Graph → Set は
左随伴または右随伴を持つか。

ob は Mathlib の `Cat.objects`、V は `Quiv` の頂点の集合を取る関手で、後者は本にも Mathlib にも
名前がないのでここで置く。Graph についての問いは、答えが随伴の有無そのものなので置かない。
-/

#check Cat.objects
#check typeToCat
#check Cat.typeToCatObjectsAdj

-- ob : Cat → Set の左随伴。Mathlib の `typeToCat` と同じ形
def obLeftAdjoint : Type u₁ ⥤ Cat.{u₁, u₁} :=
  sorry

def obLeftAdjointCoreHomEquiv : Adjunction.CoreHomEquiv typeToCat.{u₁} Cat.objects :=
  sorry

-- ob : Cat → Set の右随伴
def obRightAdjoint : Type u₁ ⥤ Cat.{u₁, u₁} :=
  sorry

def obRightAdjointCoreHomEquiv : Adjunction.CoreHomEquiv Cat.objects obRightAdjoint.{u₁} :=
  sorry

#check Quiv

-- V : Quiver → Set。Q ↦ Q の頂点の集合
def Quiv.vertices : Quiv.{u₁, u₁} ⥤ Type u₁ :=
  sorry

-- V : Quiver → Set の左随伴
def verticesLeftAdjoint : Type u₁ ⥤ Quiv.{u₁, u₁} :=
  sorry

def verticesLeftAdjointCoreHomEquiv :
    Adjunction.CoreHomEquiv verticesLeftAdjoint.{u₁} Quiv.vertices :=
  sorry

-- V : Quiver → Set の右随伴
def verticesRightAdjoint : Type u₁ ⥤ Quiv.{u₁, u₁} :=
  sorry

def verticesRightAdjointCoreHomEquiv :
    Adjunction.CoreHomEquiv Quiv.vertices verticesRightAdjoint.{u₁} :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.1.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の随伴三つ組 L ⊣ U ⊣ R から、誘導される自己関手の間の標準的な随伴 LU ⊣ RU と
UL ⊣ UR が生じることを示せ。

statement の項 := 本の記法
  U ⋙ L   := LU
  U ⋙ R   := RU
  L ⋙ U   := UL
  R ⋙ U   := UR
-/

#check Adjunction.comp

-- LU ⊣ RU
def compLeftOfTriple {L : C ⥤ D} {U : D ⥤ C} {R : C ⥤ D}
    (σ : Adjunction.CoreHomEquiv L U) (τ : Adjunction.CoreHomEquiv U R) :
    Adjunction.CoreHomEquiv (U ⋙ L) (U ⋙ R) where
  homEquiv d d' := (σ.homEquiv (U.obj d) d').trans  (τ.homEquiv d (U.obj d'))
  homEquiv_naturality_left_symm {x x' y} f g := by
    dsimp only [Functor.comp_obj, Equiv.symm_trans, Equiv.trans_apply, Functor.comp_map]
    rw [τ.homEquiv_naturality_left_symm, σ.homEquiv_naturality_left_symm]
  homEquiv_naturality_right {x y y'} f g := by
    dsimp only [Functor.comp_obj, Equiv.trans_apply, Functor.comp_map]
    erw [σ.homEquiv_naturality_right, τ.homEquiv_naturality_right]


-- UL ⊣ UR
def compRightOfTriple {L : C ⥤ D} {U : D ⥤ C} {R : C ⥤ D}
    (σ : Adjunction.CoreHomEquiv L U) (τ : Adjunction.CoreHomEquiv U R) :
    Adjunction.CoreHomEquiv (L ⋙ U) (R ⋙ U) where
  homEquiv c c' := (τ.homEquiv (L.obj c) c').trans (σ.homEquiv c (R.obj c'))
  homEquiv_naturality_left_symm {a b c} f g := by
    dsimp only [Functor.comp_obj, Equiv.symm_trans, Equiv.trans_apply, Functor.comp_map]
    rw [σ.homEquiv_naturality_left_symm, τ.homEquiv_naturality_left_symm]
  homEquiv_naturality_right {a b c} f g := by
    dsimp only [Functor.comp_obj, Equiv.trans_apply, Functor.comp_map]
    rw [τ.homEquiv_naturality_right, σ.homEquiv_naturality_right]



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習1.3.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
関手 F : D → C と G : E → C について、コンマ圏 F ↓ G から D と E への射影関手
dom : F ↓ G → D と cod : F ↓ G → E がある。

コンマ圏 F ↓ G そのものは Mathlib の `Comma F G` を使う。
-/

#check Comma.fst

-- dom : F ↓ G → D
def commaDom {E : Type*} [Category E] (F : D ⥤ C) (G : E ⥤ C) : Comma F G ⥤ D where
  obj := Comma.left
  map := CommaMorphism.left
  map_id f := by simp
  map_comp H I := by simp




#check Comma.snd

-- cod : F ↓ G → E
def commaCod {E : Type*} [Category E] (F : D ⥤ C) (G : E ⥤ C) : Comma F G ⥤ E := sorry


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.1.v
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
F : C ⇄ D : G が随伴関手で F ⊣ G ならば、F と G および C と D の恒等関手から作るコンマ圏
F ↓ D と C ↓ G は、演習1.3.vi の C × D への忘却関手と両立する同型で同型である。

圏の同型は `Cat` の対象の間の同型で書く。`Cat` の射は関手を包んだ構造で、`toFunctor` で関手に
戻す。忘却関手との両立は、同型の射を各成分の忘却関手と合成した等式 2 つで書く。

statement の項 := 本の記法
  Comma F (𝟭 D)           := F ↓ D
  Comma (𝟭 C) G           := C ↓ G
  Comma.fst F (𝟭 D)       := F ↓ D → C, (c, d, f) ↦ c
  Comma.snd F (𝟭 D)       := F ↓ D → D, (c, d, f) ↦ d
-/

#print Comma
#check Comma.fst
#check Comma.snd
#check Cat.of
#check Cat.Hom.toFunctor

#print CostructuredArrow

-- F ↓ D ≅ C ↓ G
def commaIsoOfCoreHomEquiv {F : C ⥤ D} {G : D ⥤ C} (σ : Adjunction.CoreHomEquiv F G) :
    Cat.of (Comma F (𝟭 D)) ≅ Cat.of (Comma (𝟭 C) G) where
  hom := ⟨{
    obj f := Comma.mk f.left f.right (σ.homEquiv f.left f.right f.hom)
    map {f g} H := {
      left := H.left
      right := H.right
      w := by
        simp only [Functor.id_obj, Functor.id_map]
        erw [<- σ.homEquiv_naturality_right, <- H.w, σ.homEquiv_naturality_left]
    }
    map_id x := by
      apply Comma.hom_ext<;> simp
    map_comp {f g h} H I := by
      apply Comma.hom_ext<;> simp
  }⟩
  inv := ⟨{
    obj f := Comma.mk f.left f.right ((σ.homEquiv f.left f.right).symm f.hom)
    map {f g} H := {
      left := H.left
      right := H.right
      w := by
        dsimp only [Functor.id_obj, Functor.id_map]
        erw [<- σ.homEquiv_naturality_right_symm, <- H.w, σ.homEquiv_naturality_left_symm]
        simp
    }
    map_id f := by
      apply Comma.hom_ext<;> simp
    map_comp f g := by
      apply Comma.hom_ext<;> simp
  }⟩
  hom_inv_id := by
    ext; simp only [Cat.of_α, Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor]
    apply CategoryTheory.Functor.ext ?_ ?_
    · intro f; simp
    · intro f g σ; simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
      apply Comma.hom_ext<;> simp
  inv_hom_id := by
    ext; simp only [Cat.of_α, Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor]
    apply CategoryTheory.Functor.ext ?_ ?_
    · intro f; simp
    · intro f g σ; simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
      apply Comma.hom_ext<;> simp




-- 同型は C への忘却関手と両立する
theorem commaIsoOfCoreHomEquiv_fst {F : C ⥤ D} {G : D ⥤ C} (σ : Adjunction.CoreHomEquiv F G) :
    (commaIsoOfCoreHomEquiv σ).hom.toFunctor ⋙ Comma.fst (𝟭 C) G = Comma.fst F (𝟭 D) := by
  apply CategoryTheory.Functor.ext ?_ ?_
  · intro f; simp only [Cat.of_α, Functor.comp_obj, Comma.fst_obj, commaIsoOfCoreHomEquiv]
  · intro f g H
    simp only [Cat.of_α, Functor.comp_obj, Comma.fst_obj, Functor.comp_map, Comma.fst_map, commaIsoOfCoreHomEquiv]
    rw [eqToHom_refl, Category.id_comp]
    erw [Category.comp_id]






-- 同型は D への忘却関手と両立する
theorem commaIsoOfCoreHomEquiv_snd {F : C ⥤ D} {G : D ⥤ C} (σ : Adjunction.CoreHomEquiv F G) :
    (commaIsoOfCoreHomEquiv σ).hom.toFunctor ⋙ Comma.snd (𝟭 C) G = Comma.snd F (𝟭 D) :=
  sorry

end Riehl
