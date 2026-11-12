import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# 4.2 普遍射としての単位と余単位

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 節冒頭の引用、例4.2.4（自由群の単位と余単位。Mathlib の `GrpCat.adj`）、
Remark 4.2.6（三角等式の読み方）、脚注5、系4.2.10 の後の順像・逆像の例（`Set.image_preimage`）は
載せない。
-/

open CategoryTheory Limits

namespace Riehl

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題4.2.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
随伴 F ⊣ G が与えられたとき、c での成分 η_c : c → GFc を恒等射 1_{Fc} の転置と定めると、
自然変換 η : id_C ⇒ GF が得られる。これを随伴の単位と呼ぶ。

随伴は 4.1 の形 `Adjunction.CoreHomEquiv` で与える。
-/

-- 単位 η : id_C ⇒ GF
def unitOfCoreHomEquiv {F : C ⥤ D} {G : D ⥤ C} (σ : Adjunction.CoreHomEquiv F G) :
    𝟭 C ⟶ F ⋙ G where
  app c := σ.homEquiv c (F.obj c) (𝟙 (F.obj c))
  naturality {c c'} f := by
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
    rw [<- σ.homEquiv_naturality_right, Category.id_comp]
    rw [<- σ.homEquiv_naturality_left, Category.comp_id]


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題4.2.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
随伴 F ⊣ G が与えられたとき、d での成分 ε_d : FGd → d を恒等射 1_{Gd} の転置と定めると、
自然変換 ε : FG ⇒ id_D が得られる。これを随伴の余単位と呼ぶ。
-/

-- 余単位 ε : FG ⇒ id_D
def counitOfCoreHomEquiv {F : C ⥤ D} {G : D ⥤ C} (σ : Adjunction.CoreHomEquiv F G) :
    G ⋙ F ⟶ 𝟭 D where
  app d := (σ.homEquiv (G.obj d) d).symm (𝟙 (G.obj d))
  naturality {d d'} f := by
    simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map]
    rw [<- σ.homEquiv_naturality_left_symm, <- σ.homEquiv_naturality_right_symm]
    simp


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義4.2.5
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
随伴とは、一対の関手 F : C → D と G : D → C に、自然変換 η : id_C ⇒ GF と ε : FG ⇒ id_D で
あって三角等式 εF ⋅ Fη = 1_F と Gε ⋅ ηG = 1_G を満たすものを添えたものである。

三角等式は成分ごとの等式 ε_{Fc} ∘ F(η_c) = 1_{Fc} と G(ε_d) ∘ η_{Gd} = 1_{Gd} で書く。
Mathlib の `F ⊣ G` は `Adjunction F G` の記法で、この定義の形をしている。
-/

#check Adjunction

-- 随伴。単位、余単位、2 つの三角等式
structure AdjunctionII (F : C ⥤ D) (G : D ⥤ C) where
  unit : 𝟭 C ⟶ F ⋙ G
  counit : G ⋙ F ⟶ 𝟭 D
  -- μF ≫ Fε = 𝟙 F
  left_triangle_components :
    ∀ c, F.map (unit.app c) ≫ counit.app (F.obj c) = 𝟙 (F.obj c)
  -- Gμ ≫ εG = 𝟙 G
  right_triangle_components :
    ∀ d, unit.app (G.obj d) ≫ G.map (counit.app d) = 𝟙 (G.obj d)

-- example (F : C ⥤ D) (G : D ⥤ C) (σ : F ⊣ G) : sorry := by
--   let μ := σ.unit
--   let ε := σ.counit
--   let μF : F ⟶ F ⋙ G ⋙ F := Functor.whiskerRight μ F
--   let Fε : F ⋙ G ⋙ F ⟶ F := F.whiskerLeft ε
--   let Gμ : G ⟶ G ⋙ F ⋙ G := G.whiskerLeft μ
--   let εG : G ⋙ F ⋙ G ⟶ G := Functor.whiskerRight ε G
--   #check Functor.whiskerRight σ.unit F ≫ F.whiskerLeft σ.counit = 𝟙 F
--   #check G.whiskerLeft σ.unit ≫ Functor.whiskerRight σ.counit G = 𝟙 G




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理4.2.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
一対の関手 F : C → D と G : D → C について、随伴 F ⊣ G のデータは次のどれによっても同値に
与えられる。
(i) すべての c ∈ C と d ∈ D についての同型 Hom(Fc, d) ≅ Hom(c, Gd) の自然な族
(ii) 自然変換 η : id_C ⇒ GF と ε : FG ⇒ id_D であって、三角等式を満たすもの
(iii) 自然変換 η : id_C ⇒ GF であって、Fc → d の射 f を Gf ∘ η_c に送る写像 (4.2.8)
  Hom(Fc, d) → Hom(c, Gd) が、すべての c ∈ C と d ∈ D について同型であるもの
(iv) 自然変換 ε : FG ⇒ id_D であって、c → Gd の射 g を ε_d ∘ Fg に送る写像 (4.2.9)
  Hom(c, Gd) → Hom(Fc, d) が、すべての c ∈ C と d ∈ D について同型であるもの
(v) 自然変換 η : id_C ⇒ GF であって、すべての c ∈ C について、成分 η_c がコンマ圏 c ↓ G の
  始対象であるもの
(vi) 自然変換 ε : FG ⇒ id_D であって、すべての d ∈ D について、成分 ε_d がコンマ圏 F ↓ d の
  終対象であるもの

(i) は `Adjunction.CoreHomEquiv F G`、(ii) は `F ⊣ G` である。(iii) と (iv) の条件を、本文は
定理の直後で、自然変換 Hom(F-, -) ⇒ Hom(-, G-) と Hom(-, G-) ⇒ Hom(F-, -) の可逆性と言い直して
いる。宣言ではこの形で書く。この 2 つの自然変換は `homNatTransOfUnit` と `homNatTransOfCounit`
で、矢印の宣言より前に置く。

宣言は次の図の矢印ごとに置く。点線の矢印 n' は、実線の矢印 n の双対である。

  (v) ←───5────┐  ┌┄┄┄5'┄┄→ (vi)
   │ 4         │  ┆          ┆ 4'
   ↓           │  ┆          ↓
  (iii) ←──2───(ii) ┄┄2'┄┄→ (iv)
   │           1↑            ┆
   │            │            ┆
   └────3────→ (i) ←┄┄┄┄3'┄┄┄┘

本文の証明が示すのは 1、2、2'、3、3' と、4 と 4' の両向きである。本文は 4 と 4' を c または d
ごとに示す。宣言では、(iii) と (iv) の条件を自然変換全体の可逆性で書くのに合わせて、すべての c
または d についての条件と結ぶ。4 と 4' の逆向きは宣言にせず、(v) と (vi) は 5 と 5' で (ii) から
得る。5 と 5' は本文の証明には現れない。2 と 2' は 1 つの宣言にする。双対の 3'、4'、5' の宣言は
最後にまとめて置く。
本文の証明の最後の段（(i) と (ii) の間の構成が互いに逆であること）は宣言にしない。

statement の項 := 本の記法
  F.op ⋙ coyoneda                             := c ↦ Hom(Fc, -)
  (G ⋙ yoneda).flip                           := c ↦ Hom(c, G-)
  StructuredArrow c G                         := c ↓ G
  StructuredArrow.mk (η.app c)                := c ↓ G の対象 (Fc, η_c : c → GFc)
  CostructuredArrow F d                       := F ↓ d
  CostructuredArrow.mk (ε.app d)              := F ↓ d の対象 (Gd, ε_d : FGd → d)
-/

#check Adjunction.mkOfHomEquiv

-- 補題4.2.2 の単位と補題4.2.3 の余単位は三角等式を満たす（矢印 1、(i) ⇒ (ii)）
def adjunctionOfCoreHomEquiv {F : C ⥤ D} {G : D ⥤ C} (σ : Adjunction.CoreHomEquiv F G) :
    F ⊣ G where
  unit := unitOfCoreHomEquiv σ
  counit := counitOfCoreHomEquiv σ
  left_triangle_components c := by
    simp only [unitOfCoreHomEquiv, counitOfCoreHomEquiv]
    erw [<- σ.homEquiv_naturality_left_symm, Category.comp_id]
    erw [Equiv.apply_symm_apply]
  right_triangle_components d := by
    simp only [unitOfCoreHomEquiv, counitOfCoreHomEquiv]
    erw [<- σ.homEquiv_naturality_right, Category.id_comp, Equiv.apply_symm_apply]



-- (4.2.8) unit から構成する自然変換 : Hom(F-, -) ⟶ Hom(-, G-)
def homNatTransOfUnit {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G) :
    F.op ⋙ coyoneda ⟶ (G ⋙ yoneda).flip where
  app c := {
    app d := TypeCat.ofHom <| fun f => η.app c.unop ≫ G.map f
    naturality {d d'} f := by
      ext g; simp
  }
  naturality {c c'} f := by
    ext d g; dsimp
    have E := η.naturality f.unop
    dsimp at E
    rw [<- Category.assoc, E]
    simp



-- (4.2.9) counitから高瀬雨する自然変換 Hom(-, G-) ⇒ Hom(F-, -)
def homNatTransOfCounit {F : C ⥤ D} {G : D ⥤ C} (ε : G ⋙ F ⟶ 𝟭 D) :
    (G ⋙ yoneda).flip ⟶ F.op ⋙ coyoneda where
  app c := {
    app d := TypeCat.ofHom <| fun g => F.map g ≫ ε.app d
    naturality {d d'} g := by
      ext f; dsimp only [Functor.flip_obj_obj, Functor.comp_obj, yoneda_obj_obj, Functor.op_obj,
        Functor.flip_obj_map, Functor.comp_map, yoneda_map_app, TypeCat.Fun.toFun_apply,
        types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
      rw [F.map_comp, Category.assoc, Category.assoc]
      congr 1
      exact ε.naturality g
  }
  naturality {c c'} f := by
    ext d g; simp


#check Adjunction.compCoyonedaIso

-- 随伴の単位と余単位について、(4.2.8) と (4.2.9) の自然変換は互いに逆
-- （矢印 2 と 2'、(ii) ⇒ (iii) と (iv)）
def homNatIsoOfAdjunction {F : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) :
    F.op ⋙ coyoneda ≅ (G ⋙ yoneda).flip where
  hom := homNatTransOfUnit σ.unit
  inv := homNatTransOfCounit σ.counit
  hom_inv_id := by
    simp only [homNatTransOfUnit, homNatTransOfCounit]
    ext c d f; dsimp only [Functor.comp_obj, Functor.op_obj, Functor.flip_obj_obj, yoneda_obj_obj,
      NatTrans.comp_app, TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, NatTrans.id_app, types_id_apply]
    have E := σ.counit.naturality f;
    dsimp only [Functor.op_obj, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
      Functor.id_map] at E
    have E' := σ.left_triangle_components (Opposite.unop c)
    rw [F.map_comp, Category.assoc, E, <- Category.assoc, E']
    simp
  inv_hom_id := by
    simp only [homNatTransOfUnit, homNatTransOfCounit]
    ext c d g; dsimp only [Functor.flip_obj_obj, Functor.comp_obj, yoneda_obj_obj, Functor.op_obj,
      NatTrans.comp_app, TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, NatTrans.id_app, types_id_apply]
    have E := σ.unit.naturality g
    dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at E
    rw [G.map_comp, <- Category.assoc, <- E, Category.assoc, σ.right_triangle_components]
    simp




-- (4.2.8) の自然変換が同型である η の定める、(i) の同型の自然な族（矢印 3、(iii) ⇒ (i)）
noncomputable def coreHomEquivOfIsIsoHomNatTransOfUnit {F : C ⥤ D} {G : D ⥤ C}
    (η : 𝟭 C ⟶ F ⋙ G) [IsIso (homNatTransOfUnit η)] : Adjunction.CoreHomEquiv F G where
  homEquiv c d := (((asIso (homNatTransOfUnit η)).app (Opposite.op c)).app d).toEquiv
  homEquiv_naturality_left_symm {c c' d} f g := by
    have E := (asIso (homNatTransOfUnit η)).inv.naturality f.op
    have E' := congr_arg (fun x => x.hom g ) (congr_app E d)
    dsimp at E'
    exact E'
  homEquiv_naturality_right {c d d'} f g := by
    have E := ((asIso (homNatTransOfUnit η)).app (Opposite.op c)).hom.naturality g
    exact congr_arg (fun x => x.hom f) E



#check StructuredArrow.mk
/-
  c ↓ G　:= StructuedArrow c G
    :: c ⟶ G.obj _ という型の圏
  IsInitial (StructuredArrow.mk (η.app c))
    :: η.app c : c ⟶ G.obj (F.obj c) がc ↓ Gの始対象

-/
-- すべての c で η_c が c ↓ G の始対象ならば、(4.2.8) の自然変換は同型
-- （矢印 4、(v) ⇒ (iii)）
theorem isIso_homNatTransOfUnit_of_isInitial {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (h : ∀ c, IsInitial (StructuredArrow.mk (η.app c) : StructuredArrow c G)) :
    IsIso (homNatTransOfUnit η) := by
  let f : (G ⋙ yoneda).flip ⟶ F.op ⋙ coyoneda := {
    app c := {
      app d := TypeCat.ofHom <| fun f => ((h c.unop).to (StructuredArrow.mk f)).right
      naturality {d d'} f := by
        ext g
        simp only [Functor.comp_obj, Functor.op_obj, Functor.flip_obj_obj, yoneda_obj_obj,
          Functor.flip_obj_map, Functor.comp_map, yoneda_map_app, TypeCat.Fun.toFun_apply,
          comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
        set a := ((h (Opposite.unop c)).to (StructuredArrow.mk g))
        set b := ((h (Opposite.unop c)).to (StructuredArrow.mk (g ≫ G.map f)))
        let k : (StructuredArrow.mk g : StructuredArrow c.unop G) ⟶
          StructuredArrow.mk (g ≫ G.map f) := {
          left := 𝟙 _
          right := f
          w := by simp
        }
        have : b = a ≫ k := (h c.unop).hom_ext _ _
        exact congr_arg (fun x => x.right) this
    }
    naturality {c c'} f := by
      ext d g
      set a := (h (Opposite.unop c')).to (StructuredArrow.mk (f.unop ≫ g))
      set b := ((h (Opposite.unop c)).to (StructuredArrow.mk g))
      have Hb := b.w; dsimp at Hb
      let k : (StructuredArrow.mk (η.app (Opposite.unop c')) : StructuredArrow (Opposite.unop c') G)
        ⟶  (StructuredArrow.mk (f.unop ≫ g) : StructuredArrow (Opposite.unop c') G) := {
        left := 𝟙 _
        right := F.map f.unop ≫ b.right
        w := by
          simp only [StructuredArrow.mk_left, Functor.const_obj_obj, StructuredArrow.mk_right,
            Discrete.functor_map_id, StructuredArrow.mk_hom_eq_self, Category.id_comp,
            Functor.map_comp]
          erw [<- Category.assoc, <- η.naturality f.unop, Category.assoc, Hb]
          simp
      }
      have : a = k := (h c'.unop).hom_ext _ _
      exact congr_arg (fun x => x.right) this
  }
  use f; constructor
  · ext c d g
    let a : (StructuredArrow.mk (η.app (Opposite.unop c)) : StructuredArrow (Opposite.unop c) G)⟶
            StructuredArrow.mk ((ConcreteCategory.hom (((homNatTransOfUnit η).app c).app d)) g) := {
      left := 𝟙 _
      right := g
      w := by simp [homNatTransOfUnit]
    }
    have :
      (h c.unop ).to
      (StructuredArrow.mk ((ConcreteCategory.hom (((homNatTransOfUnit η).app c).app d)) g))
      = a := (h (Opposite.unop c)).hom_ext _ _
    exact congr_arg (fun x => x.right) this
  · ext c d g
    exact ((h (Opposite.unop c)).to (StructuredArrow.mk g)).w



#check Adjunction.homEquiv_symm_unit

-- 単位の成分 η_c : c → GFc の転置は 1_{Fc}
theorem homEquiv_symm_unit' {F : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (c : C) :
    (σ.homEquiv c (F.obj c)).symm (σ.unit.app c) = 𝟙 (F.obj c) := by
  rw [σ.homEquiv_symm_apply, σ.left_triangle_components]


#check mkInitialOfLeftAdjoint

-- 随伴の単位の成分 η_c は c ↓ G の始対象（矢印 5、(ii) ⇒ (v)）
def unitIsInitial {F : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (c : C) :
    IsInitial (StructuredArrow.mk (σ.unit.app c) : StructuredArrow c G) := by
  apply IsInitial.ofUniqueHom ?_ ?_
  · intro f
    refine {
      left := 𝟙 _
      right := (σ.homEquiv c f.right).invFun f.hom
      w := by
        simp only [StructuredArrow.mk_left, Functor.const_obj_obj, Discrete.functor_map_id,
          Category.id_comp, StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self,
          Equiv.invFun_as_coe]
        rw [σ.homEquiv_symm_apply, G.map_comp, σ.unit_naturality_assoc f.hom,  σ.right_triangle_components]
        simp
    }

-- 以下は双対（矢印 3'、4'、5'）

-- (4.2.9) の自然変換が同型である ε の定める、(i) の同型の自然な族（矢印 3'、(iv) ⇒ (i)）
noncomputable def coreHomEquivOfIsIsoHomNatTransOfCounit {F : C ⥤ D} {G : D ⥤ C}
    (ε : G ⋙ F ⟶ 𝟭 D) [IsIso (homNatTransOfCounit ε)] : Adjunction.CoreHomEquiv F G :=
  sorry

-- すべての d で ε_d が F ↓ d の終対象ならば、(4.2.9) の自然変換は同型
-- （矢印 4'、(vi) ⇒ (iv)）
theorem isIso_homNatTransOfCounit_of_isTerminal {F : C ⥤ D} {G : D ⥤ C} (ε : G ⋙ F ⟶ 𝟭 D)
    (h : ∀ d, IsTerminal (CostructuredArrow.mk (ε.app d) : CostructuredArrow F d)) :
    IsIso (homNatTransOfCounit ε) :=
  sorry

#check mkTerminalOfRightAdjoint

-- 随伴の余単位の成分 ε_d は F ↓ d の終対象（矢印 5'、(ii) ⇒ (vi)）
def counitIsTerminal {F : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (d : D) :
    IsTerminal (CostructuredArrow.mk (σ.counit.app d) : CostructuredArrow F d) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系4.2.10
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
A と B が半順序集合で、F : A → B と G : B → A が随伴 F ⊣ G をなすならば、FGF = F と
GFG = G が成り立つ。

半順序集合は圏、順序を保つ写像は関手である。2 つの等式は対象ごとの等式で書く。
-/

section

variable {A : Type u₁} {B : Type u₂} [PartialOrder A] [PartialOrder B]

#check GaloisConnection.l_u_l_eq_l

-- FGF = F
theorem map_map_map_eq_left {F : A ⥤ B} {G : B ⥤ A} (σ : F ⊣ G) (a : A) :
    F.obj (G.obj (F.obj a)) = F.obj a :=
  sorry

#check GaloisConnection.u_l_u_eq_u

-- GFG = G
theorem map_map_map_eq_right {F : A ⥤ B} {G : B ⥤ A} (σ : F ⊣ G) (b : B) :
    G.obj (F.obj (G.obj b)) = G.obj b :=
  sorry

end

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題4.2.11
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
随伴 F ⊣ G の関手 F : C → D と G : D → C は、単位の成分 η_c が同型である対象 c ∈ C の張る
充満部分圏と、余単位の成分 ε_d が同型である対象 d ∈ D の張る充満部分圏の間の圏同値に制限
される。

本文の証明が確かめる 2 つの主張（F と G が部分圏を部分圏に送ること）と、圏同値を、別の宣言に
する。

statement の項 := 本の記法
  ObjectProperty.FullSubcategory fun c => IsIso (σ.unit.app c)
    := η_c が同型である対象 c ∈ C の張る充満部分圏
  ObjectProperty.FullSubcategory fun d => IsIso (σ.counit.app d)
    := ε_d が同型である対象 d ∈ D の張る充満部分圏
-/

-- η_c が同型ならば ε_{Fc} は同型
theorem isIso_counit_app_obj_of_isIso_unit_app {F : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (c : C)
    [IsIso (σ.unit.app c)] : IsIso (σ.counit.app (F.obj c)) :=
  sorry

-- ε_d が同型ならば η_{Gd} は同型
theorem isIso_unit_app_obj_of_isIso_counit_app {F : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (d : D)
    [IsIso (σ.counit.app d)] : IsIso (σ.unit.app (G.obj d)) :=
  sorry

-- F と G の制限が定める、2 つの充満部分圏の間の圏同値
def fullSubcategoryEquivalenceOfAdjunction {F : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) :
    (ObjectProperty.FullSubcategory fun c => IsIso (σ.unit.app c)) ≌
      (ObjectProperty.FullSubcategory fun d => IsIso (σ.counit.app d)) :=
  sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.2.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題4.2.2 の主張を補題4.2.3 の主張に書き換える段階を説明する問題で、説明すること自体が
-- 解答なので宣言を置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.2.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 例4.1.10 の忘却関手を 1 つ選んで左随伴、単位、余単位を定義する問題で、どの関手を選ぶかが
-- 解答に含まれるので宣言を置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.2.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
F : A → B と G : B → A を前順序集合の間の順序を保つ写像とするとき、次の 2 つは同値である。
(i) すべての a ∈ A と b ∈ B について、Fa ≤ b と a ≤ Gb が同値である。
(ii) すべての a ∈ A について a ≤ G(Fa) であり、すべての b ∈ B について F(Gb) ≤ b である。
-/

-- (i) ⇔ (ii)
theorem le_iff_le_iff_le_and_le {A : Type u₁} {B : Type u₂} [Preorder A] [Preorder B]
    {f : A → B} {g : B → A} (hf : Monotone f) (hg : Monotone g) :
    (∀ a b, f a ≤ b ↔ a ≤ g b) ↔ ((∀ a, a ≤ g (f a)) ∧ (∀ b, f (g b) ≤ b)) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.2.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 随伴の厳密な射の 3 つの条件の同値を示す問題。条件が関手の等式 KF = F′H と HG = G′K を
-- 前提にしていて、3 つの条件の両辺の型をこの等式で書き換える必要があるので、宣言を置かない。

end Riehl
