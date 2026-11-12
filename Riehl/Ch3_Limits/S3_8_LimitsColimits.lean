import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.ColimitLimit
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Basic.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# 3.8 極限と余極限の相互作用

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 定理3.8.1 の直後の等化子と引き戻しの例、注意3.8.5（解析学での直接の
証明）、例3.8.6（下極限と上極限）、例3.8.8（フィルター圏の例）、脚注22（κ-フィルター圏。
Mathlib の `IsCardinalFiltered`）は載せない。(3.8.2) の余極限の四角形は、極限の四角形の双対
なので載せない。定理3.8.9 の後の、代数理論のモデルの圏についての段落は、定理5.6.5 に依存する
ので載せない。
-/

open CategoryTheory Limits Functor

namespace Riehl

universe v u

variable {I J : Type v} [SmallCategory I] [SmallCategory J] {C : Type u} [Category.{v} C]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.8.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
図式 F : I × J → C に付随する繰り返し極限 limit (i ↦ limit F(i, -)) と
limit (j ↦ limit F(-, j)) が C に存在するならば、両者は同型であり、極限 limit F を定める。

statement に現れる項が表す図式:
  curry.obj F ⋙ lim                                   := i ↦ limit F(i, -)
  CategoryTheory.Prod.swap J I ⋙ F                    := (j, i) ↦ F(i, j)
  curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim  := j ↦ limit F(-, j)

本は各 i ∈ I で limit F(i, -) が存在することを仮定する。`lim` は C がすべての J 型の極限を
持つことを要求するので、宣言はそちらを仮定している。
-/

/-
以下の 5 つは本にない。Mathlib が `isLimitConeOfHasLimitCurryCompLim` の証明に使う定義で、
同じ形で組む。
-/

#print DiagramOfCones
#print Cone.postcompose
#print limMap
#print IsLimit.map

-- `G ⋙ lim` を `lim` を使わずに書き下した構造。
-- `obj i` が lim G(i, -)、`map f` が lim(G f)
structure DiagramOfCones' (G : I ⥤ J ⥤ C) where
  obj : ∀ i : I, Cone (G.obj i)
  -- Cone.postcompose (G.map f) : Cone (G i) ⥤ Cone (G i')
  map : ∀ {i i' : I} (f : i ⟶ i'), (Cone.postcompose (G.map f)).obj (obj i) ⟶ obj i'
  id : ∀ i : I, (map (𝟙 i)).hom = 𝟙 _ := by cat_disch
  comp : ∀ {i₁ i₂ i₃ : I} (f : i₁ ⟶ i₂) (g : i₂ ⟶ i₃),
    (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom := by cat_disch



#check DiagramOfCones.conePoints

-- D の錐の頂点と、頂点の間の射からなる関手 I → C
def DiagramOfCones.conePoints' {G : I ⥤ J ⥤ C} (D : DiagramOfCones G) : I ⥤ C where
  obj i := (D.obj i).pt
  map {i i'} f := (D.map f).hom
  map_id i := by rw [D.id]; simp
  map_comp {x y z} f g := by rw [D.comp]

#check DiagramOfCones.mkOfHasLimits

-- 各 i ∈ I で `obj i` を G i の極限錐に取った `DiagramOfCones G`
noncomputable def DiagramOfCones.mkOfHasLimits' (G : I ⥤ J ⥤ C) [HasLimitsOfShape J C] :
    DiagramOfCones G where
  obj i := limit.cone (G.obj i)
  map {i i'} f := {
    hom := limMap (G.map f)
    w j := by dsimp; rw [limMap_π]
  }


#check DiagramOfCones.mkOfHasLimits_conePoints

-- `mkOfHasLimits'` の `conePoints'` は `G ⋙ lim` である
theorem DiagramOfCones.mkOfHasLimits_conePoints' (G : I ⥤ J ⥤ C) [HasLimitsOfShape J C] :
    DiagramOfCones.conePoints (DiagramOfCones.mkOfHasLimits G) = G ⋙ lim := by
  apply CategoryTheory.Functor.ext ?_ ?_
  · intro i; simp
  · intro i i' f; simp


#check Prod.sectR

-- i ∈ I を固定して J を I × J に埋め込む関手 j ↦ (i, j)
def Prod.sectR' (i : I) : J ⥤ I × J where
  obj j := ⟨i, j⟩
  map {j j'} f := ⟨𝟙 i, f⟩
  map_id := by simp
  map_comp := by simp



#check coneOfConeCurry

-- 各 `D.obj i` が極限錐であるとき、F 上の錐 c から定まる `D.conePoints` 上の錐
def coneOfConeCurry' (F : I × J ⥤ C) {D : DiagramOfCones (curry.obj F)}
    (Q : ∀ i, IsLimit (D.obj i)) (c : Cone F) : Cone D.conePoints where
  pt := c.pt
  π := {
    app i := (Q i).lift (c.whisker (Prod.sectR i J))
    naturality {i i'} f := by
      dsimp only [const_obj_obj, const_obj_map]
      apply  (Q i').hom_ext; intro j; simp only [curry_obj_obj_obj, DiagramOfCones.conePoints_map]
      erw [Category.id_comp, Category.assoc, (D.map f).w j]
      dsimp only [Cone.postcompose_obj_pt, Cone.postcompose_obj_π, NatTrans.comp_app, const_obj_obj,
        curry_obj_obj_obj, curry_obj_map_app]
      erw [<- Category.assoc, (Q i).fac]
      conv => arg 2; dsimp [Prod.sectR]
      rw [c.w, (Q i').fac (Cone.whisker (Prod.sectR i' J) c) j]
      unfold Cone.whisker; dsimp
      dsimp only [Prod.sectR]
  }


-- ここから定理3.8.1 の宣言

#check coneOfHasLimitCurryCompLim

-- 繰り返し極限 limit (i ↦ limit F(i, -)) から定まる F 上の錐
-- curry.obj F ⋙ lim := i ↦ limit (j ↦ F(i, j))
noncomputable def coneOfHasLimitCurryCompLim' (F : I × J ⥤ C) [HasLimitsOfShape J C]
    [HasLimit (curry.obj F ⋙ lim)] : Cone F where
  pt := limit (curry.obj F ⋙ lim)
  π := {
    app i := limit.π (curry.obj F ⋙ lim) i.1 ≫ limit.π ((curry.obj F).obj i.1) i.2
    naturality {i i'} f:= by
      simp only [const_obj_obj, const_obj_map, comp_obj, lim_obj, Category.id_comp, Category.assoc]
      have E1 := limit.w (curry.obj F ⋙ lim) f.1
      have E2 := limit.w ((curry.obj F).obj i'.1) f.2
      dsimp at E1 E2
      rw [<- E1, <- E2]
      rw [Category.assoc, <- Category.assoc (limMap _), limMap_π]
      dsimp only [curry_obj_obj_obj, curry_obj_map_app]
      rw [Category.assoc, <- F.map_comp, <- Prod.fac']
  }


#check isLimitConeOfHasLimitCurryCompLim

noncomputable def isLimitConeOfHasLimitCurryCompLim' (F : I × J ⥤ C) [HasLimitsOfShape J C]
    [HasLimit (curry.obj F ⋙ lim)] : IsLimit (coneOfHasLimitCurryCompLim F) where
  lift s := by
    let D := DiagramOfCones.mkOfHasLimits (curry.obj F)
    have HD : ((j : I) → IsLimit (D.obj j)) := fun i => limit.isLimit (((curry.obj F).obj i))
    let c :=  coneOfConeCurry F HD s
    exact limit.lift (curry.obj F ⋙ lim) c
  fac s i := by
    simp only
    set D := DiagramOfCones.mkOfHasLimits (curry.obj F)
    set HD : ((j : I) → IsLimit (D.obj j)) := fun i => limit.isLimit (((curry.obj F).obj i))
    set c :=  coneOfConeCurry F HD s
    have : HasLimit D.conePoints := by
      simp only [DiagramOfCones.mkOfHasLimits_conePoints, D]; infer_instance
    simp only [coneOfHasLimitCurryCompLim, DiagramOfCones.mkOfHasLimits]
    erw [<- Category.assoc, limit.lift_π, limit.cone_π, (HD i.1).fac]
  uniq s m w := by
    simp only
    set D := DiagramOfCones.mkOfHasLimits (curry.obj F)
    set HD : ((j : I) → IsLimit (D.obj j)) := fun i => limit.isLimit (((curry.obj F).obj i))
    set c :=  coneOfConeCurry F HD s
    simp only [coneOfHasLimitCurryCompLim, DiagramOfCones.mkOfHasLimits, limit.cone_π] at m w
    apply limit.hom_ext; intro i
    apply limit.hom_ext; intro j
    simp only [curry_obj_obj_obj, comp_obj, lim_obj, Category.assoc]
    erw [w ⟨i, j⟩, limit.lift_π]; simp only [coneOfConeCurry_π_app]
    erw [(HD i).fac]







-- 積圏の成分を入れ替える関手 J × I → I × J
#check CategoryTheory.Prod.swap

-- 繰り返し極限 limit (j ↦ limit F(-, j)) から定まる F 上の錐
noncomputable def coneOfHasLimitCurrySwapCompLim (F : I × J ⥤ C) [HasLimitsOfShape I C]
    [HasLimit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim)] : Cone F where
  pt := limit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim)
  π := {
    app p :=
      limit.π (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim) p.2 ≫
      limit.π ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj p.2) p.1
    naturality {p p'} f := by
      simp only [const_obj_obj, const_obj_map, comp_obj, lim_obj, Category.id_comp, Category.assoc]
      have E := limit.w ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj p.2) f.1
      dsimp at E
      rw [Prod.fac' f, F.map_comp, <- Category.assoc _ (F.map (Prod.mkHom f.1 (𝟙 p.2))), E]; clear E
      have E := limit.w (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim) f.2
      dsimp at E
      rw [<- E]; clear E
      rw [Category.assoc, limMap_π]
      simp
  }


noncomputable def isLimitConeOfHasLimitCurrySwapCompLim (F : I × J ⥤ C) [HasLimitsOfShape I C]
    [HasLimit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim)] :
    IsLimit (coneOfHasLimitCurrySwapCompLim F) where
  lift s := by
    set D := DiagramOfCones.mkOfHasLimits (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) )
    set HD : ((j : J) → IsLimit (D.obj j)) :=
      fun i => limit.isLimit (((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj i))
    set c :=
      coneOfConeCurry
      (CategoryTheory.Prod.swap J I ⋙ F) HD
      (Cone.whisker (CategoryTheory.Prod.swap J I) s)
    exact limit.lift (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim) c
  fac s p := by
    simp only
    set D := DiagramOfCones.mkOfHasLimits (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) )
    set HD : ((j : J) → IsLimit (D.obj j)) :=
      fun i => limit.isLimit (((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj i))
    set c :=
      coneOfConeCurry
      (CategoryTheory.Prod.swap J I ⋙ F) HD
      (Cone.whisker (CategoryTheory.Prod.swap J I) s)
    simp only [coneOfHasLimitCurrySwapCompLim, const_obj_obj, comp_obj, lim_obj]
    erw [<- Category.assoc, limit.lift_π]
    simp only [coneOfConeCurry_π_app, Cone.whisker_pt, Cone.whisker_π, whiskerLeft_app,
      Prod.swap_obj]
    erw [(HD p.2).fac]
  uniq s m w := by
    set D := DiagramOfCones.mkOfHasLimits (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) )
    set HD : ((j : J) → IsLimit (D.obj j)) :=
      fun i => limit.isLimit (((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj i))
    set c :=
      coneOfConeCurry
      (CategoryTheory.Prod.swap J I ⋙ F) HD
      (Cone.whisker (CategoryTheory.Prod.swap J I) s)
    simp only
    simp only [coneOfHasLimitCurrySwapCompLim, const_obj_obj, comp_obj, lim_obj, Prod.forall] at m w
    apply limit.hom_ext; intro j
    apply limit.hom_ext; intro i
    simp only [curry_obj_obj_obj, comp_obj, Prod.swap_obj, lim_obj, Category.assoc]
    rw [w i j]
    erw [limit.lift_π]; simp only [coneOfConeCurry_π_app, Cone.whisker_pt, Cone.whisker_π,
      whiskerLeft_app, Prod.swap_obj]
    erw [(HD j).fac]




#check limitCurrySwapCompLimIsoLimitCurryCompLim
#check Yoneda.fullyFaithful.preimageIso

noncomputable def limitCurrySwapCompLimIsoLimitCurryCompLim' (F : I × J ⥤ C)
    [HasLimitsOfShape I C] [HasLimitsOfShape J C] [HasLimit (curry.obj F ⋙ lim)]
    [HasLimit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim)] :
    limit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim) ≅ limit (curry.obj F ⋙ lim) := by
  have μ := (isLimitConeOfHasLimitCurryCompLim F).representableBy
  have ν := (isLimitConeOfHasLimitCurrySwapCompLim F).representableBy
  exact ν.uniqueUpToIso μ


#check yonedaEquiv_comp

-- 自然変換の合成 α ≫ β の米田対応（定理2.2.4 の全単射での像）は、α の米田対応を β で送ったもの
theorem yonedaEquiv_comp' {X : C} {F G : Cᵒᵖ ⥤ Type v} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) :
    yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α) := by
  simp only [yonedaEquiv, Equiv.coe_fn_mk]
  rw [NatTrans.comp_app, comp_apply]


#check yonedaEquiv_yoneda_map

-- 射 f を米田埋め込みで送った自然変換の米田対応は f 自身
theorem yonedaEquiv_yoneda_map' {X Y : C} (f : X ⟶ Y) :
    yonedaEquiv (yoneda.map f) = f := by
  simp only [yonedaEquiv, Equiv.coe_fn_mk]
  erw [yoneda_map_app]; simp



#check Yoneda.fullyFaithful.preimageIso
#check yoneda.mapIso

-- 同じ関手 F の 2 つの表現 e, e' から得る同型 φ : Y ≅ Y' について、
-- e'.homEquiv (g ≫ φ.hom) = e.homEquiv g
theorem uniqueUpToIso_homEquiv_comp {F : Cᵒᵖ ⥤ Type v} {Y Y' : C}
    (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') {Z : C} (g : Z ⟶ Y) :
    e'.homEquiv (g ≫ (e.uniqueUpToIso e').hom) = e.homEquiv g := by
  apply e'.homEquiv.symm.injective
  rw [Equiv.symm_apply_apply]
  apply yoneda.map_injective
  rw [yoneda.map_comp]
  simp only [RepresentableBy.uniqueUpToIso_hom, NatIso.ofComponents]
  rw [FullyFaithful.map_preimage]
  ext x f
  simp only [yoneda_obj_obj, NatTrans.comp_app, yoneda_map_app, TypeCat.Fun.toFun_apply, comp_apply,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Function.comp_apply]
  rw [e.homEquiv_comp, Equiv.symm_apply_eq, e'.homEquiv_comp]
  simp




-- 同じ図式の 2 つの極限錐 t, t' から得る頂点の同型 φ : t.pt ≅ t'.pt について、
-- φ.hom ≫ t'.π.app j = t.π.app j
theorem uniqueUpToIso_representableBy_hom_comp {F : J ⥤ C} {t t' : Cone F}
    (h : IsLimit t) (h' : IsLimit t') (j : J) :
    (h.representableBy.uniqueUpToIso h'.representableBy).hom ≫ t'.π.app j = t.π.app j := by
  have E := uniqueUpToIso_homEquiv_comp (h.representableBy) (h'.representableBy) (𝟙 _)
  conv at E => arg 2; erw [h.homEquiv_apply]; simp only [Cone.extend_π, CategoryTheory.Functor.map_id, Category.id_comp]
  set σ := (h.representableBy.uniqueUpToIso h'.representableBy).hom
  rw [<- Equiv.eq_symm_apply, Category.id_comp] at E
  simp only [cones_obj, IsLimit.representableBy, IsLimit.homEquiv, Cone.extend_π, Equiv.symm_mk,
    Equiv.coe_fn_mk] at E
  rw [E]
  rw [h'.fac]



#check limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π

-- 同型の hom に 2 段の射影を合成すると、順序を入れ替えた 2 段の射影になる
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π' (F : I × J ⥤ C)
    [HasLimitsOfShape I C] [HasLimitsOfShape J C] [HasLimit (curry.obj F ⋙ lim)]
    [HasLimit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim)] (i : I) (j : J) :
    (limitCurrySwapCompLimIsoLimitCurryCompLim' F).hom ≫
        limit.π (curry.obj F ⋙ lim) i ≫ limit.π ((curry.obj F).obj i) j =
      limit.π (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim) j ≫
        limit.π ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj j) i := by
  have E :=
    uniqueUpToIso_representableBy_hom_comp
    (isLimitConeOfHasLimitCurrySwapCompLim F)
    (isLimitConeOfHasLimitCurryCompLim F) ⟨i, j⟩
  erw [E]; rfl



#check limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π

-- 同型の inv についての同じ等式
theorem limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π' (F : I × J ⥤ C)
    [HasLimitsOfShape I C] [HasLimitsOfShape J C] [HasLimit (curry.obj F ⋙ lim)]
    [HasLimit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim)] (i : I) (j : J) :
    (limitCurrySwapCompLimIsoLimitCurryCompLim' F).inv ≫
        limit.π (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim) j ≫
          limit.π ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj j) i =
      limit.π (curry.obj F ⋙ lim) i ≫ limit.π ((curry.obj F).obj i) j := by
    rw [Iso.inv_comp_eq]; symm
    rw [<- limitCurrySwapCompLimIsoLimitCurryCompLim_hom_π_π']





-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- (3.8.2)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C が I 型の極限と J 型の極限を持つとき、F を limit (i ↦ limit F(i, -)) に送る関手
C^{I×J} → C と、F を limit (j ↦ limit F(-, j)) に送る関手 C^{I×J} → C は、極限関手をどう
選んでも自然同型である。

本はこの 2 つの関手を、合成 C^{I×J} → C^I → C と C^{I×J} → C^J → C として描いている。
`limJ I J C` は F を図式 i ↦ limit F(i, -) に送る関手 C^{I×J} → C^I、`limI I J C` は F を図式
j ↦ limit F(-, j) に送る関手 C^{I×J} → C^J である。本はこの 2 つの式を与えていない。
C^I → C と C^J → C は極限関手 `lim` である。
-/

section

variable (I J C)

-- F ↦ (i ↦ limit F(i, -))
noncomputable def limJ [HasLimitsOfShape J C] : (I × J ⥤ C) ⥤ (I ⥤ C) :=
  curry ⋙ (whiskeringRight I (J ⥤ C) C).obj lim



-- F ↦ (j ↦ limit F(-, j))
noncomputable def limI [HasLimitsOfShape I C] : (I × J ⥤ C) ⥤ (J ⥤ C) :=
  (whiskeringLeft (J × I) (I × J) C).obj (CategoryTheory.Prod.swap J I) ⋙ limJ J I C






noncomputable def limJCompLimIsoLimICompLim [HasLimitsOfShape I C] [HasLimitsOfShape J C] :
    limJ I J C ⋙ lim ≅ limI I J C ⋙ lim := by
  apply NatIso.ofComponents ?_ ?_
  · intro F; --simp [limI, limJ]
    exact (limitCurrySwapCompLimIsoLimitCurryCompLim F).symm
  · intro F G σ
    dsimp only [comp_obj, lim_obj, Functor.comp_map, lim_map, Iso.symm_hom]
    apply limit.hom_ext; intro j
    apply limit.hom_ext; intro i
    dsimp only [whiskeringLeft_obj_obj, curry_obj_obj_obj, comp_obj, Prod.swap_obj]
    dsimp only [limJ, comp_obj, whiskeringRight_obj_obj, limI, whiskeringLeft_obj_obj, lim_obj,
      Functor.comp_map, whiskeringRight_obj_map, whiskeringLeft_obj_map]
    rw [Category.assoc, Category.assoc, limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π]
    erw [<- Category.assoc, limMap_π, whiskerRight_app]
    erw [Category.assoc, limMap_π, curry_map_app_app]
    simp only [comp_obj, lim_obj, curry_obj_obj_obj, Category.assoc]
    erw [<- Category.assoc (limMap _), limMap_π, whiskerRight_app]
    rw [Category.assoc, lim_map, limMap_π, curry_map_app_app]
    erw [<- Category.assoc, <- Category.assoc, <- Category.assoc]
    rw [Category.assoc ((limitCurrySwapCompLimIsoLimitCurryCompLim F).inv), limitCurrySwapCompLimIsoLimitCurryCompLim_inv_π_π]
    simp


end

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.8.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
双関手 F : I × J → C について、κ の始域と終域に現れる極限と余極限が存在するならば、標準的な射
κ : colimit (i ↦ limit F(i, -)) → limit (j ↦ colimit F(-, j)) がある。

`curry.obj F ⋙ lim` は図式 i ↦ limit F(i, -)、
`curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ colim` は図式 j ↦ colimit F(-, j) である。
本は κ の始域と終域に現れる極限と余極限の存在だけを仮定する。`lim` と `colim` を使うので、
宣言は C がすべての J 型の極限と I 型の余極限を持つことを仮定している。
-/

-- 余極限関手。命題3.3.1 の双対

#check colimitLimitToLimitColimit


noncomputable def colimLimComparison (F : I × J ⥤ C) [HasLimitsOfShape J C]
    [HasColimitsOfShape I C] :
    -- colim_i lim_j F(i,j) ⟶ lim_j colim_i F(i, j)
    colimit (curry.obj F ⋙ lim) ⟶ limit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ colim) := by
  -- apply colimit.post (curry.obj F) lim ≫ limMap _
  -- let t : Cocone (curry.obj F) := {
  --   pt := curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ colim
  --   ι := {
  --     app i := {
  --       app j := colimit.ι ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj j) i
  --       naturality {j j'} f := by simp
  --     }
  --     naturality {i i'} f := by
  --       ext j;
  --       simp only [curry_obj_obj_obj, const_obj_obj, comp_obj, colim_obj, NatTrans.comp_app,
  --         curry_obj_map_app, const_obj_map, Category.comp_id]
  --       exact colimit.w ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj j) f
  --   }
  -- }
  -- exact colimit.desc (curry.obj F) t
  let s : Cocone (curry.obj F ⋙ lim) := {
    pt := limit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ colim)
    ι := {
      app i := limMap <| {
        app j := colimit.ι ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj j) i
        naturality {j j'} f := by simp
      }
      naturality {i i'} f := by
        dsimp only [comp_obj, lim_obj, const_obj_obj, Functor.comp_map, lim_map, const_obj_map]
        ext j;
        simp only [comp_obj, colim_obj, Category.assoc, limMap_π, curry_obj_obj_obj, limMap_π_assoc,
          curry_obj_map_app, Category.comp_id]
        have := (colimit.w ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj j) f)
        erw [this]
    }
  }
  exact colimit.desc (curry.obj F ⋙ lim) s







#check ι_colimitLimitToLimitColimit_π

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系3.8.4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の集合 X, Y と任意の関数 f : X × Y → ℝ について、不等式
sup_{x∈X} inf_{y∈Y} f(x, y) ≤ inf_{y∈Y} sup_{x∈X} f(x, y) は、現れる下限と上限がすべて存在する
ならば成り立つ。

`a x` は inf_{y∈Y} f(x, y)、`s` は不等式の左辺、`b y` は sup_{x∈X} f(x, y)、`t` は不等式の右辺で
ある。下限と上限が存在するという仮定は、`a x`・`s`・`b y`・`t` がそれぞれ下限・上限であるという
仮定 `ha`・`hs`・`hb`・`ht` になる。
-/

-- 集合 A の上限（最小上界）。`IsGLB`（命題3.6.10）の双対
#check IsLUB

-- Mathlib にあるのは、完備束に値を取る関数についての同じ不等式
#check iSup_iInf_le_iInf_iSup

theorem sup_inf_le_inf_sup {X Y : Type*} (f : X × Y → ℝ)
    (a : X → ℝ) (ha : ∀ x, IsGLB (Set.range fun y ↦ f (x, y)) (a x))
    (s : ℝ) (hs : IsLUB (Set.range a) s)
    (b : Y → ℝ) (hb : ∀ y, IsLUB (Set.range fun x ↦ f (x, y)) (b y))
    (t : ℝ) (ht : IsGLB (Set.range b) t) : s ≤ t :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.8.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏 J がフィルター圏であるとは、J の任意の有限な図式の下に錐があることである。

有限な図式は、有限な圏 K（定理3.5.17 の `FinCategory`）からの関手 K → J である。

Mathlib の `IsFiltered J` は別の形で定義されている。J が空でなく、任意の 2 対象 X, Y に対して
射 X → Z と Y → Z を持つ対象 Z があり、任意の平行な射 f, g : X → Y に対して h ∘ f = h ∘ g と
なる射 h : Y → Z がある、という 3 条件である。`isFiltered'_iff` は 2 つの定義の同値である。
-/

def IsFiltered' (J : Type u) [Category.{v} J] : Prop :=
  ∀ (K : Type v) [SmallCategory K] [FinCategory K] (F : K ⥤ J), Nonempty (Cocone F)

#check IsFiltered
#check IsFiltered.iff_cocone_nonempty

theorem isFiltered'_iff (J : Type u) [Category.{v} J] : IsFiltered' J ↔ IsFiltered J :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- フィルター余極限の記述（定理3.8.9 の直後）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小さなフィルター圏 J で添字づけた図式 F : J → Set について、colimit F は、余積 ∐ F j を次の
同値関係で割った商である: x ∈ F j と y ∈ F k が同一視されるのは、J の射 f : j → t と
g : k → t で F f(x) = F g(y) となるものが存在するとき、かつそのときに限る。より一般に、∐ F j の
有限個の要素が colimit F で同一視されるならば、それらはある F t の共通の要素に写る。

`Σ j, F.obj j` は余積 ∐ F j で、要素は j ∈ J と x ∈ F j の組 ⟨j, x⟩ である（命題3.6.1）。
`Types.FilteredColimit.Rel F` は ⟨j, x⟩ と ⟨k, y⟩ の間の上の関係で、`FilteredColimitRel F` と
同じ定義である。

`filteredColimitCocone F` は、∐ F j をこの関係で割った商を頂点とし、x ∈ F j を ⟨j, x⟩ の類に
送る射を脚とする F 下の錐である。これが余極限錐であることが「colimit F は商である」にあたる。

`colimit.ι F j x` は、x ∈ F j の colimit F での像である。`colimit_eq_iff'` は、同一視の条件を
Mathlib の `colimit F` について述べる。`exists_map_eq_of_colimit_ι_eq` は「より一般に」以降の
主張で、有限個の要素を、有限な型 A で添字づけた族 `x` として受け取る。
-/

#check Types.FilteredColimit.Rel

def FilteredColimitRel (F : J ⥤ Type v) (x y : Σ j, F.obj j) : Prop :=
  ∃ (t : J) (f : x.1 ⟶ t) (g : y.1 ⟶ t), F.map f x.2 = F.map g y.2

#check Types.FilteredColimit.rel_equiv

theorem filteredColimitRel_equivalence [IsFiltered J] (F : J ⥤ Type v) :
    _root_.Equivalence (Types.FilteredColimit.Rel F) :=
  sorry

def filteredColimitCocone (F : J ⥤ Type v) : Cocone F where
  pt := Quot (Types.FilteredColimit.Rel F)
  ι := {
    app j := TypeCat.ofHom fun x ↦ Quot.mk _ ⟨j, x⟩
    naturality := sorry
  }

def isColimitFilteredColimitCocone [IsFiltered J] (F : J ⥤ Type v) :
    IsColimit (filteredColimitCocone F) :=
  sorry

#check Types.FilteredColimit.colimit_eq_iff

theorem colimit_eq_iff' [IsFiltered J] (F : J ⥤ Type v) {j k : J} (x : F.obj j) (y : F.obj k) :
    colimit.ι F j x = colimit.ι F k y ↔ ∃ (t : J) (f : j ⟶ t) (g : k ⟶ t), F.map f x = F.map g y :=
  sorry

theorem exists_map_eq_of_colimit_ι_eq [IsFiltered J] (F : J ⥤ Type v) {A : Type} [Finite A]
    (x : A → Σ j, F.obj j)
    (h : ∀ a b, colimit.ι F (x a).1 (x a).2 = colimit.ι F (x b).1 (x b).2) :
    ∃ (t : J) (f : ∀ a, (x a).1 ⟶ t), ∀ a b, F.map (f a) (x a).2 = F.map (f b) (x b).2 :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.8.9
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
Set において、フィルター余極限は有限極限と交換する。すなわち、有限な圏 I と小さなフィルター圏 J に
ついて、任意の関手 F : I × J → Set の標準的な射
κ : colimit (j ↦ limit F(-, j)) → limit (i ↦ colimit F(i, -)) は同型である。

κ は補題3.8.3 の標準的な射で、補題3.8.3 と比べて I と J の役割が入れ替わっている。極限を取る
変数が I、余極限を取る変数が J である。`colimitLimitToLimitColimit F` がこの κ である。

本の証明は κ が全単射であることを示す。Set の射が全単射であることと同型であることは同値である。
-/

#check colimitLimitToLimitColimit_isIso

theorem colimitLimitToLimitColimit_isIso' [FinCategory I] [IsFiltered J] (F : I × J ⥤ Type v) :
    IsIso (colimitLimitToLimitColimit F) :=
  sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.8.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 冪等射の分裂が任意の形の極限・余極限と交換することを、演習3.4.vi から結論する問題。分裂を
-- 極限・余極限として述べるには、冪等射を 1 つ持つ 1 対象圏で添字づけた図式が要る。この圏は
-- Mathlib になく、演習3.4.vi (ii) も同じ理由で置いていないので、置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.8.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
G と H が位数の互いに素な群ならば、Set において、BG で添字づけた極限は BH で添字づけた余極限と
交換する。

「交換する」は定理3.8.9 と同じ意味である。任意の関手 F : BG × BH → Set について、補題3.8.3 の
標準的な射 κ が同型であることをいう。極限を取る変数が BG、余極限を取る変数が BH で、
`colimitLimitToLimitColimit F` がこの κ である。

`SingleObj G` は BG（例3.2.10）、`Nat.card G` は G の位数である。`Nat.card` は無限の型に 0 を
返すので、G と H が有限であること（`Finite`）を仮定に加えている。
-/

-- 型の要素の個数。無限の型では 0
#check Nat.card
-- 2 つの自然数が互いに素であること
#check Nat.Coprime

theorem colimitLimitToLimitColimit_isIso_of_coprime {G H : Type v} [Group G] [Group H]
    [Finite G] [Finite H] (hGH : Nat.Coprime (Nat.card G) (Nat.card H))
    (F : SingleObj G × SingleObj H ⥤ Type v) :
    IsIso (colimitLimitToLimitColimit F) :=
  sorry

end Riehl
