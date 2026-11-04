import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Yoneda
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# 3.5 極限と余極限の表現可能性

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 例3.5.4（冪）、例3.5.7（余積）、例3.5.8（余冪）、例3.5.9（押し出し）、
注意3.5.14（一般化された要素）は載せない。
-/

open CategoryTheory Limits Opposite

namespace Riehl

universe v u w t

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  前の節の復習
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.5
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 極限 limit F は関手 Cone(−, F) を表現する：Hom(−, limit F) ≅ Cone(−, F)
#check IsLimit.natIso
noncomputable def homLimitIsoCones (F : J ⥤ C) [HasLimit F] :
    yoneda.obj (limit F) ≅ F.cones where
  hom := {
    app x':= TypeCat.ofHom (fun f => {
      app i := f ≫ limit.π F i
      naturality {i i'} f := by simp
    })
    naturality {x' y'} f := by
      ext f; apply NatTrans.ext; ext j; simp
  }

  inv := {
    app x := TypeCat.ofHom (fun σ => limit.lift F ⟨unop x, σ⟩)
    naturality {x x'} f := by
      ext σ; apply limit.hom_ext; intro j; simp
  }
  hom_inv_id := by
    ext x f; apply limit.hom_ext; intro j; simp
  inv_hom_id := by
    ext x σ; apply NatTrans.ext; ext j; simp


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.2.4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Set の極限の要素は、各射影での値で決まる
#check Types.limit_ext
theorem types_limit_ext {F : J ⥤ Type v} (x y : limit F)
    (w : ∀ j, limit.π F j x = limit.π F j y) :
    x = y := by
  let σ := Functor.CorepresentableBy.id.homEquiv (Y := limit F)
  simp at σ
  apply σ.symm.injective
  apply limit.hom_ext
  intro j
  ext u; simp only [TypeCat.Fun.toFun_apply, comp_apply]
  erw [w j]
  simp  [σ]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.3.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 極限関手 lim : Cᴶ → C（命題3.3.1）を組み直す
#check lim
noncomputable def lim' [HasLimitsOfShape J C] : (J ⥤ C) ⥤ C where
  obj F := limit F
  map {F G} σ := by
    set s : Cone G := {
      pt := limit F
      π := {
        app i := limit.π F i ≫ σ.app i
        naturality {j j'} f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
          rw [<- limit.w F f, Category.assoc, σ.naturality f]
      }
    }
    exact limit.lift G s

-- limit.lift F c ≫ limMap α は、c を α で後合成した錐の limit.lift
#check limit.lift_map
theorem limit_lift_map {F G : J ⥤ C} [HasLimit F] [HasLimit G] (c : Cone F) (α : F ⟶ G) :
    limit.lift F c ≫ limMap α = limit.lift G ((Cone.postcompose α).obj c) := by
  apply limit.hom_ext; intro j
  rw [limit.lift_π]
  dsimp only [Cone.postcompose_obj_pt, Cone.postcompose_obj_π, NatTrans.comp_app,
    Functor.const_obj_obj]
  simp only [limMap, IsLimit.map]
  rw [limit.isLimit_lift, Category.assoc, limit.lift_π]
  dsimp only [Cone.postcompose_obj_pt, limit.cone_x, Cone.postcompose_obj_π, NatTrans.comp_app,
    Functor.const_obj_obj, limit.cone_π]
  rw [<- Category.assoc, limit.lift_π]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.4.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 関手 F で写した極限錐から得られる比較射 F(limit K) → limit (K ⋙ F) を組み直す
#check limit.post

noncomputable def limitPost' (K : J ⥤ C) {D : Type*} [Category.{v} D] (F : C ⥤ D)
    [HasLimit K] [HasLimit (K ⋙ F)] :
    F.obj (limit K) ⟶ limit (K ⋙ F) := by
  exact limit.lift (K ⋙ F) (F.mapCone (limit.cone K))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.4.9
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 関手圏に値を取る図式は、各点で極限を持てば極限を持つ
#check functorCategoryHasLimit

theorem functorCategory_hasLimit {K : Type*} [Category K] (F : J ⥤ K ⥤ C)
    [∀ k, HasLimit (F.flip.obj k)] :
    HasLimit F where
  exists_limit := ⟨{
    cone := {
      pt := {
        obj k := limit ((F.flip.obj k))
        map {k k'} f := limMap (F.flip.map f)
        map_id k := by ext j; simp
        map_comp {k l m} f g := by ext j; simp
      }
      π := {
        app j := {
          app k := limit.π (F.flip.obj k) j
          naturality {k k'} f := by simp
        }

        naturality {j j'} f := by
          apply NatTrans.ext; ext k;
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            NatTrans.comp_app]
          rw [<- limit.w (F.flip.obj k) f]; simp
      }
    }
    isLimit := {
      lift s := {
        app k := by
          simp only
          let c : Cone (F.flip.obj k) := {
            pt := s.pt.obj k
            π := {
              app j := (s.π.app j).app k
              naturality {j j'} f := by
                simp only [Functor.const_obj_obj, Functor.flip_obj_obj, Functor.const_obj_map,
                  Category.id_comp, Functor.flip_obj_map]
                rw [<- NatTrans.comp_app, <- s.π.naturality f]
                rw [NatTrans.comp_app]; simp
            }
          }
          exact limit.lift (F.flip.obj k) c
        naturality {k k'} f := by
          dsimp only [Functor.const_obj_obj, Lean.Elab.WF.paramLet, id_eq]
          apply limit.hom_ext; intro j
          rw [Category.assoc, limit.lift_π]
          dsimp only [Functor.flip_obj_obj]
          rw [limit.lift_map, limit.lift_π]
          dsimp only [Cone.postcompose_obj_pt, Cone.postcompose_obj_π, NatTrans.comp_app,
            Functor.const_obj_obj, Functor.flip_obj_obj, Functor.flip_map_app]
          rw [<- ((s.π.app j)).naturality f]
          rfl
      }

      fac s j := by
        apply NatTrans.ext; ext k;
        dsimp only [Functor.const_obj_obj, Lean.Elab.WF.paramLet, id_eq, NatTrans.comp_app]
        rw [limit.lift_π]
      uniq s m w := by
        simp only [Functor.const_obj_obj] at m w
        apply NatTrans.ext; ext k j;
        dsimp only [Functor.flip_obj_obj, Functor.const_obj_obj, Lean.Elab.WF.paramLet, id_eq]
        rw [limit.lift_π]; dsimp only
        rw [<- w j]; simp
    }
  }⟩


-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- (3.5.1) と演習3.5.i（定理3.5.2 の前）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の図式 F : J → C について、limit (Hom(X, F-)) の要素は頂点 X を持つ F 上の錐にほかならず、
同型 limit (Hom(X, F-)) ≅ Cone(X, F) が X について自然に成り立つ（(3.5.1)、演習3.5.i）。

構成: 関手 X ↦ limit (Hom(X, F-)) を前合成と lim の合成で組み、Cone(−, F)（Functor.cones）との
      自然同型を組む。
-/

-- 関手 F : J → C との前合成 (C → D) → (J → D) を関手として組む。射の部分は 1.7 の whiskering
#check Functor.whiskeringLeft

def whiskeringLeft' (J : Type v) [SmallCategory J] (C : Type u) [Category.{v} C] (D : Type*)
    [Category.{v} D] :
    (J ⥤ C) ⥤ (C ⥤ D) ⥤ (J ⥤ D) where
  obj F := {
    obj G := F ⋙ G
    map {G G'} σ := F.whiskerLeft σ
    map_id G := by simp
    map_comp {G H K} σ ι := by simp
  }
  map {F F'} σ := {
    app G := Functor.whiskerRight σ G
    naturality {G G'} ι := by
      ext j; simp
  }
  map_id F := by
    ext G j; simp
  map_comp {F G H} ι τ := by
    ext I j; simp


-- X ↦ limit (Hom(X, F-))
noncomputable def limHomFunctor (F : J ⥤ C) : Cᵒᵖ ⥤ Type v :=
  (coyoneda ⋙ (Functor.whiskeringLeft J C (Type v)).obj F) ⋙ lim
-- (x ↦ Hom(x,-))   (G ↦ F ⋙ G)   (K ↦ limt K)
-- (x ↦ F ⋙ Hom(x, -))  (K ↦ limit K)
-- (x ↦ Hom(x, F-)) (K →  limit K)
-- x ↦ limit (Hom(x, F-))

-- 関手 G ↦ limit G と G ↦ Hom((const J).obj PUnit, G) の自然同型
noncomputable def limIsoCoyonedaConstPUnit :
    lim ≅ coyoneda.obj (op ((Functor.const J).obj PUnit.{v + 1})) where
  hom := {
    app F := TypeCat.ofHom (fun f => {
      app i := TypeCat.ofHom (fun u => limit.π F i f)
      naturality {i j} h := by ext u; simp
    })
    naturality {F G} σ := by
      ext x; apply NatTrans.ext; ext j u; simp
  }
  inv := {
    app F := TypeCat.ofHom (fun σ => limit.lift F ⟨_, σ⟩ PUnit.unit)
    naturality {F G} σ := by
      ext τ; apply Types.limit_ext; intro j; simp
  }
  hom_inv_id := by
    apply NatTrans.ext; ext F x
    rw [NatTrans.comp_app]
    apply Types.limit_ext; intro j
    simp
  inv_hom_id := by
    apply NatTrans.ext; ext F σ
    apply NatTrans.ext; ext j u
    rcases u; simp

#check limitCompCoyonedaIsoCone
#print Functor.cones
noncomputable def limHomIsoCones (F : J ⥤ C) : limHomFunctor F ≅ F.cones := by
  symm
  apply Iso.trans _ (Functor.isoWhiskerLeft ((coyoneda ⋙ (Functor.whiskeringLeft J C (Type v)).obj F))
    limIsoCoyonedaConstPUnit.symm)
  apply NatIso.ofComponents ?_ ?_
  · intro x
    refine {
      hom :=
      TypeCat.ofHom (fun σ => {
        app i := TypeCat.ofHom (fun u => σ.app i)
        naturality {i j} f := by
          ext u;
          simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.flip_obj_obj,
            yoneda_obj_obj, Functor.const_obj_obj, Functor.const_obj_map, Functor.op_obj,
            Category.id_comp, TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk,
            Functor.comp_map, Functor.flip_obj_map, yoneda_map_app, comp_apply]
          rw [<- σ.naturality f]
          simp
      })
      inv := TypeCat.ofHom (fun σ => {
        app i :=  (σ.app i).hom PUnit.unit
        naturality {i j} f := by
          simp only [Functor.op_obj, Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj,
            Functor.whiskeringLeft_obj_obj, Functor.flip_obj_obj, yoneda_obj_obj, Category.id_comp]
          have E := σ.naturality f
          apply congr_arg (fun x => x.hom PUnit.unit) E
      })
      hom_inv_id := by
        ext σ; apply NatTrans.ext; ext j; simp
      inv_hom_id := by
        ext σ; apply NatTrans.ext; ext j u
        congr
    }
  · intro x y f; ext σ
    apply NatTrans.ext; ext j u
    dsimp


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
極限が存在する任意の図式 F : J → C について、極限錐が誘導する標準的な写像は、各 X ∈ C に
ついて自然な同型 Hom(X, limit F) ≅ limit (Hom(X, F-)) を定める。したがって共変表現可能関手
Hom(X, −) : C → Set は、C に存在する任意の極限を保存する。

構成: 本文の証明に沿う。補題3.4.3 の比較射を Hom(X, −) に当てて標準的な写像の X 成分とし、
      X について束ねる。それと (3.5.1) の自然同型との合成が、定義3.1.5 の自然同型
      Hom(−, limit F) ≅ Cone(−, F) に等しいこと（三角形）から、標準的な写像が同型であることを
      示す。最後に補題3.4.3 から極限の保存を示す。
-/

#check limit.post
noncomputable def homLimitToLimitHomApp (F : J ⥤ C) [HasLimit F] (X : Cᵒᵖ) :
    (unop X ⟶ limit F) ⟶ limit (F ⋙ coyoneda.obj X) :=
  limit.post F (coyoneda.obj X)


-- (X ↦ Hom(X, limit F)) → (X ↦ limit (Hom(X, F-)))
noncomputable def homLimitToLimitHom (F : J ⥤ C) [HasLimit F] :
    yoneda.obj (limit F) ⟶ limHomFunctor F where
  app X := homLimitToLimitHomApp F X
  naturality {X Y} f := by
    ext y; simp only [yoneda_obj_obj, yoneda_obj_map, TypeCat.Fun.toFun_apply]
    apply Types.limit_ext; intro j
    dsimp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.flip_obj_obj,
      yoneda_obj_obj]
    dsimp only [limHomFunctor, Functor.comp_obj, Functor.whiskeringLeft_obj_obj, lim_obj,
      homLimitToLimitHomApp, Functor.comp_map, Functor.whiskeringLeft_obj_map, lim_map]
    simp only [limit.post, limit.lift_map]
    erw [<- comp_apply, <- comp_apply]
    rw [Category.assoc, limit.lift_π, limit.lift_π]
    simp

#check IsLimit.representableBy
theorem homLimitToLimitHom_comp (F : J ⥤ C) [HasLimit F] :
    homLimitToLimitHom F ≫ (limHomIsoCones F).hom =
      (limit.isLimit F).representableBy.toIso.hom := by
  let σ := yonedaEquiv (X := limit F) (F := F.cones)
  apply σ.injective
  apply NatTrans.ext; ext j
  simp only [Functor.op_obj, Functor.const_obj_obj, Functor.cones_obj, yonedaEquiv, yoneda_obj_obj,
    op_unop, Functor.cones_map, Quiver.Hom.unop_op, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    Equiv.coe_fn_mk, NatTrans.comp_app, comp_apply, limit.cone_x, σ]

  simp only [Functor.RepresentableBy.toIso, IsLimit.representableBy, limit.cone_x]
  simp only [Functor.representableByEquiv, op_unop, Functor.cones_obj, yoneda_obj_obj,
    IsLimit.homEquiv, limit.cone_x, Cone.extend_π, limit.isLimit_lift, Equiv.coe_fn_mk,
    NatIso.ofComponents_hom_app, Equiv.toIso_hom_hom_apply, CategoryTheory.Functor.map_id,
    Category.id_comp, limit.cone_π]

  simp only [homLimitToLimitHom, homLimitToLimitHomApp]
  -- erw [<- comp_apply]
  simp only [limHomIsoCones, Functor.cones_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
    Functor.flip_obj_obj, yoneda_obj_obj, Functor.const_obj_obj, Functor.op_obj]
  erw [Iso.trans_symm]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskeringLeft_obj_obj, Functor.flip_obj_obj, yoneda_obj_obj, Functor.cones_obj,
    NatIso.ofComponents_inv_app]
  erw [comp_apply]
  erw [Iso.symm_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv]
  simp only [TypeCat.hom_ofHom, limIsoCoyonedaConstPUnit, lim_obj, Functor.flip_obj_obj,
    yoneda_obj_obj, Functor.const_obj_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
    TypeCat.Fun.coe_mk]
  change (limit.post F (coyoneda.obj (op (limit F))) ≫
      limit.π (F ⋙ coyoneda.obj (op (limit F))) j) (𝟙 (limit F)) = _
  rw [limit.post_π]
  simp



theorem isIso_homLimitToLimitHom (F : J ⥤ C) [HasLimit F] :
    IsIso (homLimitToLimitHom F) := by
  have E := homLimitToLimitHom_comp F
  rw [<- Iso.eq_comp_inv] at E
  rw [E]
  exact
    NatIso.isIso_of_isIso_app ((limit.isLimit F).representableBy.toIso.hom ≫ (limHomIsoCones F).inv)

#check coyoneda_preservesLimit
theorem coyonedaObj_preservesLimit (F : J ⥤ C) [HasLimit F] (X : Cᵒᵖ) :
    PreservesLimit F (coyoneda.obj X) := by
  have H := isIso_homLimitToLimitHom F
  have HX :=  NatIso.isIso_app_of_isIso (homLimitToLimitHom F) X
  simp [homLimitToLimitHom, homLimitToLimitHomApp] at HX
  apply preservesLimit_of_isIso_post

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.5
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C を任意の局所小圏とする。(i) 共変表現可能関手 C(X, −) は C に存在するすべての極限を保存する。
(ii) 共変米田埋め込み c ↦ Hom(−, c) : C ↪ Set^{C^op} は極限を保存し、かつ反映する。
-/

#print Functor.RepresentableBy.toIso

#check coyoneda_preservesLimits

theorem coyonedaObj_preservesLimits (X : Cᵒᵖ) :
    PreservesLimitsOfSize.{v, v} (coyoneda.obj X) where
  preservesLimitsOfShape {J} := {
    preservesLimit {K} := by
      apply coyoneda_preservesLimit
  }

example [Category C] [Category D] (F : C ⥤ D) [F.Full] [F.Faithful] (K : J ⥤ C) :
    ReflectsLimit K F where
  reflects {c} Hc := ⟨{
    lift s := F.preimage (Hc.lift (F.mapCone s))
    fac s j := by
      apply F.map_injective
      rw [F.map_comp, F.map_preimage]
      have E := Hc.fac (F.mapCone s) j
      simp only [Functor.mapCone_pt, Functor.comp_obj, Functor.mapCone_π_app] at E
      rw [E]
    uniq s m w := by
      apply F.map_injective
      erw [F.map_preimage]
      rw [Hc.uniq (F.mapCone s) (F.map m)]
      intro j; simp only [Functor.mapCone_pt, Functor.comp_obj, Functor.mapCone_π_app]
      rw [<- F.map_comp, w j]
  }⟩

#check yonedaFunctor_preservesLimits

theorem yonedaEmbedding_preservesLimits :
    PreservesLimitsOfSize.{v, v} (yoneda : C ⥤ Cᵒᵖ ⥤ Type v) where
  preservesLimitsOfShape {J} := {
    preservesLimit {F} := {
      preserves {c} Hc := ⟨by
        apply evaluationJointlyReflectsLimits
        intro x
        have E :
          ((evaluation Cᵒᵖ (Type v)).obj x).mapCone (yoneda.mapCone c) = (coyoneda.obj x).mapCone c
          := rfl
        rw [E]
        have := coyoneda_preservesLimits.{v, v} x
        exact isLimitOfPreserves (coyoneda.obj x) Hc
      ⟩
    }
  }


#check yonedaFunctor_reflectsLimits

theorem yonedaEmbedding_reflectsLimits :
    ReflectsLimitsOfSize.{w, t} (yoneda : C ⥤ Cᵒᵖ ⥤ Type v) := by
  have H1 := Yoneda.yoneda_faithful (C := C)
  have H2 := Yoneda.yoneda_full (C := C)
  apply fullyFaithful_reflectsLimits


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
余極限が存在する任意の図式 F : J → C について、余極限錐が誘導する標準的な写像は、各 X ∈ C
について自然な同型 Hom(colimit F, X) ≅ limit (Hom(F-, X)) を定める。したがって反変表現可能
関手 Hom(−, X) : Cᵒᵖ → Set は、C に存在する任意の余極限を Set の極限に写す。

構成: 定理3.5.2 の双対。関手 X ↦ limit (Hom(F-, X)) を組み、標準的な写像を
      Hom(colimit F, −) からその関手への自然変換として組み、それが関手圏で同型であることを
      示す。そこから、Hom(−, X) が F の余極限を Fᵒᵖ の極限として保存することを示す。
-/

-- 対象 X を limit (Hom(F-, X)) に送り、射は f との後合成が誘導する。Mathlib では既存の関手の合成で書ける
noncomputable def limHomOpFunctor (F : J ⥤ C) : C ⥤ Type v := sorry

-- (X ↦ Hom(colimit F, X)) → (X ↦ limit (Hom(F-, X)))
noncomputable def homColimitToLimitHom (F : J ⥤ C) [HasColimit F] :
    coyoneda.obj (op (colimit F)) ⟶ limHomOpFunctor F := sorry

theorem isIso_homColimitToLimitHom (F : J ⥤ C) [HasColimit F] :
    IsIso (homColimitToLimitHom F) := sorry

#check yoneda_preservesLimit

theorem yonedaObj_preservesLimit (F : J ⥤ C) (X : C) :
    PreservesLimit F.op (yoneda.obj X) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.10
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C を任意の局所小圏とする。(i) 反変表現可能関手 C(−, X) は C の余極限を Set の極限に写す。
(ii) 反変米田埋め込み c ↦ Hom(c, −) : C^op ↪ Set^C は C^op の極限を保存し、かつ反映する。
-/

#check yoneda_preservesLimits

theorem yonedaObj_preservesLimits (X : C) : PreservesLimitsOfSize.{v, v} (yoneda.obj X) := sorry

#check coyonedaFunctor_preservesLimits

theorem coyonedaEmbedding_preservesLimits :
    PreservesLimitsOfSize.{v, v} (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v) := sorry

#check coyonedaFunctor_reflectsLimits

theorem coyonedaEmbedding_reflectsLimits :
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

noncomputable def coproductDom (F : J ⥤ C) [HasCoproducts.{v} C] :
    ∐ (fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.1) ⟶ ∐ F.obj :=
  Sigma.desc fun f ↦ Sigma.ι F.obj f.1.1

noncomputable def coproductCod (F : J ⥤ C) [HasCoproducts.{v} C] :
    ∐ (fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.1) ⟶ ∐ F.obj :=
  Sigma.desc fun f ↦ F.map f.2 ≫ Sigma.ι F.obj f.1.2

#check HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit

noncomputable def coproductCoequalizerCocone (F : J ⥤ C) [HasCoproducts.{v} C] [HasCoequalizers C] :
    Cocone F where
  pt := coequalizer (coproductDom F) (coproductCod F)
  ι := {
    app j := Sigma.ι F.obj j ≫ coequalizer.π (coproductDom F) (coproductCod F)
    naturality := sorry
  }

#check HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit

noncomputable def isColimitCoproductCoequalizerCocone (F : J ⥤ C) [HasCoproducts.{v} C]
    [HasCoequalizers C] : IsColimit (coproductCoequalizerCocone F) := sorry

#check has_colimits_of_hasCoequalizers_and_coproducts

theorem hasColimits_of_hasCoproducts_of_hasCoequalizers [HasCoproducts.{v} C] [HasCoequalizers C] :
    HasColimitsOfSize.{v, v} C := sorry

-- 極限の形（双対）：等化子図式 lim F → ∏ Fj ⇉ ∏ F(cod f) を Mathlib 流に書いたもの
-- c₁ : ∏ Fj（脚 c₁.π.app ⟨j⟩ が射影 π_j）、c₂ : ∏ F(cod f)（脚 c₂.π.app ⟨f⟩ が射影 π_f）
-- 添字 f = ⟨(j, k), φ⟩ は J の射 φ : j ⟶ k で、f.1.1 = dom f、f.1.2 = cod f、f.2 = φ
-- 本の d が s、本の c が t で、hs は d の四角形 s ≫ π_f = π_j ≫ F.map φ、ht は c の三角形 t ≫ π_f = π_k
-- c₂ が積とは仮定しないので、s, t は成分から作らずに受け取り、成分を hs, ht で指定する
-- i : Fork s t が等化子の候補で、そこから F 上の錐を組む
#check Fan
#check HasLimitOfHasProductsOfHasEqualizers.buildLimit
noncomputable def buildLimit' {F : J ⥤ C} {c₁ : Fan F.obj}
    {c₂ : Fan (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)} (s t : c₁.pt ⟶ c₂.pt)
    (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
    (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
    (i : Fork s t) : Cone F where
  pt := i.pt
  π := {
    app j := i.ι ≫ c₁.π.app ⟨j⟩
    naturality {j j'} f := by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
      erw [ <- hs ⟨⟨j, j'⟩, f⟩, <- ht ⟨⟨j, j'⟩, f⟩]
      rw [<- Category.assoc, <- i.condition, Category.assoc]
  }




#check HasLimitOfHasProductsOfHasEqualizers.buildIsLimit
noncomputable def buildIsLimit' {F : J ⥤ C} {c₁ : Fan F.obj}
    {c₂ : Fan fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2} (s t : c₁.pt ⟶ c₂.pt)
    (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
    (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
    {i : Fork s t} (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) :
    IsLimit (buildLimit' s t hs ht i) where
  lift c := by
    -- simp [buildLimit']
    have := hi.lift
    let c' :=  Fan.mk c.pt (fun i => c.π.app i)
    let f := t₁.lift c'
    have Hf : f ≫ s = f ≫ t := by {
      simp only [f, c']; clear f
      apply t₂.hom_ext
      intro ⟨⟨j, j'⟩, f⟩
      simp only [Fan.mk_pt, Discrete.functor_obj_eq_as, Category.assoc]
      rw [hs, ht, t₁.fac, <- Category.assoc, t₁.fac]
      dsimp only [Discrete.functor_obj_eq_as, Fan.mk_pt, Fan.mk_π_app]
      exact c.w f
    }

    let j : Fork s t :=  Fork.ofι f Hf
    exact hi.lift j
  fac c j := by
    simp only [Fan.mk_pt, buildLimit']
    rw [<- i.app_zero_eq_ι]
    rw [<- Category.assoc, hi.fac]
    dsimp only [Fork.ofι_pt, Fork.ofι_π_app, Functor.const_obj_obj, parallelPair_obj_zero,
      parallelPair_obj_one]
    rw [t₁.fac]; rfl
  uniq c m w := by
    simp only [Fan.mk_pt, buildLimit'] at ⊢ m w
    apply hi.hom_ext; intro j
    rcases j
    · dsimp only [parallelPair_obj_zero, Fork.app_zero_eq_ι]
      rw [<- i.app_zero_eq_ι, hi.fac]
      dsimp only [Fork.app_zero_eq_ι, Fork.ofι_pt, Fork.ofι_π_app, Functor.const_obj_obj,
        parallelPair_obj_zero, parallelPair_obj_one]
      apply t₁.hom_ext; intro ⟨j⟩
      dsimp only [Discrete.functor_obj_eq_as]
      rw [Category.assoc, w, t₁.fac]; rfl
    · rw [hi.fac]
      dsimp only [parallelPair_obj_one, Fork.ofι_pt, Fork.ofι_π_app, Functor.const_obj_obj]
      apply t₂.hom_ext
      intro ⟨⟨j, j'⟩, f⟩
      rw [Category.assoc, i.app_one_eq_ι_comp_left, Category.assoc, hs]
      rw [<- Category.assoc, <- Category.assoc, Category.assoc m, w]
      rw [Category.assoc, hs, <- Category.assoc, t₁.fac]
      rfl



#check has_limits_of_hasEqualizers_and_products
theorem has_limits_of_hasEqualizers_and_products' [HasProducts.{v} C] [HasEqualizers C] :
    HasLimitsOfSize.{v, v} C := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.5.15
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
終対象 ∗ を持つ任意の圏において、A → ∗ ← B の引き戻しは A と B の積 A × B である。より一般に、
I で添字づけられた対象の族 (A_i) の積は、射の族 (! : A_i → ∗) の広い引き戻しとして構成できる。
したがって、引き戻しと終対象を持つ任意の圏はすべての有限積を持つ。
-/

#check isProductOfIsTerminalIsPullback

def isLimitBinaryFanOfPullbackTerminal {P A B T : C} (hT : IsTerminal T) (f : P ⟶ A) (g : P ⟶ B)
    (h : IsLimit (PullbackCone.mk f g (hT.hom_ext (f ≫ hT.from A) (g ≫ hT.from B)))) :
    IsLimit (BinaryFan.mk f g) where
  lift (s : BinaryFan A B) := h.lift (PullbackCone.mk s.fst s.snd (hT.hom_ext _ _))
  fac (s : BinaryFan A B) i := by
    have H1 := h.fac (PullbackCone.mk s.fst s.snd (hT.hom_ext _ _)) WalkingCospan.one
    have Hl := h.fac (PullbackCone.mk s.fst s.snd (hT.hom_ext _ _)) WalkingCospan.left
    have Hr := h.fac (PullbackCone.mk s.fst s.snd (hT.hom_ext _ _)) WalkingCospan.right
    simp only [Functor.const_obj_obj, cospan_one, PullbackCone.mk_π_app, IsTerminal.comp_from,
      cospan_left, cospan_right] at H1 Hl Hr
    obtain ⟨i⟩ := i
    rcases i
    · dsimp only [pair_obj_left, BinaryFan.mk_pt, Functor.const_obj_obj, BinaryFan.mk_fst]
      erw [Hl]
    · dsimp only [pair_obj_right, BinaryFan.mk_pt, Functor.const_obj_obj, BinaryFan.mk_snd]
      erw [Hr]
  uniq (s : BinaryFan A B) m w := by
    apply h.uniq (PullbackCone.mk s.fst s.snd (hT.hom_ext _ _))
    intro i; rcases i with _ | ⟨i, i⟩
    · simp only [Functor.const_obj_obj, cospan_one, PullbackCone.mk_π_app, IsTerminal.comp_from]
      apply hT.hom_ext
    · erw [w ⟨WalkingPair.left⟩]; rfl
    · erw [ w ⟨WalkingPair.right⟩]; rfl

#print WidePullbackShape
#check WidePullbackShape.wideCospan
#check WidePullbackCone
#check WidePullbackCone.π

def isLimitFanOfWidePullbackTerminal {I : Type v} (A : I → C) {T : C} (hT : IsTerminal T)
    (c : WidePullbackCone fun i ↦ hT.from (A i)) (hc : IsLimit c) :
    IsLimit (Fan.mk c.pt fun i ↦ c.π i) where
  lift s :=
    hc.lift (WidePullbackCone.mk (hT.from s.pt) (fun i =>  s.π.app ⟨i⟩) (fun i => hT.hom_ext _ _))
  fac s i := by
    apply hc.fac (WidePullbackCone.mk (hT.from s.pt) (fun i =>  s.π.app ⟨i⟩) (fun i => hT.hom_ext _ _)) (some i.as)
  uniq s m w := by
    rw [hc.uniq (WidePullbackCone.mk (hT.from s.pt) (fun i =>  s.π.app ⟨i⟩) (fun i => hT.hom_ext _ _)) m]
    intro j
    rcases j with _ | j
    · apply hT.hom_ext
    · simp only [WidePullbackCone.mk, WidePullbackShape.wideCospan_obj,
        WidePullbackShape.mkCone_π_app]
      rw [<- w ⟨j⟩]; rfl




#check hasBinaryProducts_of_hasTerminal_and_pullbacks

theorem hasBinaryProducts_of_hasTerminal_of_hasPullbacks [HasTerminal C] [HasPullbacks C] :
    HasBinaryProducts C where
  has_limit F := by
    let f := (terminal.from (F.obj ⟨WalkingPair.left⟩))
    let g := (terminal.from (F.obj ⟨WalkingPair.right⟩))
    refine {
    exists_limit := ⟨{
      cone := {
        pt := pullback f g
        π := {
          app := fun ⟨i⟩ => match i with
            | .left => pullback.fst f g
            | .right => pullback.snd f g
          naturality {i j} h := by
            obtain ⟨i⟩ := i
            obtain ⟨j⟩ := j
            obtain ⟨⟨rfl⟩⟩ := h
            simp
        }
      }
      isLimit := {
        lift s :=
          pullback.lift  (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) ( terminal.hom_ext _ _)
        fac s i := by
          obtain ⟨⟨_|_⟩⟩ := i
          · erw [pullback.lift_fst]
          · rw [pullback.lift_snd]
        uniq s m w := by
          simp only [Functor.const_obj_obj, Discrete.forall] at m w
          apply pullback.hom_ext
          · rw [w WalkingPair.left, pullback.lift_fst]
          · rw [w WalkingPair.right, pullback.lift_snd]
      }
    }⟩
  }

#check hasFiniteProducts_of_has_binary_and_terminal

theorem hasFiniteProducts_of_hasTerminal_of_hasPullbacks [HasTerminal C] [HasPullbacks C] :
    HasFiniteProducts C := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.5.16
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C を二項積を持つ圏とし、A, B を C の対象、f, g : A → B を平行な射の対とする。f と g が定める射
(f, g) : A → B × B と、対角射 δ = (id_B, id_B) : B → B × B の引き戻しを E とし、その射影を
e : E → A、ℓ : E → B とする。このとき E と e は f と g の等化子である。
-/

#check HasEqualizersOfHasPullbacksAndBinaryProducts.equalizerCone

-- e を f と g のフォークとして見た、補題の図式 E → A ⇉ B
def forkOfPullbackDiag {A B E : C} [HasBinaryProduct B B] {f g : A ⟶ B}
    {e : E ⟶ A} {l : E ⟶ B} (w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B)) :
    Fork f g := by
  apply Fork.ofι e
  rw [<- prod.lift_fst f g, <- Category.assoc, w, Category.assoc, prod.lift_fst]
  rw [<- prod.lift_snd f g, <- Category.assoc, w, Category.assoc, prod.lift_snd]

-- 積の表現可能な普遍性 Hom(X, B × B) ≅ Hom(X, B) × Hom(X, B)
noncomputable def homProdIso (B : C) [HasBinaryProduct B B] :
    yoneda.obj (B ⨯ B) ≅ yoneda.obj B ⨯ yoneda.obj B := by
  apply (prodIsProd B B).representableBy.toIso ≪≫ ?_ ≪≫ (FunctorToTypes.binaryProductIso _ _).symm
  refine {
    hom := {
      app x := TypeCat.ofHom (fun σ => ⟨σ.app ⟨WalkingPair.left⟩, σ.app ⟨WalkingPair.right⟩⟩)
      naturality {x y} f := by rfl
    }
    inv := {
      app x :=  TypeCat.ofHom (fun ⟨f, g⟩ => {
          app := fun ⟨i⟩ => match i with
            | .left => f
            | .right => g
          naturality {x y} f := by
            obtain ⟨x⟩ := x
            obtain ⟨y⟩ := y
            obtain ⟨⟨rfl⟩⟩ := f
            simp
      })
      naturality {x y} f := by
        simp only [Functor.cones_obj, FunctorToTypes.prod_map, yoneda_obj_obj, yoneda_obj_map,
          TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Functor.op_obj, Functor.const_obj_obj,
          Functor.cones_map];
        ext ⟨f, g⟩ ⟨i⟩
        rcases i<;> rfl
    }
    hom_inv_id := by
      ext x σ; apply NatTrans.ext; ext ⟨i⟩
      rcases i<;>rfl
    inv_hom_id := by
      ext x ⟨f, g⟩<;> rfl
  }

-- 引き戻しの錐を Hom(X, −) で移し、X 型の一般化された要素の錐として見る。
noncomputable def isLimitHomPullback {A B E : C} [HasBinaryProduct B B] {f g : A ⟶ B}
    {e : E ⟶ A} {l : E ⟶ B} (w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B))
    (h : IsLimit (PullbackCone.mk e l w)) (X : C) :
    IsLimit ((coyoneda.obj (op X)).mapCone (PullbackCone.mk e l w)) :=
  ((coyoneda_preservesLimits (op X)).preservesLimitsOfShape.preservesLimit.preserves h).some

-- 例3.2.9: Set の引き戻しの頂点は対の集合 Hom(X, E) ≅ {(a, b) | (f, g) ∘ a = (id, id) ∘ b}
noncomputable def homPairsIso {A B E : C} [HasBinaryProduct B B] {f g : A ⟶ B}
    {e : E ⟶ A} {l : E ⟶ B} (w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B)) (X : C)
    (H : IsLimit (PullbackCone.mk e l w)) :
    (X ⟶ E) ≅ {p : (X ⟶ A) × (X ⟶ B) // p.1 ≫ prod.lift f g = p.2 ≫ prod.lift (𝟙 B) (𝟙 B)} where
  hom := TypeCat.ofHom <| fun h => by
    use ⟨h ≫ e, h ≫ l⟩; simp only [prod.comp_lift, Category.assoc, Category.comp_id]
    apply prod.hom_ext
    · rw [prod.lift_fst, prod.lift_fst, <- prod.lift_fst f g]
      rw [<- Category.assoc e, w, Category.assoc, prod.lift_fst]
      simp
    · rw [prod.lift_snd, prod.lift_snd, <- prod.lift_snd f g]
      rw [<- Category.assoc e, w, Category.assoc, prod.lift_snd]
      simp
  inv := TypeCat.ofHom <| fun h => H.lift (PullbackCone.mk h.1.1 h.1.2 h.2)
  hom_inv_id := by
    ext h; simp only [TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, id_apply]
    erw [TypeCat.Fun.coe_mk]
    apply H.hom_ext; intro i
    have He := PullbackCone.IsLimit.lift_fst H (h ≫ e) (h ≫ l) (by rw [Category.assoc, w]; simp)
    have Hl := PullbackCone.IsLimit.lift_snd H (h ≫ e) (h ≫ l) (by rw [Category.assoc, w]; simp)
    simp only [PullbackCone.mk_π_app] at He Hl
    rcases i with _ | _ | _
    · simp only [cospan_one, PullbackCone.mk_π_app, Functor.const_obj_obj, prod.comp_lift]
      apply prod.hom_ext
      · conv => arg 1; erw [Category.assoc]; arg 2; erw [prod.lift_fst]
        conv => arg 2; erw [Category.assoc]; arg 2; erw [prod.lift_fst]
        conv => arg 1;  erw [<- Category.assoc, He]
        conv => arg 1; erw [Category.assoc]
        rfl
      · conv => arg 1; erw [Category.assoc]; arg 2; erw [prod.lift_snd]
        conv => arg 2; erw [Category.assoc]; arg 2; erw [prod.lift_snd]
        conv => arg 1;  erw [<- Category.assoc, He]
        conv => arg 1; erw [Category.assoc]
        rfl
    · simp only [cospan_left, PullbackCone.mk_π_app]
      erw [He]; rfl
    · simp only [cospan_right, PullbackCone.mk_π_app]
      erw [Hl]; rfl


  inv_hom_id := by
    ext ⟨⟨a, b⟩, h⟩
    · dsimp only at h
      simp only [TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, id_apply]
      erw [TypeCat.Fun.coe_mk]
      simp only
      exact PullbackCone.IsLimit.lift_fst H a b h
    · dsimp only at h
      simp only [TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, id_apply]
      erw [TypeCat.Fun.coe_mk]
      simp only
      exact PullbackCone.IsLimit.lift_snd H a b h


-- e との合成による同型 Hom(X, E) ≅ {a ∈ Hom(X, A) | f ∘ a = g ∘ a}
noncomputable def homEqualizerIso {A B E : C} [HasBinaryProduct B B] {f g : A ⟶ B}
    {e : E ⟶ A} {l : E ⟶ B} (w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B)) (X : C)
    (h : IsLimit (PullbackCone.mk e l w)) :
    (X ⟶ E) ≅ {a : X ⟶ A // a ≫ f = a ≫ g} := by
  apply homPairsIso w X h ≪≫ _
  refine {
    hom := TypeCat.ofHom <| fun ⟨⟨a, b⟩, W⟩ => by
      dsimp only at W
      use a
      rw [<- prod.lift_fst f g, <- Category.assoc, W, Category.assoc, prod.lift_fst, Category.comp_id]
      rw [<- prod.lift_snd f g, <- Category.assoc, W, Category.assoc, prod.lift_snd, Category.comp_id]
    inv := TypeCat.ofHom <| fun ⟨a, Ha⟩ => by
      use ⟨a, a ≫ f⟩
      simp only
      apply prod.hom_ext
      · rw [Category.assoc, prod.lift_fst, Ha]
        erw [Category.assoc, prod.lift_fst]
        simp
      · rw [Category.assoc, prod.lift_snd, Ha]
        erw [Category.assoc, prod.lift_snd]
        simp
    hom_inv_id := by
      ext ⟨⟨a,b⟩, H⟩
      · simp
      · dsimp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
        types_id_apply]
        rw [<- prod.lift_fst f g, <- Category.assoc, H, Category.assoc, prod.lift_fst, Category.comp_id]
    inv_hom_id := by
      ext ⟨a, Ha⟩
      simp
  }


-- Hom(X, E) → Hom(X, A) ⇉ Hom(X, B) は等化子図式
noncomputable def isLimitHomForkOfPullbackDiag {A B E : C} [HasBinaryProduct B B] {f g : A ⟶ B}
    {e : E ⟶ A} {l : E ⟶ B} (w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B)) (X : C)
    (h : IsLimit (PullbackCone.mk e l w)) :
    IsLimit ((coyoneda.obj (op X)).mapCone (forkOfPullbackDiag w)) := by
  let σ := homEqualizerIso w X h
  let p (s : Cone (parallelPair f g ⋙ coyoneda.obj (op X))) (x : s.pt) :
      {a : X ⟶ A // a ≫ f = a ≫ g} :=
    ⟨s.π.app .zero x, by
      have h1 := ConcreteCategory.congr_hom (s.w .left) x
      have h2 := ConcreteCategory.congr_hom (s.w .right) x
      simp at h1 h2
      exact h1.trans h2.symm⟩
  refine {
    lift s := TypeCat.ofHom fun x => σ.inv.hom (p s x)
    fac s i := by
      ext x
      simp only [Functor.comp_obj, Functor.flip_obj_obj, yoneda_obj_obj, forkOfPullbackDiag,
        Functor.mapCone_pt, Fork.ofι_pt, Functor.const_obj_obj, parallelPair_obj_zero,
        Functor.mapCone_π_app, Fork.ofι_π_app, parallelPair_obj_one, Functor.flip_obj_map,
        yoneda_map_app, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
      have E := congr_arg (fun t => (t.hom (p s x)).val) σ.inv_hom_id
      dsimp at E
      conv at E => arg 1; arg 1; arg 1; simp [σ, homEqualizerIso, homPairsIso]
      conv at E => arg 2; simp [p]
      simp only [comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk] at E
      rcases i
      · simp only [parallelPair_obj_zero]
        exact E
      · simp only [parallelPair_obj_one]
        rw [<- Category.assoc, E]
        have := ConcreteCategory.congr_hom (s.w .left) x
        dsimp at this
        exact this
    uniq s m W := by
      ext x
      simp only [Functor.mapCone_pt, Functor.flip_obj_obj, yoneda_obj_obj, TypeCat.Fun.toFun_apply,
        ConcreteCategory.hom_ofHom]
      erw [TypeCat.Fun.coe_mk, TypeCat.Fun.coe_mk]
      have H := congr_arg (fun t => (t.hom (m x))) σ.hom_inv_id
      conv at H => arg 1; arg 1; arg 1; arg 1; simp [σ, homEqualizerIso, homPairsIso]
      simp only [Category.assoc, Functor.mapCone_pt, Functor.flip_obj_obj, yoneda_obj_obj] at H
      erw [comp_apply] at H
      simp only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, comp_apply] at H
      simp only [Functor.mapCone_pt, Functor.flip_obj_obj, yoneda_obj_obj, TypeCat.Fun.toFun_apply,
        Functor.const_obj_obj, Functor.comp_obj, parallelPair_obj_zero, p]
      erw [<- H]
      congr
      have wo := W .zero; simp only [Functor.comp_obj, parallelPair_obj_zero, Functor.flip_obj_obj,
        yoneda_obj_obj, forkOfPullbackDiag, Functor.mapCone_pt, Fork.ofι_pt, Functor.mapCone_π_app,
        Fork.ofι_π_app, Functor.flip_obj_map, yoneda_map_app] at wo
      rw [<- wo]; rfl
  }


#check HasEqualizersOfHasPullbacksAndBinaryProducts.equalizerConeIsLimit

-- 定理3.5.5(ii): すべての X で Hom(X, −) が等化子図式に写すなら、元の図式も等化子
noncomputable def isLimitForkOfPullbackDiag {A B E : C} [HasBinaryProduct B B] {f g : A ⟶ B}
    {e : E ⟶ A} {l : E ⟶ B} (w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B))
    (hF : ∀ X : C, IsLimit ((coyoneda.obj (op X)).mapCone (forkOfPullbackDiag w))) :
    IsLimit (forkOfPullbackDiag w) := by
  have H : IsLimit (yoneda.mapCone (forkOfPullbackDiag w)) :=
    evaluationJointlyReflectsLimits (yoneda.mapCone (forkOfPullbackDiag w)) (fun X => hF X.unop)
  exact (yonedaEmbedding_reflectsLimits.reflectsLimitsOfShape.reflectsLimit.reflects H).some






-- WalkingParallelPair からの図式は、その 2 本の射が定める平行対と自然同型。本では明示されない Lean 側の補題
#check diagramIsoParallelPair

def diagramIsoParallelPair' (F : WalkingParallelPair ⥤ C) :
    F ≅ parallelPair (F.map .left) (F.map .right) where
  hom := {
    app i := by simp; exact 𝟙 (F.obj i)
    naturality {i j} f := by
      rcases f with _ | _ | _ | _<;> simp
  }

  inv := {
    app i := by simp; exact 𝟙 (F.obj i)
    naturality {i j} f := by
      rcases f with _ | _ | _ | _<;> simp
  }
  hom_inv_id := by
    ext i; simp
  inv_hom_id := by
    ext i; simp


#check hasEqualizers_of_hasPullbacks_and_binary_products

theorem hasEqualizers_of_hasBinaryProducts_of_hasPullbacks [HasBinaryProducts C] [HasPullbacks C] :
    HasEqualizers C where
  has_limit F := {
    exists_limit := .intro <| by
      let A := F.obj .zero
      let B := F.obj .one
      let f : A ⟶ B := F.map .left
      let g : A ⟶ B := F.map .right
      let E := pullback (prod.lift f g) (prod.lift (𝟙 B) (𝟙 B))
      let e : E ⟶ A := pullback.fst (prod.lift f g) (prod.lift (𝟙 B) (𝟙 B))
      let l : E ⟶ B := pullback.snd (prod.lift f g) (prod.lift (𝟙 B) (𝟙 B))
      have w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B)
        := pullback.condition (f := prod.lift f g) (g := prod.lift (𝟙 B) (𝟙 B))
      have H : IsLimit (forkOfPullbackDiag w) := by {
        apply isLimitForkOfPullbackDiag w
        intro x
        apply isLimitHomForkOfPullbackDiag w x (pullbackIsPullback (prod.lift f g) (prod.lift (𝟙 B) (𝟙 B)))
      }
      have σ := diagramIsoParallelPair F
      have := HasLimit.mk ⟨_, H⟩
      have :=  hasLimit_of_iso σ.symm
      exact getLimitCone F
  }

theorem hasEqualizers_of_hasBinaryProducts_of_hasPullbacks' [HasBinaryProducts C] [HasPullbacks C] :
    HasEqualizers C where
  has_limit F := by
    let A := F.obj .zero
    let B := F.obj .one
    let f : A ⟶ B := F.map .left
    let g : A ⟶ B := F.map .right
    let E := pullback (prod.lift f g) (prod.lift (𝟙 B) (𝟙 B))
    let e : E ⟶ A := pullback.fst (prod.lift f g) (prod.lift (𝟙 B) (𝟙 B))
    let l : E ⟶ B := pullback.snd (prod.lift f g) (prod.lift (𝟙 B) (𝟙 B))
    have w : e ≫ prod.lift f g = l ≫ prod.lift (𝟙 B) (𝟙 B)
      := pullback.condition (f := prod.lift f g) (g := prod.lift (𝟙 B) (𝟙 B))
    refine {
      exists_limit := Nonempty.intro <| {
        cone := {
          pt := E
          π := {
            app i := match i with
              | .zero => e
              | .one => l
            naturality {i j} h := match h with
              | .left => by
                simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
                change l = e ≫ f
                rw [<- prod.lift_fst f g, <- Category.assoc, w, Category.assoc, prod.lift_fst, Category.comp_id]
              | .right => by
                simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
                change l = e ≫ g
                rw [<- prod.lift_snd f g, <- Category.assoc, w, Category.assoc, prod.lift_snd, Category.comp_id]
              | .id i => by simp
          }
        }
        isLimit := {
          lift s := by
            apply pullback.lift (s.π.app .zero) (s.π.app .one) ?_
            simp only [Functor.const_obj_obj, prod.comp_lift]
            apply prod.hom_ext
            · rw [prod.lift_fst, prod.lift_fst, <- s.π.naturality .left]
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
              rw [Category.comp_id]
            · rw [prod.lift_snd, prod.lift_snd, <- s.π.naturality .right]
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
              rw [Category.comp_id]
          fac s i := by
            simp only [Functor.const_obj_obj]
            rcases i
            · simp only [e]
              rw [pullback.lift_fst]
            · simp only [l]
              rw [pullback.lift_snd]
          uniq s m W := by
            apply pullback.hom_ext
            · rw [W .zero, pullback.lift_fst]
            · rw [W .one, pullback.lift_snd]
        }
      }
    }











-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.5.17
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
図式が有限であるとは、その添字圏の射が有限個であることをいう。引き戻しと終対象を持つ任意の圏は、
すべての有限極限を持つ。双対に、押し出しと始対象を持つ任意の圏は、すべての有限余極限を持つ。
-/

#print FinCategory

class FinCategory' (J : Type v) [SmallCategory J] : Prop where
  finite_mor : Finite (Σ p : J × J, p.1 ⟶ p.2)

theorem finCategory'_iff (J : Type v) [SmallCategory J] :
    FinCategory' J ↔ Nonempty (FinCategory J) := sorry

#print HasFiniteLimits
#check hasFiniteLimits_of_hasTerminal_and_pullbacks

theorem hasFiniteLimits_of_hasTerminal_of_hasPullbacks [HasTerminal C] [HasPullbacks C] :
    HasFiniteLimits C := sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習 3.5.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- statement を置かない。本文の「(3.5.1) と演習3.5.i」の limHomIsoCones が受け持つ。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習 3.5.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- statement を置かない。「自分の言葉で説明せよ」型で、反例を見つけること自体が問いである。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習 3.5.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- statement を置かない。モノ射・エピ射の表現可能な定義を書くこと自体が解答になる。

end Riehl
