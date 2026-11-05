import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# 極限を積の間の平行な射の対の等化子として作る

定理3.5.11 の極限の形（3.5）で使う、等化子図式 lim F → ∏ F j ⇉ ∏ F(cod f) から F 上の錐を作る
構成を、試しながら組むためのファイル。節に対応しない話題なので解説資料はない。

`S3_5_Representable.lean` の `buildLimit'` と名前がぶつからないように、名前空間
`Riehl.LimitAsEqualizer` に置く。
-/

open CategoryTheory Limits

namespace Riehl.LimitAsEqualizer

universe w v u

variable {J : Type w} [SmallCategory J] {C : Type u} [Category.{v} C]

#check HasLimitOfHasProductsOfHasEqualizers.buildLimit

noncomputable def sMap (F : J ⥤ C) [HasProduct F.obj]
    [HasProduct (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] :
    ∏ᶜ F.obj ⟶ ∏ᶜ (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2) :=
  Pi.lift (fun p => Pi.π F.obj p.1.1 ≫ F.map p.2)

noncomputable def tMap (F : J ⥤ C) [HasProduct F.obj]
    [HasProduct (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] :
    ∏ᶜ F.obj ⟶ ∏ᶜ (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2) :=
  Pi.lift (fun p => Pi.π F.obj p.1.2)

theorem sMap_comp_π (F : J ⥤ C) [HasProduct F.obj]
    [HasProduct (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] (f : Σ p : J × J, p.1 ⟶ p.2) :
    sMap F ≫ Pi.π (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2) f =
      Pi.π F.obj f.1.1 ≫ F.map f.2 :=
  Pi.lift_comp_π _ _

theorem tMap_comp_π (F : J ⥤ C) [HasProduct F.obj]
    [HasProduct (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)] (f : Σ p : J × J, p.1 ⟶ p.2) :
    tMap F ≫ Pi.π (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2) f = Pi.π F.obj f.1.2 :=
  Pi.lift_comp_π _ _

noncomputable def build {F : J ⥤ C}
    [HasProduct F.obj] [HasProduct (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)]
    (i : Fork (sMap F) (tMap F)) :
    Cone F where
  pt := i.pt
  π := {
    app j := i.ι ≫ Pi.π F.obj j
    naturality {j j'} f := by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
      rw [<- sMap_comp_π F ⟨⟨j, j'⟩, f⟩, <- tMap_comp_π F ⟨⟨j, j'⟩, f⟩]
      rw [<- Category.assoc, <- i.condition]; simp
  }

noncomputable def buildIsLimit (F : J ⥤ C)
    [HasProduct F.obj] [HasProduct (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)]
    [HasEqualizer (sMap F) (tMap F)] :
    IsLimit (build (equalizer.fork (sMap F) (tMap F))) where
  lift s := by
    apply equalizer.lift (f := sMap F) (g := tMap F) (Pi.lift s.π.app)
    apply Pi.hom_ext
    intro p
    rw [Category.assoc, Category.assoc, sMap_comp_π, tMap_comp_π]
    rw [Pi.lift_comp_π, <- Category.assoc, Pi.lift_comp_π]
    rw [<- s.π.naturality p.2]; simp
  fac s j := by
    simp only [build]
    erw [<- Category.assoc, equalizer.lift_ι, Pi.lift_comp_π]
  uniq s m w := by
    apply equalizer.hom_ext
    apply Pi.hom_ext; intro j
    simp only [build] at w
    erw [Category.assoc, w]
    rw [equalizer.lift_ι, Pi.lift_comp_π]

-- 2 つの積と等化子があれば、F は極限を持つ
#check hasLimit_of_equalizer_and_product

theorem hasLimit_of_hasProducts_of_hasEqualizer {F : J ⥤ C}
    [HasProduct F.obj] [HasProduct (fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.2)]
    [HasEqualizer (sMap F) (tMap F)] :
    HasLimit F := HasLimit.mk ⟨_, buildIsLimit F⟩

-- 小さい積と等化子を持つ圏は、すべての小さい極限を持つ
#check has_limits_of_hasEqualizers_and_products

theorem has_limits_of_hasEqualizers_and_products' [HasProducts.{v} C] [HasEqualizers C] :
    HasLimitsOfSize.{v, v} C where
  has_limits_of_shape _ _ := {
    has_limit F := hasLimit_of_hasProducts_of_hasEqualizer (F := F) 
  }

-- 有限版：有限積と等化子を持つ圏は、すべての有限極限を持つ
#check hasFiniteLimits_of_hasEqualizers_and_finite_products

theorem hasFiniteLimits_of_hasFiniteProducts_of_hasEqualizers [HasFiniteProducts C]
    [HasEqualizers C] : HasFiniteLimits C where
  out J SJ FJ := by
    obtain ⟨HJ, FJ⟩ := FJ
    refine {
      has_limit F := hasLimit_of_hasProducts_of_hasEqualizer (F := F)
    }









end Riehl.LimitAsEqualizer
