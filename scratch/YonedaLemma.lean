import Mathlib.CategoryTheory.Yoneda

/-!
# 米田の補題（2変数版）

`Hom(Hom(−, X), F)` と `F X` を、`X` と `F` の両方について関手と見て、その間の自然同型として
述べる。2.2 の `coyonedaLemma`（共変版・Mathlib に証明を委譲）の反変版にあたる。

置き場を決めていないスクラッチ。`Riehl.lean` からは import していない。
-/

open CategoryTheory Opposite

universe v₁ u₁

-- ev : (X, F) ↦ ULift (F X)
def myYonedaEvaluation (C : Type u₁) [Category.{v₁} C] :
    Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) where
  obj := fun x => ULift (x.snd.obj x.fst)
  map {x y} f := uliftFunctor.map (f.snd.app x.fst ≫ y.snd.map f.fst)
  map_id x := by
    simp; rfl
  map_comp {x y z} f g := by
    erw [<- Functor.map_comp]
    congr 1; simp

-- Hom(Hom(−, X), F) : (X, F) ↦ (yoneda.obj X.unop ⟶ F)
def myYonedaPairing (C : Type u₁) [Category.{v₁} C] :
    Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) where
obj x := yoneda.obj x.fst.unop ⟶ x.snd
map {x y} f := ↾ (fun σ => yoneda.map f.fst.unop ≫  σ ≫ f.snd)
map_id p := by ext; simp
map_comp {p q r} f g := by ext; simp



def myYonedaLemma (C : Type u₁) [Category.{v₁} C] :
    myYonedaPairing C ≅ myYonedaEvaluation C where
  hom := {
    app x := ↾ (fun σ => ⟨σ.app x.fst (𝟙 _)⟩)
    naturality {x y} f := by
      simp only [myYonedaEvaluation, myYonedaPairing]
      ext σ;
      simp only [yoneda_obj_obj, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom,
        TypeCat.Fun.coe_mk, NatTrans.comp_app, yoneda_map_app, Category.id_comp, uliftFunctor_map]
      rw [<- comp_apply, <- comp_apply, <- comp_apply]
      rw [<- f.2.naturality f.1, <- Category.assoc, <- σ.naturality f.1]
      simp
  }
  inv := {
    app p :=  ↾ fun x => {
      app y := ↾ fun g => p.2.map g.op x.down
      naturality a b f := by ext; simp
    }
    naturality p q f := by
      simp only [myYonedaEvaluation, myYonedaPairing]
      ext; simp
  }
  inv_hom_id := by
    -- apply NatTrans.ext
    ext ⟨c, F⟩ (Fc : ULift.{u₁, v₁} (F.obj c))
    simp only [myYonedaEvaluation, prod_Hom, yoneda_obj_obj, op_unop, NatTrans.comp_app,
      TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, NatTrans.id_app, id_apply]
    ext; simp only
    apply ConcreteCategory.congr_hom (F.map_id c) Fc.down
  hom_inv_id := by
    ext ⟨x, F⟩ σ
    simp only [myYonedaPairing, prod_Hom, yoneda_obj_obj, op_unop, NatTrans.comp_app,
      TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, NatTrans.id_app, id_apply] at σ ⊢
    ext y (f : unop y ⟶ unop x)
    simp only [yoneda_obj_obj, TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk]
    conv => arg 1; arg 2; change (ConcreteCategory.hom (σ.app x)) (𝟙 (unop x))
    rw [<- comp_apply, <- σ.naturality]
    simp
