import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Equivalence
import Riehl.Ch4_Adjunctions.S4_2_UnitCounit

/-!
# 4.3 随伴の計算

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 節冒頭の引用、Remark 4.3.9（構文的な証明と米田流の証明の適用範囲）、
脚注6〜9 は載せない。
-/

open CategoryTheory Functor Opposite

namespace Riehl

universe v u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

variable {F : C ⥤ D} {G : D ⥤ C}

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
F と F′ がともに G の左随伴ならば、自然同型 θ : F ≅ F′ であって、2 つの随伴の単位と Gθ ⋅ η = η′
を満たし、余単位と ε′ ⋅ θG = ε を満たすものが、ただ 1 つ存在する。

η, ε は F ⊣ G の単位と余単位、η′, ε′ は F′ ⊣ G の単位と余単位である。一意性は、本文の証明に
合わせて、単位との等式を満たす自然変換 F ⇒ F′ が θ に限ることとして書く。

statement の項 := 本の記法
  whiskerRight θ G    := Gθ
  whiskerLeft G θ     := θG
-/

section

variable {F' : C ⥤ D}

#print Adjunction.leftAdjointUniq
#check conjugateIsoEquiv

-- G の 2 つの左随伴 F, F′ の間の自然同型 θ : F ≅ F′
def leftAdjointUniq' (σ : F ⊣ G) (τ : F' ⊣ G) : F ≅ F' where
  hom := whiskerRight τ.unit F ≫ F'.whiskerLeft σ.counit
  inv := whiskerRight σ.unit F' ≫ F.whiskerLeft τ.counit
  hom_inv_id := by
    ext c
    dsimp only [NatTrans.comp_app, comp_obj, whiskerRight_app, id_obj, whiskerLeft_app,
      NatTrans.id_app]
    rw [Category.assoc, <- σ.counit_naturality_assoc]
    rw [<- Category.assoc, <- F.map_comp, τ.unit_naturality]
    rw [<- σ.counit_naturality]
    rw [<- Category.assoc, <- F.map_comp, Category.assoc]
    rw [τ.right_triangle_components (F.obj c), Category.comp_id]
    rw [σ.left_triangle_components]
  inv_hom_id := by
    ext c
    dsimp only [NatTrans.comp_app, comp_obj, whiskerRight_app, id_obj, whiskerLeft_app,
      NatTrans.id_app]
    rw [Category.assoc, <- τ.counit_naturality_assoc]
    rw [<- Category.assoc, <- F'.map_comp, σ.unit_naturality]
    rw [<- τ.counit_naturality]
    rw [<- Category.assoc, <- F'.map_comp, Category.assoc]
    rw [σ.right_triangle_components, Category.comp_id]
    rw [τ.left_triangle_components]





#check Adjunction.unit_leftAdjointUniq_hom

-- θ は単位と可換: Gθ ⋅ η = η′
theorem unit_leftAdjointUniq_hom' (σ : F ⊣ G) (τ : F' ⊣ G) :
    σ.unit ≫ whiskerRight (leftAdjointUniq' σ τ).hom G = τ.unit := by
  dsimp [leftAdjointUniq']
  ext c; dsimp only [id_obj, comp_obj, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  rw [G.map_comp, σ.unit_naturality_assoc, σ.right_triangle_components]
  simp


#check Adjunction.leftAdjointUniq_hom_counit

-- θ は余単位と可換: ε′ ⋅ θG = ε
theorem leftAdjointUniq_hom_counit' (σ : F ⊣ G) (τ : F' ⊣ G) :
    whiskerLeft G (leftAdjointUniq' σ τ).hom ≫ τ.counit = σ.counit := by
  ext d; dsimp only [comp_obj, id_obj, leftAdjointUniq', whiskerLeft_comp, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app]
  rw [Category.assoc, <- σ.counit_naturality]
  rw [<- Category.assoc, <- F.map_comp, τ.right_triangle_components]
  simp


-- 単位と可換な自然変換 F ⇒ F′ は θ に限る
theorem eq_leftAdjointUniq_hom_of_unit (σ : F ⊣ G) (τ : F' ⊣ G)
    (θ : F ⟶ F') (h : σ.unit ≫ whiskerRight θ G = τ.unit) :
    θ = (leftAdjointUniq' σ τ).hom := by
  have H := σ.unit_leftAdjointUniq_hom τ
  have H2 := σ.leftAdjointUniq_hom_counit τ
  ext c; dsimp [leftAdjointUniq']
  rw [<- h]; dsimp
  rw [F.map_comp, Category.assoc, σ.counit_naturality, σ.left_triangle_components_assoc]



/-
本文の 2 つ目の証明は、同じ自然同型を米田の補題から得る。各 c ∈ C について、2 つの随伴の転置を
合成した、d について自然な同型

  D(F′c, d) ≅ C(c, Gd) ≅ D(Fc, d)        (4.3.2)

があり、米田の補題によって、これは同型 θ_c : Fc ≅ F′c による前合成である。θ_c は 1_{F′c} の像で、
1 つ目の証明の式 ε_{F′c} ⋅ Fη′_c に一致する。

statement の項 := 本の記法
  coyoneda.obj (op (F'.obj c))    := D(F′c, −)
  coyoneda.obj (op (F.obj c))     := D(Fc, −)
-/

-- (4.3.2) の自然同型 D(F′c, −) ≅ D(Fc, −)
def coyonedaObjIsoOfLeftAdjoints (σ : F ⊣ G) (τ : F' ⊣ G) (c : C) :
    coyoneda.obj (op (F'.obj c)) ≅ coyoneda.obj (op (F.obj c)) := by
  let T := fun d => (σ.homEquiv c d).trans (τ.homEquiv c d).symm
  apply NatIso.ofComponents ?_ ?_
  · simp only [flip_obj_obj, yoneda_obj_obj]
    intro d
    refine {
      hom := TypeCat.ofHom (T d).symm
      inv := TypeCat.ofHom (T d)
      hom_inv_id := by ext f; simp
      inv_hom_id := by ext g; simp
    }
  · intro x y f; ext g; simp at g
    simp only [flip_obj_obj, yoneda_obj_obj, flip_obj_map, yoneda_map_app, Equiv.symm_trans,
      Equiv.symm_symm, Equiv.coe_trans, id_eq, TypeCat.Fun.toFun_apply, comp_apply,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Function.comp_apply, T]
    rw [σ.homEquiv_symm_apply, σ.homEquiv_symm_apply]
    rw [Category.assoc, <- σ.counit_naturality]
    rw [<- Category.assoc, <- F.map_comp, τ.homEquiv_apply, τ.homEquiv_apply]
    simp

-- (4.3.2) から米田の補題で得る自然同型 θ : F ≅ F′
def leftAdjointUniqOfYoneda (σ : F ⊣ G) (τ : F' ⊣ G) : F ≅ F' := by
  apply NatIso.ofComponents ?_ ?_
  · intro c
    apply Iso.unop
    apply Coyoneda.fullyFaithful.preimageIso
    apply (coyonedaObjIsoOfLeftAdjoints σ τ c)
  · intro x y f
    apply Quiver.Hom.op_inj
    simp only [Iso.unop_hom, FullyFaithful.preimageIso_hom, op_comp, Quiver.Hom.op_unop]
    apply coyoneda.map_injective
    rw [coyoneda.map_comp, Coyoneda.fullyFaithful.map_preimage]
    rw [coyoneda.map_comp,  Coyoneda.fullyFaithful.map_preimage]
    ext d g
    simp only [flip_obj_obj, yoneda_obj_obj, coyonedaObjIsoOfLeftAdjoints, Equiv.symm_trans,
      Equiv.symm_symm, Equiv.coe_trans, id_eq, NatTrans.comp_app, NatIso.ofComponents_hom_app,
      flip_map_app, yoneda_obj_map, Quiver.Hom.unop_op, TypeCat.Fun.toFun_apply, comp_apply,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Function.comp_apply]
    rw [σ.homEquiv_symm_apply, σ.homEquiv_symm_apply]
    rw [τ.homEquiv_apply, τ.homEquiv_apply]
    rw [F.map_comp, Category.assoc, σ.counit_naturality]
    rw [F.map_comp, Category.assoc, σ.counit_naturality]
    rw [<- Category.assoc, <- F.map_comp, <- τ.unit_naturality]
    rw [F.map_comp, Category.assoc, σ.counit_naturality_assoc]


-- θ_c = ε_{F′c} ⋅ Fη′_c
theorem leftAdjointUniqOfYoneda_hom_app (σ : F ⊣ G) (τ : F' ⊣ G)
    (c : C) :
    (leftAdjointUniqOfYoneda σ τ).hom.app c =
      F.map (τ.unit.app c) ≫ σ.counit.app (F'.obj c) := by
  simp only [leftAdjointUniqOfYoneda, NatIso.ofComponents_hom_app, Iso.unop_hom,
    FullyFaithful.preimageIso_hom, id_obj, comp_obj]
  apply Quiver.Hom.op_inj
  simp only [Quiver.Hom.op_unop, op_comp]
  apply coyoneda.map_injective
  rw [Coyoneda.fullyFaithful.map_preimage]
  ext d f
  simp only [flip_obj_obj, yoneda_obj_obj, coyonedaObjIsoOfLeftAdjoints, Equiv.symm_trans,
    Equiv.symm_symm, Equiv.coe_trans, id_eq, NatIso.ofComponents_hom_app, TypeCat.hom_ofHom,
    TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk, Function.comp_apply, map_comp, NatTrans.comp_app,
    flip_map_app, yoneda_obj_map, Quiver.Hom.unop_op, comp_apply]
  rw [τ.homEquiv_apply, σ.homEquiv_symm_apply]
  rw [F.map_comp, Category.assoc, σ.counit_naturality]




end

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 随伴 F ⊣ G（F : C ⇄ D : G）と F′ ⊣ G′（F′ : D ⇄ E : G′）が与えられたとき、合成 F′F は
-- 合成 GG′ の左随伴である。

#check Adjunction.comp

-- F′F ⊣ GG′
def compAdjunction {E : Type u₃} [Category.{v} E] {F' : D ⥤ E} {G' : E ⥤ D} (σ : F ⊣ G)
    (τ : F' ⊣ G') : F ⋙ F' ⊣ G' ⋙ G where
  unit := σ.unit ≫ Functor.whiskerRight (F.whiskerLeft  τ.unit) G
  counit := Functor.whiskerRight (G'.whiskerLeft σ.counit) F' ≫ τ.counit
  left_triangle_components c := by
    simp only [comp_obj, NatTrans.comp_app, id_obj, whiskerRight_app, whiskerLeft_app,
      Functor.comp_map, map_comp, Category.assoc]
    rw [<- Category.assoc (F'.map (F.map (G.map _))), <- F'.map_comp]
    rw [σ.counit_naturality]
    rw [<- Category.assoc, <- F'.map_comp]
    rw [σ.left_triangle_components_assoc, τ.left_triangle_components]
  right_triangle_components e := by
    simp only [comp_obj, NatTrans.comp_app, id_obj, whiskerRight_app, whiskerLeft_app,
      Functor.comp_map, map_comp, Category.assoc]
    rw [<- Category.assoc (G.map _), <- G.map_comp]
    rw [τ.unit_naturality, <- G.map_comp]
    rw [Category.assoc, τ.right_triangle_components]
    rw [Category.comp_id, σ.right_triangle_components]



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
向かい合う関手 F : C ⇄ D : G と自然変換 η : id_C ⇒ GF, ε : FG ⇒ id_D について、合成
φ ≔ εF ⋅ Fη : F ⇒ F と ψ ≔ Gε ⋅ ηG : G ⇒ G がどちらも可逆ならば、η を単位とする随伴 F ⊣ G が
存在し、ε を余単位とする随伴 F ⊣ G も存在する。

三角等式は φ = 1_F かつ ψ = 1_G という主張である。仮定は φ と ψ が可逆であることだけなので、
η と ε の組は一般には随伴にならない。η を単位とする随伴の余単位は ε を補正した自然変換で、ε を
余単位とする随伴の単位は η を補正した自然変換である。この 2 つの随伴は一般に異なる。

補正した自然変換と、それを使う随伴を、別の宣言にする。

statement の項 := 本の記法
  whiskerRight η F ≫ whiskerLeft F ε    := φ = εF ⋅ Fη
  whiskerLeft G η ≫ whiskerRight ε G    := ψ = Gε ⋅ ηG
-/


-- η を単位とする随伴 F ⊣ G
noncomputable def adjunctionOfUnit (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    [IsIso (whiskerRight η F ≫ whiskerLeft F ε)]
    [IsIso (whiskerLeft G η ≫ whiskerRight ε G)] : F ⊣ G where
  unit := η
  counit := Functor.whiskerRight (inv (G.whiskerLeft η ≫ whiskerRight ε G)) F ≫ ε
  left_triangle_components c := by
    set ψ := (whiskerRight η F ≫ F.whiskerLeft ε)
    set φ := (G.whiskerLeft η ≫ whiskerRight ε G)
    set ε' := Functor.whiskerRight (inv φ) F ≫ ε
    have E : ε =  Functor.whiskerRight φ F ≫ ε' := by {
      dsimp [ε']
      rw [<- Category.assoc, <- whiskerRight_comp, IsIso.hom_inv_id, whiskerRight_id']
      simp
    }
    have Hc := NatIso.isIso_app_of_isIso ψ c
    rw [<- cancel_mono (ψ.app c), Category.id_comp]
    have := ε'.naturality (ψ.app c)
    simp only [comp_obj, id_obj, Functor.comp_map, Functor.id_map] at this
    rw [Category.assoc, <- this]; clear this
    simp only [comp_obj, id_obj, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, map_comp,
      Category.assoc, ψ]
    rw [<- Category.assoc, <- F.map_comp]
    have := η.naturality (η.app c); dsimp at this
    rw [<- this]; clear this
    simp only [map_comp, NatTrans.comp_app, comp_obj, id_obj, whiskerRight_app,
      NatIso.isIso_inv_app, map_inv, Category.assoc, ε']
    rw [<- Category.assoc (F.map (η.app (G.obj (F.obj c))))]
    rw [<- Category.assoc _ (inv _), <- F.map_comp]
    conv => arg 1; arg 2; arg 1; arg 1; change (F.map (φ.app (F.obj c)))
    rw [IsIso.hom_inv_id]; simp

  right_triangle_components d := by
    have H := congr_app (IsIso.inv_hom_id (G.whiskerLeft η ≫ whiskerRight ε G)) d
    set σ := (CategoryTheory.inv (G.whiskerLeft η ≫ whiskerRight ε G))
    simp only [comp_obj, id_obj, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      NatTrans.id_app, map_comp] at H ⊢
    erw [<- η.naturality_assoc (σ.app d), H]


/-
次の 2 つは、η を単位とする随伴 F ⊣ G を、定理4.2.7 の (iii) から得る。`homNatTransOfUnit η` は
4.2 で定義した (4.2.8) の自然変換 Hom(F-, -) ⇒ Hom(-, G-) である。
-/

-- φ と ψ が可逆ならば、(4.2.8) の自然変換は同型
theorem isIso_homNatTransOfUnit_of_isIso (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    [IsIso (whiskerRight η F ≫ whiskerLeft F ε)]
    [IsIso (whiskerLeft G η ≫ whiskerRight ε G)] : IsIso (homNatTransOfUnit η) := by
  use homNatTransOfCounit ε ≫  Functor.whiskerRight (NatTrans.op (inv (whiskerRight η F ≫ F.whiskerLeft ε))) coyoneda
  constructor
  · ext c d f
    dsimp [homNatTransOfUnit, homNatTransOfCounit]
    simp only [NatIso.isIso_inv_app, comp_obj, id_obj, NatTrans.comp_app, whiskerRight_app,
      whiskerLeft_app, map_comp, Category.assoc, IsIso.inv_comp_eq]
    erw [ε.naturality f]; rfl
  · ext c d f
    dsimp [homNatTransOfUnit, homNatTransOfCounit]
    set ψ :=  (whiskerRight η F ≫ F.whiskerLeft ε)
    conv => arg 1; arg 2; arg 2; arg 1; arg 1; change inv ψ
    simp only [NatIso.isIso_inv_app, comp_obj, id_obj, map_comp, map_inv]
    have Hd := NatIso.isIso_app_of_isIso (G.whiskerLeft η ≫ whiskerRight ε G) d
    simp at Hd
    rw [<- cancel_mono (η.app (G.obj d) ≫ G.map (ε.app d))]
    simp only [id_obj, comp_obj, Category.assoc]
    erw [η.naturality_assoc, η.naturality_assoc]
    simp only [id_obj, comp_obj, Functor.comp_map]
    slice_lhs 2 3 => erw [η.naturality (CategoryTheory.inv (G.map (ψ.app (unop c))))]
    simp only [comp_obj, id_obj, Functor.comp_map, map_inv, Category.assoc]
    erw [η.naturality_assoc]; simp only [id_obj, comp_obj, Functor.comp_map]
    slice_lhs 5 6 => erw [<- G.map_comp, ε.naturality]
    simp only [comp_obj, id_obj, Functor.id_map, map_comp]
    slice_lhs 4 5 => erw [<- G.map_comp, ε.naturality]
    simp only [comp_obj, id_obj, Functor.id_map, map_comp, Category.assoc]
    rw [<- map_inv, <- map_inv, <- map_inv]
    slice_lhs 3 4 => erw [<- G.map_comp, ε.naturality]
    simp only [comp_obj, id_obj, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.id_map, map_comp, map_inv, Category.assoc, ψ]
    slice_lhs 2 4 => rw [<- Category.assoc, IsIso.hom_inv_id]
    simp only [Category.id_comp]
    erw [<- η.naturality_assoc f]; simp




-- η を単位とする随伴 F ⊣ G（定理4.2.7 の (iii) から）
noncomputable def adjunctionOfUnitOfHomNatTrans (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    [IsIso (whiskerRight η F ≫ whiskerLeft F ε)]
    [IsIso (whiskerLeft G η ≫ whiskerRight ε G)] : F ⊣ G := by
  apply adjunctionOfCoreHomEquiv
  haveI := isIso_homNatTransOfUnit_of_isIso η ε
  apply coreHomEquivOfIsIsoHomNatTransOfUnit η



-- ε を余単位とする随伴 F ⊣ G
noncomputable def adjunctionOfCounit (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    [IsIso (whiskerRight η F ≫ whiskerLeft F ε)]
    [IsIso (whiskerLeft G η ≫ whiskerRight ε G)] : F ⊣ G := sorry







-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系4.3.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の圏同値 F : C ⇄ D : G, η : id_C ≅ GF, ε : FG ≅ id_D は、η と ε の一方を取り替えて
随伴同値にできる。随伴同値とは、η と ε が三角等式を満たす圏同値である。

本の圏同値にあたる型は Mathlib にない。
本の随伴同値は Mathlib の圏同値 `C ≌ D` にあたる。
-/

#check Equivalence.mk

#check Functor.whiskerLeft_id'
-- 恒等自然変換 1_K に関手 H を先に合成した 1_K H は、恒等自然変換 1_{KH}
theorem whiskerLeft_id'' {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B]
    {E : Type u₃} [Category.{v} E] (H : A ⥤ B) {K : B ⥤ E} :
    whiskerLeft H (𝟙 K) = 𝟙 (H ⋙ K) := by
  ext a; dsimp only [comp_obj,  NatTrans.id_app]
  rw [whiskerLeft_app, NatTrans.id_app]


#check Functor.whiskerLeft_comp
-- 自然変換の合成 α ≫ β に関手 H を先に合成した (α ≫ β)H は、αH ≫ βH
theorem whiskerLeft_comp' {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B]
    {E : Type u₃} [Category.{v} E] (H : A ⥤ B) {K L M : B ⥤ E} (α : K ⟶ L) (β : L ⟶ M) :
    whiskerLeft H (α ≫ β) = whiskerLeft H α ≫ whiskerLeft H β := by
  ext a
  rw [NatTrans.comp_app, whiskerLeft_app, whiskerLeft_app, whiskerLeft_app]
  rw [NatTrans.comp_app]


#check Functor.isoWhiskerLeft
-- 自然同型 α : K ≅ L に関手 H を先に合成した自然同型 αH : KH ≅ LH
def isoWhiskerLeft' {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B]
    {E : Type u₃} [Category.{v} E] (H : A ⥤ B) {K L : B ⥤ E} (σ : K ≅ L) :
    H ⋙ K ≅ H ⋙ L where
  hom := H.whiskerLeft σ.hom
  inv := H.whiskerLeft σ.inv
  hom_inv_id := by
    rw [<- whiskerLeft_comp, σ.hom_inv_id, whiskerLeft_id']
  inv_hom_id := by
    rw [<- whiskerLeft_comp, σ.inv_hom_id, whiskerLeft_id']

#check Functor.isoWhiskerRight
-- 自然同型 α : K ≅ L に関手 H を後に合成した自然同型 Hα : HK ≅ HL
def isoWhiskerRight' {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B]
    {E : Type u₃} [Category.{v} E] {K L : A ⥤ B} (α : K ≅ L) (H : B ⥤ E) :
    K ⋙ H ≅ L ⋙ H := sorry

-- η を単位に残して作る随伴同値
noncomputable def equivalenceOfUnitIso (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D := by
  let σ := adjunctionOfUnitOfHomNatTrans η.hom ε.hom
  refine {
    functor := F
    inverse := G
    unitIso := η
    counitIso := {
      hom := σ.counit
      inv := ε.inv ≫ whiskerRight (G.whiskerLeft σ.unit ≫ whiskerRight ε.hom G) F

      hom_inv_id := by
        set inv := ε.inv ≫ whiskerRight (G.whiskerLeft σ.unit ≫ whiskerRight ε.hom G) F
        have H : IsIso inv := by {
          simp only [inv]
          have : σ.unit = η.hom := by {
            ext c
            simp [σ, adjunctionOfUnitOfHomNatTrans, adjunctionOfCoreHomEquiv, unitOfCoreHomEquiv, coreHomEquivOfIsIsoHomNatTransOfUnit, homNatTransOfUnit]
          }
          rw [this]
          simp only [whiskerRight_comp, whiskerRight_twice, isIso_comp_left_iff,
            MorphismProperty.isomorphisms.iff]
          exact NatIso.isIso_of_isIso_app ((𝟭 D).associator G F).inv
        }
        rw [<- cancel_epi inv]
        have : inv ≫ σ.counit = 𝟙 _ := by {
          ext d
          dsimp only [id_obj, whiskerLeft_comp, NatTrans.comp_app, comp_obj, whiskerLeft_app,
            whiskerRight_app, NatTrans.id_app, inv]
          rw [F.map_comp, Category.assoc, Category.assoc, σ.counit_naturality]
          rw [<- Category.assoc (F.map _), σ.left_triangle_components]
          rw [Category.id_comp, ε.inv_hom_id_app]
          simp
        }
        rw [<- Category.assoc, this]
        erw [Category.id_comp, Category.comp_id]
      inv_hom_id := by
        ext d
        dsimp only [id_obj, whiskerLeft_comp, NatTrans.comp_app, comp_obj, whiskerLeft_app,
          whiskerRight_app, NatTrans.id_app]
        rw [F.map_comp, Category.assoc, Category.assoc, σ.counit_naturality]
        rw [<- Category.assoc (F.map _), σ.left_triangle_components]
        rw [Category.id_comp, ε.inv_hom_id_app]
        simp


    }

    functor_unitIso_comp c := by
      simp only
      have : σ.unit = η.hom := by {
        ext c; simp [σ, adjunctionOfUnitOfHomNatTrans, adjunctionOfCoreHomEquiv, unitOfCoreHomEquiv, coreHomEquivOfIsIsoHomNatTransOfUnit, homNatTransOfUnit]
      }
      rw [<- this]
      exact σ.left_triangle_components c
  }






-- ε を余単位に残して作る随伴同値
noncomputable def equivalenceOfCounitIso (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
随伴 F ⊣ G（F : C ⥤ D, G : D ⥤ C）が与えられたとき、任意の小圏 J について、F を後ろに合成する
関手 (H : J ⥤ C) ↦ H ⋙ F は、G を後ろに合成する関手 (H : J ⥤ D) ↦ H ⋙ G の左随伴である。
また、任意の局所小圏 E について、G を前に合成する関手 (H : C ⥤ E) ↦ G ⋙ H は、F を前に合成する
関手 (H : D ⥤ E) ↦ F ⋙ H の左随伴である。

J と E の大きさについての仮定は、関手圏を局所小にするためのもので、宣言には置かない。

statement の項 := 本の記法
  (whiskeringRight J C D).obj F    := (H : J ⥤ C) ↦ H ⋙ F
  (whiskeringRight J D C).obj G    := (H : J ⥤ D) ↦ H ⋙ G
  (whiskeringLeft D C E).obj G     := (H : C ⥤ E) ↦ G ⋙ H
  (whiskeringLeft C D E).obj F     := (H : D ⥤ E) ↦ F ⋙ H
-/


-- (H ↦ H ⋙ F) ⊣ (H ↦ H ⋙ G)
def whiskerRightAdjunction (J : Type u₃) [Category.{v} J] (σ : F ⊣ G) :
    (whiskeringRight J C D).obj F ⊣ (whiskeringRight J D C).obj G where
  unit := {
    app H := H.whiskerLeft σ.unit
    naturality {H H'} τ := by
      ext j
      simp only [id_obj, comp_obj, whiskeringRight_obj_obj, Functor.id_map, NatTrans.comp_app,
        whiskerLeft_app, Functor.comp_map, whiskeringRight_obj_map, whiskerRight_twice,
        associator_hom_app, whiskerRight_app, associator_inv_app, Category.comp_id,
        Category.id_comp]
      erw [σ.unit_naturality (τ.app j)]
    }
  counit := {
    app H := H.whiskerLeft σ.counit
    naturality {H H'} τ := by
      ext j
      simp only [comp_obj, whiskeringRight_obj_obj, id_obj, Functor.comp_map,
        whiskeringRight_obj_map, whiskerRight_twice, Category.assoc, NatTrans.comp_app,
        associator_hom_app, whiskerRight_app, associator_inv_app, whiskerLeft_app, Category.id_comp,
        Functor.id_map]
      rw [σ.counit_naturality]
  }
  left_triangle_components H := by
    ext j
    dsimp only [whiskeringRight_obj_obj, comp_obj, whiskeringRight_obj_map, NatTrans.comp_app,
      whiskerRight_app, whiskerLeft_app, NatTrans.id_app]
    rw [σ.left_triangle_components]
  right_triangle_components H := by
    ext j
    dsimp only [whiskeringRight_obj_obj, comp_obj, whiskeringRight_obj_map, NatTrans.comp_app,
      whiskerLeft_app, whiskerRight_app, NatTrans.id_app]
    rw [σ.right_triangle_components]





#check Adjunction.whiskerLeft

-- (H ↦ G ⋙ H) ⊣ (H ↦ F ⋙ H)
def whiskerLeftAdjunction (E : Type u₃) [Category.{v} E] (σ : F ⊣ G) :
    (whiskeringLeft D C E).obj G ⊣ (whiskeringLeft C D E).obj F where
  unit := {
    app H := Functor.whiskerRight σ.unit H
    naturality {H H'} τ := by
      ext c
      dsimp only [id_obj, comp_obj, whiskeringLeft_obj_obj, Functor.id_map, NatTrans.comp_app,
        whiskerRight_app, Functor.comp_map, whiskeringLeft_obj_map, whiskerLeft_app]
      rw [τ.naturality]
  }
  counit := {
    app H := Functor.whiskerRight σ.counit H
    naturality {H H'} τ := by
      ext d
      dsimp only [comp_obj, whiskeringLeft_obj_obj, id_obj, Functor.comp_map,
        whiskeringLeft_obj_map, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
        Functor.id_map]
      rw [τ.naturality]
  }
  left_triangle_components H := by
    ext d
    dsimp only [whiskeringLeft_obj_obj, comp_obj, whiskeringLeft_obj_map, NatTrans.comp_app,
      whiskerLeft_app, whiskerRight_app, id_obj, Functor.comp_map, NatTrans.id_app]
    rw [<- H.map_comp, σ.right_triangle_components, H.map_id]
  right_triangle_components H := by
    ext c
    dsimp only [whiskeringLeft_obj_obj, comp_obj, whiskeringLeft_obj_map, NatTrans.comp_app,
      whiskerRight_app, id_obj, Functor.comp_map, whiskerLeft_app, NatTrans.id_app]
    rw [<- H.map_comp, σ.left_triangle_components, H.map_id]


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.8
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
随伴 F ⊣ G（F : C ⥤ D, G : D ⥤ C）と F′ ⊣ G′（F′ : C′ ⥤ D′, G′ : D′ ⥤ C′）、関手 H : C′ ⥤ C と
K : D′ ⥤ D が与えられたとき、自然変換 H ⋙ F ⟶ F′ ⋙ K 全体の集合と、自然変換
G′ ⋙ H ⟶ K ⋙ G 全体の集合の間に、2 つの随伴による転置で与えられる全単射がある。この全単射で
対応する 2 つの自然変換を、互いのメイトという。

H と K が恒等関手のとき、この全単射は、自然変換 F ⟶ F′ 全体の集合と、自然変換 G′ ⟶ G 全体の
集合の間の全単射になる。この全単射で対応する 2 つの自然変換を、互いの共役という。
-/

section

variable {C' : Type u₃} [Category.{v} C'] {D' : Type u₄} [Category.{v} D']

variable {F' : C' ⥤ D'} {G' : D' ⥤ C'} {H : C' ⥤ C} {K : D' ⥤ D}
variable (σ' : F' ⊣ G') (σ : F ⊣ G)

#check mateEquiv

-- メイトの全単射
def mate : (H ⋙ F ⟶ F' ⋙ K) ≃ (G' ⋙ H ⟶ K ⋙ G)  where
  toFun α :=
    G'.whiskerLeft (H.whiskerLeft σ.unit) ≫
    G'.whiskerLeft (Functor.whiskerRight α G) ≫
    Functor.whiskerRight (Functor.whiskerRight σ'.counit K) G
  invFun β :=
    Functor.whiskerRight (Functor.whiskerRight σ'.unit H ) F ≫
    Functor.whiskerRight (F'.whiskerLeft β) F ≫
    F'.whiskerLeft (K.whiskerLeft σ.counit)
  left_inv := by
    intro α; ext c'
    dsimp only [comp_obj, whiskerLeft_comp, NatTrans.comp_app, whiskerRight_app, id_obj,
      whiskerLeft_app]
    rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc]
    rw [σ.counit_naturality, σ.counit_naturality_assoc, σ.left_triangle_components_assoc]
    erw [α.naturality_assoc (σ'.unit.app c')]
    simp only [id_obj, comp_obj, Functor.comp_map]
    rw [<- K.map_comp, σ'.left_triangle_components]
    simp
  right_inv := by
    intro β; ext d'
    dsimp only [comp_obj, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, id_obj]
    rw [G.map_comp, G.map_comp, Category.assoc, Category.assoc]
    rw [σ.unit_naturality_assoc, σ.unit_naturality_assoc]
    rw [σ.right_triangle_components_assoc]
    erw [<-  β.naturality]; simp only [comp_obj, Functor.comp_map]
    rw [<- Category.assoc, <- H.map_comp, σ'.right_triangle_components]
    simp

end

#check conjugateEquiv

-- 共役の全単射
def conjugate {F' : C ⥤ D} {G' : D ⥤ C} (σ' : F' ⊣ G') (σ : F ⊣ G) :
    (F ⟶ F') ≃ (G' ⟶ G) := by
  exact mateEquiv σ' σ (G := Functor.id C ) (H := Functor.id D)



-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.3.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 三角等式を確かめて、命題4.3.3 の 2 つ目の証明を完成させよ。宣言は命題4.3.3 のセクションの
-- `compAdjunction` である。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.3.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 随伴の単位と余単位を使って、命題4.3.7 を証明せよ。宣言は命題4.3.7 のセクションの
-- `whiskerRightAdjunction` と `whiskerLeftAdjunction` である。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.3.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- hom 集合の間の自然な全単射を使って、命題4.3.7 の前半 (H ↦ H ⋙ F) ⊣ (H ↦ H ⋙ G) を
-- 証明せよ。宣言は命題4.3.7 のセクションの `whiskerRightAdjunction` である。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.3.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.1 の自然同型 θ を 1_G のメイトとして解釈し直す問題で、statement を書くことが解答に
-- なるので宣言を置かない。Mathlib の `Adjunction.leftAdjointUniq` は、この形で定義されている。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.3.v
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
左随伴の間の自然変換 α♯ : F ⇒ F′ が同型であることと、その共役 α♭ : G′ ⇒ G が同型であることは
同値である。

問題の後半（自然同型のメイトが同型とは限らない例を見つけよ）は、どの例を選ぶかが解答に
含まれるので宣言を置かない。
-/

#check conjugateEquiv_iso
#check conjugateEquiv_of_iso

#check conjugateEquiv_id
-- 恒等自然変換 1_F の共役は、恒等自然変換 1_G
theorem conjugateEquiv_id' (σ : F ⊣ G) : conjugateEquiv σ σ (𝟙 F) = 𝟙 G := by
  ext d
  rw [conjugateEquiv_apply_app, NatTrans.id_app, G.map_id]
  rw [Category.id_comp, σ.right_triangle_components, NatTrans.id_app]



#check conjugateEquiv_comp
-- 自然変換の合成 β ≫ α の共役は、α の共役と β の共役の合成
theorem conjugateEquiv_comp' {F' F'' : C ⥤ D} {G' G'' : D ⥤ C}
    (σ : F ⊣ G) (σ' : F' ⊣ G') (σ'' : F'' ⊣ G'') (α : F' ⟶ F) (β : F'' ⟶ F') :
    conjugateEquiv σ σ' α ≫ conjugateEquiv σ' σ'' β = conjugateEquiv σ σ'' (β ≫ α) := by
  ext d
  rw [NatTrans.comp_app, conjugateEquiv_apply_app, conjugateEquiv_apply_app, conjugateEquiv_apply_app]
  simp only [Category.assoc, NatTrans.comp_app, map_comp]
  slice_lhs 3 4 => rw [<- σ''.unit_naturality]
  rw [Category.assoc, Category.assoc]
  rw [<- σ''.unit_naturality_assoc, <- σ''.unit_naturality_assoc]
  rw [<- G''.map_comp, <- G''.map_comp, <- G''.map_comp, <- G''.map_comp]
  rw [<- G''.map_comp, <- G''.map_comp]
  congr 2
  rw [β.naturality_assoc, σ'.counit_naturality]
  slice_lhs 1 2 => rw [<- F''.map_comp]
  rw [β.naturality, F'.map_comp, Category.assoc, Category.assoc]
  slice_lhs 3 4 => rw [σ'.counit_naturality]
  slice_lhs 2 3 => rw [σ'.left_triangle_components]
  simp



-- α♯ の共役が同型 ⇔ α♯ が同型
theorem isIso_conjugateEquiv_iff {F' : C ⥤ D} {G' : D ⥤ C}
    (σ : F ⊣ G) (σ' : F' ⊣ G') (α : F ⟶ F') :
    IsIso (conjugateEquiv σ' σ α) ↔ IsIso α where
  mp H := by
    set f := (conjugateEquiv σ' σ) α
    let f' := inv f
    set τ := conjugateEquiv σ σ'
    use τ.symm (inv f)
    constructor
    · apply (conjugateEquiv σ σ).injective
      rw [<- conjugateEquiv_comp σ σ' σ] -- TODO
      simp only [τ]
      simp only [Equiv.apply_symm_apply, IsIso.inv_comp_eq]
      rw [conjugateEquiv_id] -- TODO
      simp [f]
    · apply (conjugateEquiv σ' σ').injective
      rw [<- conjugateEquiv_comp σ' σ σ']
      simp [τ, f]
  mpr H := by
    use (conjugateEquiv σ σ') (inv α)
    constructor
    · rw [conjugateEquiv_comp σ' σ σ', IsIso.inv_hom_id, conjugateEquiv_id]
    · rw [conjugateEquiv_comp σ σ' σ, IsIso.hom_inv_id, conjugateEquiv_id]





-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.3.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
メイトの対応は、(i) 関手の水平合成と四角形の水平な貼り合わせ、(ii) 随伴の垂直合成と四角形の
垂直な貼り合わせ、の 2 つと可換である。

Mathlib の補題で済むので宣言を置かない。(i) が `mateEquiv_vcomp`、(ii) が `mateEquiv_hcomp` で
ある。Mathlib は随伴を横に、関手 H と K を縦に描くので、名前の縦と横が本と逆になる。
-/

#check mateEquiv_vcomp
#check mateEquiv_hcomp

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.3.vii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 対象が圏、水平な射が関手、垂直な射が随伴、四角形がメイトの対である二重圏があることを示す
-- 問題。二重圏の定義（演習3.6.v）を宣言にしていないので、宣言を置かない。

end Riehl
