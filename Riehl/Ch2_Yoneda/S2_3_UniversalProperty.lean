import Mathlib.CategoryTheory.Yoneda
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# 2.3 普遍性と普遍要素

節の数学的な内容は同名の HTML にある。このファイルは本の主張を出現順に並べたもので、主張と
定理群の構成は各セクションの冒頭に、形式化の判断は下の表に、Mathlib の対応物は各
statement の直前の `#check` にある。

形式化の判断:
  Set 値関手   hom 集合と同じ universe に値を取る関手として書く。本が圏に課す locally
               small の仮定が、この universe の一致にあたる
  命題2.3.1 の 系2.2.8（米田埋め込みの充満忠実性）と演習1.5.iv から命題2.3.1 を出す道を、
  別解       別解として置く。1.5.iv は同型の反映（`isIso_of_fully_faithful`）と創出
               （`Functor.preimageIso`）を片道2本で扱っており、それを一つの全単射に束ねた
               ものが `myIsoEquivOfFullyFaithful`。往復が互いに逆であることは 1.5 では
               示していないので、そこがこの演習の中身になる。続く `*_alt` の2本は
               この道具から命題2.3.1 を出すもので、別解が別解として閉じるようにここだけ
               自前定義を参照する（共変側は `Cᵒᵖ` へ移す `isoOpEquiv` を挟む）
  命題2.3.1    本は「3つのデータが等価」と述べるので、`Iso` の型どうしの `Equiv` として
               述べ、反変側と共変側の2本に割る。Mathlib の対応物は充満忠実関手一般に
               ついての `Functor.FullyFaithful.isoEquiv` で、米田埋め込みに特殊化した
               宣言は持たない
  系2.3.2      表現の2つの持ち方を往復させる `myRepresentableByEquiv`、同型の存在、表現と
               両立する射の一意性に割る。1本目は、本が表現を「対象と自然同型 よ Y ≅ F の
               組」で持つのに対し Mathlib が hom の全単射の族で持つ、その差を渡す宣言。
               2.1 以降の演習が Mathlib の形で述べられていることの根拠にあたる。
               一意性は同型に限らず射で述べる（本の主張より強く、証明は同じ）。Mathlib は
               存在側の `RepresentableBy.uniqueUpToIso` だけを持ち、一意性に対応物なし
  定義2.3.3    本は普遍要素を「対象 c と要素 x ∈ Fc の組で、Ψ(x) が自然同型になるもの」
               として定義する。Mathlib は表現を hom の全単射の族で持ち、要素はそこから
               `Functor.reprx` で取り出す派生物なので、持ち方が食い違う。本の形を
               `MyUniversalElement` として自前で置く。構造は本の定義の写しなので
               フィールドまで書いて渡し、演習になるのはそれを使う主張のほう
  普遍要素から `def_2_3_3_isRepresentable` は `MyUniversalElement` を参照する。この
  の表現       パッケージングに対応する Mathlib の宣言がないため
  命題2.3.10   本はテンソル積を Bilin(V,W;−) の表現として定義し、この命題を表現対象の
  演習2.3.ii   一意性（系2.3.2）から導く。Mathlib の `TensorProduct` は商による構成で
               定義され、普遍性は `TensorProduct.lift` として定理の側にある。証明の筋
               （普遍性で分解する）は移るが、出発点が逆になる。Bilin を関手として組む
               ところからは範囲外なので、statement は Mathlib の `TensorProduct` で述べる

statement を置かない節末問題:
  2.3.i    表現の普遍要素を記述する問題で、要素の形自体が答えになる
  2.3.iii  評価写像 ev を定義する問題。ev は表現のデータそのものなので、表現可能性を
           statement に書くと ev の構成が答えとして出てしまう
  2.3.iv   本文とは別の普遍要素を見つける問題で、2.3.i と同じ理由

本文中の例（例2.3.4・2.3.6・2.3.7・2.3.8・2.3.13）と注意2.3.12 は載せない。注意2.3.12 は
命題2.3.10 の同型を明示的に取り出す計算で、対応する Mathlib の宣言は `TensorProduct.comm`
の `simps` 補題（`TensorProduct.comm_tmul`）。

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Yoneda.lean`（`yoneda`・`coyoneda`・`yonedaEquiv`・
    `RepresentableBy`・`IsRepresentable`・`representableByEquiv`・
    `RepresentableBy.uniqueUpToIso`）
  - `Mathlib/CategoryTheory/Functor/FullyFaithful.lean`（`Functor.FullyFaithful.isoEquiv`）
  - `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`（`TensorProduct`・`TensorProduct.lift`）
  - `Mathlib/LinearAlgebra/TensorProduct/Associator.lean`（`TensorProduct.lid`・
    `TensorProduct.assoc`）
-/

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

variable {C : Type u₁} [Category.{v₁} C]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  前提: 演習が使う Mathlib の定義
-- ╚═════════════════════════════════════════════════════════════════════════

namespace Recap

variable {C : Type u₁} [Category.{v₁} C]

-- 定義1.3.11 の hom 関手 C(−,X)。Mathlib は対象ごとの関手を1つに束ねて持つ
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj Y := unop Y ⟶ X
      map f := ↾fun g ↦ f.unop ≫ g }
  map f := { app _ := ↾fun g ↦ g ≫ f }

-- そのうち c ↦ C(c,−) の側。Mathlib は独立に定義せず引数の入れ替えで得る
abbrev coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ := yoneda.flip

-- 定義2.1.4 の表現。Mathlib は自然同型ではなく hom の全単射の族と合成との両立で持つ
structure RepresentableBy (F : Cᵒᵖ ⥤ Type v₁) (Y : C) where
  homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X)
  homEquiv_comp {X X' : C} (g : X ⟶ X') (f : X' ⟶ Y) :
    homEquiv (g ≫ f) = F.map g.op (homEquiv f)

-- 定義2.1.4(ii) の表現可能性。表現のデータが存在すること
class IsRepresentable (F : Cᵒᵖ ⥤ Type v₁) : Prop where
  has_representation : ∃ Y : C, Nonempty (RepresentableBy F Y)

end Recap

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題2.3.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
局所小な圏の対象 x, y について、C における同型 x ≅ y、前層の圏における同型
C(−,x) ≅ C(−,y)、共変側の圏における同型 C(y,−) ≅ C(x,−) の3つのデータは等価である。

構成: 反変側との等価性と共変側との等価性を、それぞれ型どうしの全単射として述べる。
-/

#check @CategoryTheory.Functor.FullyFaithful.isoEquiv

def prop_2_3_1_contra (x y : C) : (x ≅ y) ≃ (yoneda.obj x ≅ yoneda.obj y) where
  toFun σ := {
    hom := yoneda.map σ.hom
    inv := yoneda.map σ.inv
    hom_inv_id := by
      rw [<- yoneda.map_comp, σ.hom_inv_id]; simp
    inv_hom_id := by
      rw [<- yoneda.map_comp, σ.inv_hom_id]; simp
  }
  invFun σ := {
    hom := (σ.app (op x) ).hom (𝟙 x)
    inv := (σ.app (op y)).inv (𝟙 y)
    hom_inv_id := by
      have Hx :=  (σ.app (op x)).hom_inv_id_apply (𝟙 x)
      set f : x ⟶ y := (ConcreteCategory.hom (σ.app (op x)).hom) (𝟙 x)
      set g : y ⟶ x := (ConcreteCategory.hom (σ.app (op y)).inv) (𝟙 y)
      have Hf := σ.inv.naturality_apply f.op (𝟙 y)
      simp only [yoneda_obj_obj, yoneda_obj_map, Quiver.Hom.unop_op, TypeCat.hom_ofHom,
        TypeCat.Fun.coe_mk, Category.comp_id] at Hf
      rw [Hx.symm.trans Hf]
      rfl


    inv_hom_id := by
      have Hy := (σ.app (op y)).inv_hom_id_apply (𝟙 y)
      set f := (ConcreteCategory.hom (σ.app (op x)).hom) (𝟙 x)
      set g := (ConcreteCategory.hom (σ.app (op y)).inv) (𝟙 y)
      have E := σ.hom.naturality_apply g.op (𝟙 x)
      simp only [yoneda_obj_obj, yoneda_obj_map, Quiver.Hom.unop_op, TypeCat.hom_ofHom,
        TypeCat.Fun.coe_mk, Category.comp_id] at E
      rw [<- Hy]; simp only [yoneda_obj_obj, Iso.app_hom]
      rw [E]; rfl

  }
  right_inv := by
    intro σ; ext c (f : unop c ⟶ x)
    simp only [yoneda_obj_obj, Iso.app_hom, yoneda_map_app, TypeCat.hom_ofHom,
      TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk]
    have E := σ.hom.naturality_apply f.op (𝟙 x)
    simp only [op_unop, yoneda_obj_obj, yoneda_obj_map, Quiver.Hom.unop_op, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk, Category.comp_id] at E
    rw [E]
  left_inv := by
    intro σ; simp






#check @CategoryTheory.Functor.FullyFaithful.isoEquiv

def prop_2_3_1_cov (x y : C) :
    (x ≅ y) ≃ (coyoneda.obj (op y) ≅ coyoneda.obj (op x)) where
  toFun σ := {
    hom := coyoneda.map σ.hom.op
    inv := coyoneda.map σ.inv.op
    hom_inv_id := by
      ext c (f : y ⟶ c)
      rw [<- coyoneda.map_comp, <- op_comp, σ.inv_hom_id, op_id, coyoneda.map_id]
    inv_hom_id := by
      ext c (f : x ⟶ c)
      rw [<- coyoneda.map_comp, <- op_comp, σ.hom_inv_id, op_id, coyoneda.map_id]
  }
  invFun σ := {
    hom := (σ.app y).hom (𝟙 y)
    inv := (σ.app x).inv (𝟙 x)
    hom_inv_id := by
      have Hx := (σ.app x).inv_hom_id_apply (𝟙 x)
      set f := (ConcreteCategory.hom (σ.app y).hom) (𝟙 y)
      set g := (ConcreteCategory.hom (σ.app x).inv) (𝟙 x)
      have Hf := σ.hom.naturality_apply g (𝟙 y)
      simp only [Functor.flip_obj_obj, yoneda_obj_obj, Functor.flip_obj_map, yoneda_map_app,
        TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Category.id_comp] at Hf
      rw [Hx.symm.trans Hf]
      rfl
    inv_hom_id := by
      have Hy := (σ.app y).hom_inv_id_apply (𝟙 y)
      set f := (ConcreteCategory.hom (σ.app y).hom) (𝟙 y)
      set g := (ConcreteCategory.hom (σ.app x).inv) (𝟙 x)
      have Hg := σ.inv.naturality_apply f (𝟙 x)
      simp only [Functor.flip_obj_obj, yoneda_obj_obj, Functor.flip_obj_map, yoneda_map_app,
        TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Category.id_comp] at Hg
      rw [Hy.symm.trans Hg]; rfl
  }
  left_inv σ := by simp
  right_inv σ := by
    ext c (f : y ⟶ c); simp only [Functor.flip_obj_obj, yoneda_obj_obj, Iso.app_hom,
      Functor.flip_map_app, yoneda_obj_map, Quiver.Hom.unop_op, TypeCat.hom_ofHom,
      TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk]
    have := σ.hom.naturality_apply f (𝟙 y)
    simp only [Functor.flip_obj_obj, yoneda_obj_obj, Functor.flip_obj_map, yoneda_map_app,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Category.id_comp] at this
    rw [this]




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題2.3.1 の別解
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
充満忠実な関手のもとで、対象の間の同型と像の間の同型は1対1に対応する。米田埋め込みが
充満忠実（系2.2.8）であることと合わせると、命題2.3.1 はこの系として出る。

構成: 充満忠実な関手についての全単射を構成し、それを米田埋め込みの両側に適用する。
-/

#check @CategoryTheory.Functor.FullyFaithful.isoEquiv

noncomputable def myIsoEquivOfFullyFaithful {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [F.Full] [F.Faithful] (x y : C) : (x ≅ y) ≃ (F.obj x ≅ F.obj y) where
  toFun σ := {
    hom := F.map σ.hom
    inv := F.map σ.inv
    hom_inv_id := by
      rw [<- F.map_comp, σ.hom_inv_id, F.map_id]
    inv_hom_id := by
      rw [<- F.map_comp, σ.inv_hom_id, F.map_id]
  }
  invFun σ := {
    hom := F.preimage σ.hom
    inv := F.preimage σ.inv
    hom_inv_id := by
      apply F.map_injective
      rw [F.map_comp, F.map_preimage, F.map_preimage]
      rw [σ.hom_inv_id, F.map_id]
    inv_hom_id := by
      apply F.map_injective
      rw [F.map_comp, F.map_preimage, F.map_preimage]
      rw [σ.inv_hom_id, F.map_id]
  }
  left_inv := by
    intro σ; dsimp
    ext; dsimp
    rw [F.preimage_map]
  right_inv := by
    intro σ; dsimp; ext; dsimp
    rw [F.map_preimage]





#check @CategoryTheory.Yoneda.fullyFaithful

def prop_2_3_1_contra_alt (x y : C) : (x ≅ y) ≃ (yoneda.obj x ≅ yoneda.obj y) := by
  apply Functor.FullyFaithful.isoEquiv
  exact Yoneda.fullyFaithful

#check @CategoryTheory.Coyoneda.fullyFaithful

def prop_2_3_1_cov_alt (x y : C) :
    (x ≅ y) ≃ (coyoneda.obj (op y) ≅ coyoneda.obj (op x)) := by
  apply Equiv.trans _ (Functor.FullyFaithful.isoEquiv Coyoneda.fullyFaithful)
  exact (isoOpEquiv (op y) (op x)).symm




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系2.3.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
同じ関手を表現する2つの対象は同型であり、しかも2つの表現と両立する同型はただ一つである。

構成: 本の形の表現（自然同型 よ Y ≅ F）と Mathlib の形の表現を往復させ、表現対象の間の
      同型を構成して、表現と両立する射が高々一つであることを示す。
-/

#check @CategoryTheory.Functor.representableByEquiv

def myRepresentableByEquiv {F : Cᵒᵖ ⥤ Type v₁} {Y : C} :
    F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F) where
  toFun σ := {
    hom := {
      app X := by
        apply TypeCat.ofHom
        intro (f : X.unop ⟶ Y)
        exact σ.homEquiv.toFun f
      naturality {A B} g := by
        ext (f :  unop A ⟶ Y)
        simp only [yoneda_obj_obj, yoneda_obj_map, op_unop, Equiv.toFun_as_coe,
          TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
        exact σ.homEquiv_comp g.unop f
    }
    inv := {
      app X := by
        apply TypeCat.ofHom
        intro FX
        change unop X ⟶ Y
        exact σ.homEquiv.invFun FX
      naturality {A B} f := by
        ext FA
        simp only [yoneda_obj_obj, op_unop, Equiv.invFun_as_coe, id_eq, TypeCat.Fun.toFun_apply,
          comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, yoneda_obj_map]
        have E := σ.homEquiv_comp f.unop (σ.homEquiv.symm FA)
        simp at E
        rw [<- E]; simp
    }
    hom_inv_id := by ext; simp
    inv_hom_id := by ext; simp
  }
  invFun σ := {
    homEquiv {X} := {
      toFun f := σ.hom.app (op X) f
      invFun FX := σ.inv.app (op X) FX
      left_inv := by
        intro f; dsimp only [yoneda_obj_obj]
        rw [<- comp_apply, σ.hom_inv_id_app]
        simp
      right_inv := by
        intro FX; dsimp only [yoneda_obj_obj]
        rw [<- comp_apply, σ.inv_hom_id_app]
        simp
    }
  }
  left_inv := by intro σ; ext; simp
  right_inv := by intro σ; ext; simp



#check @CategoryTheory.Functor.RepresentableBy.uniqueUpToIso

def cor_2_3_2_iso {F : Cᵒᵖ ⥤ Type v₁} {Y Y' : C}
    (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') : Y ≅ Y' := by
  have σ := (e.toIso.trans e'.toIso.symm)
  exact (Functor.FullyFaithful.isoEquiv (Yoneda.fullyFaithful)).symm σ




theorem cor_2_3_2_unique {F : Cᵒᵖ ⥤ Type v₁} {Y Y' : C}
    (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') (f f' : Y ⟶ Y')
    (Hf : ∀ {Z : C} (g : Z ⟶ Y), e'.homEquiv (g ≫ f) = e.homEquiv g)
    (Hf' : ∀ {Z : C} (g : Z ⟶ Y), e'.homEquiv (g ≫ f') = e.homEquiv g) :
    f = f' := by
  have Ef := Hf (𝟙 Y)
  have Ef' := Hf' (𝟙 Y)
  rw [Category.id_comp] at Ef Ef'
  apply e'.homEquiv.injective
  rw [Ef, Ef']




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義2.3.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
関手 F の要素とは対象 c と要素 x ∈ Fc の組であり、米田の補題が定める自然変換 Ψ(x) が
自然同型であるとき普遍要素という。このとき c は F を表現する。

構成: 普遍要素を定義し、そこから表現可能性が従うことを示す。
-/

-- Recap: `Functor.reprX`・`reprx`・`reprW` の実装確認
--   表現 σ : Hom(−,c) ≅ F に対し、reprx := σ_c(𝟙 c) : Fc を普遍要素とする
--   Mathlib は c を選択で取り（reprX F）、σ を homEquiv の族で持つ（representableBy F）
namespace Recap

-- 表現対象 c
noncomputable def reprX (F : Cᵒᵖ ⥤ Type v₁) [hF : F.IsRepresentable] : C :=
  hF.has_representation.choose

-- 普遍要素 σ_c(𝟙 c)
noncomputable def reprx (F : Cᵒᵖ ⥤ Type v₁) [hF : F.IsRepresentable] :
    F.obj (op F.reprX) :=
  F.representableBy.homEquiv (𝟙 F.reprX)

-- 表現 (σ : Hom(-, c) ≅ F) そのもの
noncomputable def reprW (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable] :
    yoneda.obj F.reprX ≅ F :=
  F.representableBy.toIso

end Recap

#check @CategoryTheory.Functor.reprX
#check @CategoryTheory.Functor.reprx
#check @CategoryTheory.Functor.reprW
#check yonedaEquiv

structure MyUniversalElement (F : Cᵒᵖ ⥤ Type v₁) where
  obj : C
  elt : F.obj (op obj)
  isIso : IsIso (yonedaEquiv.symm elt : yoneda.obj obj ⟶ F)

#check @CategoryTheory.Functor.IsRepresentable

theorem def_2_3_3_isRepresentable {F : Cᵒᵖ ⥤ Type v₁} (u : MyUniversalElement F) :
    F.IsRepresentable where
  has_representation := by
    use u.obj; constructor
    refine {
      homEquiv {c} :=
        ((@asIso _ _ _ _ (yonedaEquiv.symm u.elt) u.isIso).app (op c)).toEquiv
      homEquiv_comp {X Y} f g := by
        simp only [asIso, Iso.toEquiv_fun];
        dsimp only [Iso.app_hom, yonedaEquiv_symm_app, yoneda_obj_obj, TypeCat.hom_ofHom,
          TypeCat.Fun.coe_mk, op_comp]
        rw [<- comp_apply, F.map_comp]
    }



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題2.3.10
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 任意の k-ベクトル空間 V, W に対しテンソル積は可換である。

#check @TensorProduct.comm

noncomputable def prop_2_3_10 (R : Type u) [CommSemiring R] (M N : Type u)
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] :
    TensorProduct R M N ≃ₗ[R] TensorProduct R N M := sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.3.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
テンソル積の定義的普遍性から、係数体との積が恒等であることと、結合律を示す。

構成: 単位律と結合律をそれぞれ線型同型として述べる。
-/

#check @TensorProduct.lid

noncomputable def ex_2_3_ii_lid (R : Type u) [CommSemiring R] (M : Type u)
    [AddCommMonoid M] [Module R M] : TensorProduct R R M ≃ₗ[R] M := sorry

#check @TensorProduct.assoc

noncomputable def ex_2_3_ii_assoc (R : Type u) [CommSemiring R] (M N P : Type u)
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] :
    TensorProduct R (TensorProduct R M N) P
      ≃ₗ[R] TensorProduct R M (TensorProduct R N P) := sorry
