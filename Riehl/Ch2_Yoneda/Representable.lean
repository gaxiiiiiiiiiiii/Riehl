import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Equivalence

-- ═══════════════════════════════════════════════════════════════════════════
-- 概要
-- ═══════════════════════════════════════════════════════════════════════════
/-!
# 2.1 表現可能関手

普遍性を「その対象が表現する集合値関手」の語彙で述べる節。中心は定義2.1.4（表現・
表現可能関手）で、定義2.1.3 が始対象・終対象の特徴づけとしてその原型を与える。
2.2（米田の補題）・2.3（普遍要素）・2.4（要素圏）はすべてこの語彙の上で進む。

本の定義2.1.4 は表現を「対象 c と自然同型 C(c,−) ≅ F」の組で与える。Mathlib の
`Functor.RepresentableBy`・`CorepresentableBy` は同じデータを hom の全単射の族
`homEquiv` と合成との両立条件で持ち、自然同型の形との往復は `representableByEquiv`・
`corepresentableByEquiv` が与える。パッケージングが食い違うため、本の形を
`MyRepresentation` として自前で置く。ただしそれは定義2.1.4 の再現のみで、以降の
演習の statement は Mathlib の側で述べる。用語も食い違う: 本は共変・反変のどちらも
representable と呼ぶ（脚注4）が、Mathlib は共変側を corepresentable と呼び分ける。

本文中の例（例2.1.1・2.1.5・2.1.6）は載せない。

ファイル構成:
  前提パート: 定義1.3.11（hom 関手）・定数関手 Δ・定義1.6.14（始対象・終対象）・
    定義1.2.7（monomorphism）に対応する Mathlib の定義の写し
  本体:
    Part A: 定義2.1.3（始対象・終対象の表現による特徴づけ）
    Part B: 定義2.1.4（表現・表現可能性）と定義2.1.3 の言い換え
    Part C: 節末問題

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Yoneda.lean`（`yoneda`・`coyoneda`・`RepresentableBy`・
    `CorepresentableBy`・`IsRepresentable`・`IsCorepresentable`）
  - `Mathlib/CategoryTheory/Functor/Const.lean`（`Functor.const`）
  - `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean`（`IsInitial`・`IsTerminal`）
  - `Mathlib/CategoryTheory/Equivalence.lean`（`Functor.IsEquivalence`）
-/

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

-- ═══════════════════════════════════════════════════════════════════════════
-- 前提: 演習が使う Mathlib の定義
-- ═══════════════════════════════════════════════════════════════════════════

namespace Recap

variable {C : Type u₁} [Category.{v₁} C] (J : Type u₂) [Category.{v₂} J]

-- 定義1.3.11 の represented functor。Mathlib は反変側 C(−,c) を対象 c ごとに束ねて
-- 1つの関手 `yoneda` に持ち、共変側 C(c,−) は引数の入れ替え `flip` で得る
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj Y := unop Y ⟶ X
      map f := ↾fun g => f.unop ≫ g }
  map f := { app _ := ↾fun g => g ≫ f }

abbrev coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ := yoneda.flip

-- 定義2.1.3 の Δ*（定数関手）の一般形。対象 X を、すべての対象を X に、
-- すべての射を 𝟙 X に送る関手 J ⥤ C に送る
def const : C ⥤ J ⥤ C where
  obj X :=
    { obj := fun _ => X
      map := fun _ => 𝟙 X }
  map f := { app := fun _ => f }

-- 定義1.6.14 の始対象・終対象。「任意の対象への／からの射がただ一つ」を、Mathlib は
-- 空図式上の余錐／錐の普遍性（`IsColimit`・`IsLimit`）として実装する
abbrev IsInitial (X : C) := Limits.IsColimit (Limits.asEmptyCocone X)

abbrev IsTerminal (X : C) := Limits.IsLimit (Limits.asEmptyCone X)

-- 定義1.2.7(i) の monomorphism。f を後ろに合成した等式から f を消去できること
class Mono {X Y : C} (f : X ⟶ Y) : Prop where
  right_cancellation : ∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h

end Recap

-- ═══════════════════════════════════════════════════════════════════════════
-- 本体
-- ═══════════════════════════════════════════════════════════════════════════

-- ── Part A: 定義2.1.3（始対象・終対象の表現による特徴づけ） ─────────────────

-- 定義2.1.3(i) の順方向。始対象 c の hom 関手 C(c,−) が、すべてを1点集合に送る
--    定数関手 Δ* と自然同型になることを示す。Mathlib に対応物なし。
example (c : C) (h : Limits.IsInitial c) :
    coyoneda.obj (op c) ≅ (Functor.const C).obj PUnit.{v₁ + 1} where
  hom := {
    app c' := by
      apply TypeCat.ofHom
      intro _
      exact PUnit.unit
    naturality X Y f := by
      ext h; simp
  }
  inv := {
    app c' := by
      apply TypeCat.ofHom
      intro _
      exact h.to c'
    naturality X Y f := by
      ext h; simp
  }
  hom_inv_id := by
    ext c' (f : c ⟶ c')
    apply h.hom_ext
  inv_hom_id := by
    ext c' h
    apply PUnit.ext


-- 定義2.1.3(i) の逆方向。C(c,−) ≅ Δ* から c が始対象であることを示す。
--    Mathlib に対応物なし。
example (c : C) (e : coyoneda.obj (op c) ≅ (Functor.const C).obj PUnit.{v₁ + 1}) :
    Limits.IsInitial c := by
  apply Limits.IsInitial.ofUniqueHom (fun c' => (e.app c').inv PUnit.unit)
  intro c' (m : c ⟶ c')
  rw [<- (e.app c').hom_inv_id_apply m]
  congr


-- 定義2.1.3(ii) の順方向。終対象 c の hom 関手 C(−,c) が定数関手 Δ* : Cᵒᵖ ⥤ Set と
--    自然同型になることを示す。Mathlib に対応物なし。
example (c : C) (h : Limits.IsTerminal c) :
    yoneda.obj c ≅ (Functor.const Cᵒᵖ).obj PUnit.{v₁ + 1} where
  hom := {
    app c' := by
      apply TypeCat.ofHom
      intro _; exact PUnit.unit
    naturality X Y f := by ext; simp
  }
  inv := {
    app c' := by
      apply TypeCat.ofHom
      intro _; exact h.from (unop c')
    naturality X Y f:= by ext x; simp
  }
  hom_inv_id := by
    ext c' f; apply h.hom_ext
  inv_hom_id := by
    ext c' f; apply PUnit.ext





-- 定義2.1.3(ii) の逆方向。C(−,c) ≅ Δ* から c が終対象であることを示す。
--    Mathlib に対応物なし。
example (c : C) (e : yoneda.obj c ≅ (Functor.const Cᵒᵖ).obj PUnit.{v₁ + 1}) :
    Limits.IsTerminal c := by
  apply Limits.IsTerminal.ofUniqueHom (fun c' => (e.app (op c')).inv PUnit.unit)
  intro c' (m : c' ⟶ c)
  rw [<- (e.app (op c')).hom_inv_id_apply m]
  congr

-- ── Part B: 定義2.1.4（表現・表現可能性）と定義2.1.3 の言い換え ─────────────

-- 定義2.1.4(i) の共変の場合。本の定義そのままで、表現は対象と自然同型 C(c,−) ≅ F の組。
-- F の値を hom と同じ `Type v₁` に取ることが、本が C に課す locally small の仮定にあたる。
#check @CategoryTheory.Functor.CorepresentableBy
#check @CategoryTheory.Functor.corepresentableByEquiv

structure MyRepresentation (F : C ⥤ Type v₁) where
  repObj : C
  repIso : coyoneda.obj (op repObj) ≅ F

-- 定義2.1.4(i) の反変の場合。本はどちらの変性も representation と呼ぶ（脚注4）が、
-- Mathlib は反変（前層）側を `RepresentableBy`、共変側を `CorepresentableBy` と呼ぶ。
#check @CategoryTheory.Functor.RepresentableBy
#check @CategoryTheory.Functor.representableByEquiv

structure MyContraRepresentation (F : Cᵒᵖ ⥤ Type v₁) where
  repObj : C
  repIso : yoneda.obj repObj ≅ F

-- 定義2.1.4(ii) の共変の場合。表現のデータが存在すること
#check @CategoryTheory.Functor.IsCorepresentable

def MyRepresentable (F : C ⥤ Type v₁) : Prop :=
  Nonempty (MyRepresentation F)

-- 定義2.1.4(ii) の反変の場合
#check @CategoryTheory.Functor.IsRepresentable

def MyContraRepresentable (F : Cᵒᵖ ⥤ Type v₁) : Prop :=
  Nonempty (MyContraRepresentation F)

-- 定義2.1.3 直後の本文の言い換え（番号なし）。始対象の存在と定数関手 Δ* の表現可能性が
--    同値であることを示す。表現可能性は Mathlib の `IsCorepresentable` で述べる
--    （`MyRepresentable` は定義の再現のみで、以降の statement には使わない）。
--    Mathlib に対応物なし。
example : (∃ c : C, Nonempty (Limits.IsInitial c)) ↔
    ((Functor.const C).obj PUnit.{v₁ + 1}).IsCorepresentable := sorry

-- 双対。終対象の存在と Δ* : Cᵒᵖ ⥤ Set の表現可能性が同値であることを示す。
--    Mathlib に対応物なし。
example : (∃ c : C, Nonempty (Limits.IsTerminal c)) ↔
    ((Functor.const Cᵒᵖ).obj PUnit.{v₁ + 1}).IsRepresentable := sorry

-- ── Part C: 節末問題 ────────────────────────────────────────────────────────

-- 演習2.1.i は statement を置かない。(i) は「Z/n が表現する関手を記述せよ」で、関手を
--    statement に書くこと自体が答えになる。(ii) は具体圏 Group での準同型 Z/n → Z/m の
--    決定で、具体圏の演習は扱うなら独立したファイルに分ける（演習1.5.ix と同じ方針）。

-- 演習2.1.ii。表現可能な集合値関手が monomorphism を単射に送ることを示す。
--    後半（この対偶で、表現可能でない集合値関手の例を見つける）は反例構成なので
--    statement は置かない。Mathlib に対応物なし。
example {F : C ⥤ Type v₁} [F.IsCorepresentable] {x y : C} (f : x ⟶ y) [Hf : Mono f] :
    Function.Injective (F.map f) := by
  intro a b E
  change (F.map f).hom' a = (F.map f).hom' b at E
  let σ := Functor.coreprW F
  have Ha := σ.inv.naturality_apply f a
  simp only [ConcreteCategory.hom ] at Ha
  rw [E] at Ha; simp only [Functor.flip_obj_obj, yoneda_obj_obj, Functor.flip_obj_map,
    yoneda_map_app] at Ha
  conv at Ha => arg 2; change _ ≫ _
  have Hb := σ.inv.naturality_apply f b
  simp only [ConcreteCategory.hom ] at Hb
  simp only [Functor.flip_obj_obj, yoneda_obj_obj, Functor.flip_obj_map, yoneda_map_app] at Hb
  conv at Hb => arg 2; change _ ≫ _
  have Hab := Ha.symm.trans Hb
  have := Hf.right_cancellation _ _ Hab
  rw [<- (σ.app x).inv_hom_id_apply a, <- (σ.app x).inv_hom_id_apply b]
  simp only [ConcreteCategory.hom]
  congr 1


-- 演習2.1.iii。同値 H : C ≃ D と自然同型 GH ≅ F を通じて表現可能性が移ることを示す。
--    問題は (i)(ii) とも可否を問う形だが、答えはどちらも肯定なので、表現の存在が移る
--    形に言い換えた。仮定側は表現のデータ `CorepresentableBy` で受け、結論側は表現対象の
--    特定が答えの一部になるため存在 `IsCorepresentable` で述べる。自然同型 H ⋙ G ≅ F が
--    型を持つように、D の hom は C と同じ universe に取る。Mathlib に対応物なし。

-- 演習2.1.iii(i)。G の表現から F の表現を作る。
example {D : Type u₂} [Category.{v₁} D] {F : C ⥤ Type v₁} {G : D ⥤ Type v₁}
    (H : C ⥤ D) [H.IsEquivalence] (e : H ⋙ G ≅ F) {d : D} (r : G.CorepresentableBy d) :
    F.IsCorepresentable where
  has_corepresentation := by
    obtain ⟨c, ⟨σ⟩⟩ :=  Functor.EssSurj.mem_essImage H d
    use c; constructor
    refine {
      homEquiv {c'} := {
        toFun f := ((H ⋙ G).map f ≫ (e.app c').hom) (r.homEquiv.toFun (σ.inv))
        invFun Fc' := H.preimage (σ.hom ≫ r.homEquiv.symm ((e.app c').inv Fc'))
        left_inv := by
          intro f
          simp only [Functor.comp_obj, Iso.app_inv, Functor.comp_map, Iso.app_hom,
            Equiv.toFun_as_coe, comp_apply]
          simp only [ConcreteCategory.hom]
          apply H.map_injective
          rw [H.map_preimage]
          conv => arg 1; arg 2; arg 2; change  ((G.map (H.map f)) ≫ (e.hom.app c') ≫ (e.inv.app c')).hom' (r.homEquiv σ.inv)
          simp only [Functor.comp_obj, Iso.hom_inv_id_app, Category.comp_id]
          have := r.homEquiv_comp (H.map f) σ.inv
          simp only [ConcreteCategory.hom] at this
          rw [<- this]
          simp only [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
        right_inv := by
          intro Fc'
          simp only [Functor.comp_obj, Iso.app_inv, Functor.comp_map, Functor.map_preimage,
            Functor.map_comp, Iso.app_hom, Category.assoc, comp_apply, Equiv.toFun_as_coe]
          simp only [ConcreteCategory.hom]
          conv => arg 1; arg 2; change  ((G.map σ.hom) ≫ (G.map (r.homEquiv.symm ((e.inv.app c').hom' Fc')))).hom' (r.homEquiv σ.inv)
          rw [<- G.map_comp]
          have := r.homEquiv_comp (σ.hom ≫ r.homEquiv.symm ((e.inv.app c').hom' Fc')) σ.inv
          simp only [ConcreteCategory.hom] at this
          rw [<- this]
          simp only [Functor.comp_obj, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
          change ((e.inv.app c') ≫ (e.hom.app c')).hom Fc' = Fc'
          simp
      }
      homEquiv_comp {x y} g f := by
        simp only [Functor.comp_obj, Functor.comp_map, Iso.app_hom, ConcreteCategory.hom,
          Equiv.toFun_as_coe, Iso.app_inv, Equiv.coe_fn_mk, Functor.map_comp, Category.assoc]
        rw [<- Category.assoc, <- G.map_comp, <- H.map_comp]
        rw [<- CategoryTheory.Functor.comp_map, e.hom.naturality (f ≫ g)]
        rw [<- CategoryTheory.Functor.comp_map, e.hom.naturality f]
        change _ =  (((e.hom.app c ≫ F.map f)) ≫ F.map g).hom' _
        simp
    }



-- 演習2.1.iii(ii) の証明中に必要と判明した補題。表現 r の普遍要素 r.homEquiv (𝟙 c) を
--    e.inv で G 側へ移した要素が、H.map g による押し出しのもとで r.homEquiv g と対応する
--    こと。H が同値であることは使わない。Mathlib に対応物なし。
lemma inv_app_homEquiv_eq {D : Type u₂} [Category.{v₁} D] {F : C ⥤ Type v₁} {G : D ⥤ Type v₁}
    (H : C ⥤ D) (e : H ⋙ G ≅ F) {c c' : C} (r : F.CorepresentableBy c) (g : c ⟶ c') :
    (G.map (H.map g)) ((e.inv.app c) (r.homEquiv (𝟙 c))) = (e.inv.app c') (r.homEquiv g) := by
  rw [<- comp_apply, <- Functor.comp_map]
  rw [<- e.inv.naturality g]
  rw [comp_apply]; congr 1
  rw [<- r.homEquiv_comp g (𝟙 c)]
  simp


-- 演習2.1.iii(ii)。F の表現から G の表現を作る。
example {D : Type u₂} [Category.{v₁} D] {F : C ⥤ Type v₁} {G : D ⥤ Type v₁}
    (H : C ⥤ D) [H.IsEquivalence] (e : H ⋙ G ≅ F) {c : C} (r : F.CorepresentableBy c) :
    G.IsCorepresentable where
  has_corepresentation := by
    use H.obj c; constructor
    refine {
      homEquiv {d} := by
        obtain Hd :=  Functor.EssSurj.mem_essImage H d
        let σ := Hd.choose_spec.some
        set c' := Hd.choose
        refine {
          toFun f := ((e.app c).inv ≫ G.map f).hom (r.homEquiv.toFun (𝟙 c))
          invFun Gd := H.map (r.homEquiv.invFun ((e.app c').hom (G.map σ.inv Gd))) ≫ σ.hom
          left_inv := by
            intro f
            simp only [Functor.comp_obj, Iso.app_hom, Iso.app_inv, Equiv.toFun_as_coe,
              comp_apply, Equiv.invFun_as_coe]
            rw [← comp_apply, ← comp_apply,<- comp_apply]
            have E := inv_app_homEquiv_eq H e r (H.preimage (f ≫ σ.inv))
            rw [H.map_preimage, <- comp_apply, G.map_comp] at E
            rw [<- Category.assoc, <- Category.assoc, comp_apply, Category.assoc]
            rw [E, <- comp_apply, e.inv_hom_id_app]
            simp
          right_inv := by
            intro Gd
            simp only [Functor.comp_obj, Iso.app_inv, Iso.app_hom, Equiv.invFun_as_coe,
              Functor.map_comp, comp_apply, Equiv.toFun_as_coe]
            rw [← comp_apply, ← comp_apply,<- comp_apply]
            rw [<- Category.assoc, comp_apply, comp_apply]
            rw [inv_app_homEquiv_eq H e r]
            simp only [Functor.comp_obj, comp_apply, Equiv.apply_symm_apply,
              Iso.hom_inv_id_app_apply]
            rw [<- comp_apply, <- G.map_comp, σ.inv_hom_id, G.map_id]
            simp

        }

    }


-- 演習2.1.iv は statement を置かない。問題は「成分がすべて monomorphism の自然変換
--    α : F ⇒ G があるとき F を G の subfunctor と呼ぶ。C(−,c) の subfunctor をなす
--    部分集合族 Fx ⊂ C(x,c) を特徴づけよ」というもので、特徴づけの主張の形自体が
--    答えの一部になる（演習1.5.vii と同じ理由）。
