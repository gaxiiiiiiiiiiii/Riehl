import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Data.Matrix.Basic

-- ═══════════════════════════════════════════════════════════════════════════
-- 概要
-- ═══════════════════════════════════════════════════════════════════════════
/-!
# 2.2 米田の補題

表現された関手 C(c,−) からの自然変換が、表現対象での要素 α_c(id_c) と一対一に対応する節。
中心は定理2.2.4（米田の補題）と系2.2.8（米田埋め込みの充満忠実性）で、2.3 の表現の一意性、
2.4 の要素の圏、3章の極限の表現可能性による定義、4.2 の随伴の一意性の基盤になる。

読解ガイドと形式化方針の記録は同ディレクトリの companion（`Yoneda.html`）にある。

ファイル構成:
  Recap: `yoneda`・`coyoneda`・`MulActionHom`・`Preorder.smallCategory` の写し
  本体:
    Part A: ウォームアップ（命題2.2.3）
    Part B: 定理2.2.4（米田の補題、共変版）
    Part C: 演習2.2.i（双対米田、反変版）
    Part D: 系2.2.8（米田埋め込み）と演習2.2.iii
    Part E: 応用（系2.2.10・系2.2.11）
    Part F: Lean で述べにくい節末問題

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Yoneda.lean`（`yoneda`・`coyoneda`・`yonedaEquiv`・`coyonedaEquiv`）
  - `Mathlib/CategoryTheory/Category/Preorder.lean`（`Preorder.smallCategory`）
  - `Mathlib/GroupTheory/GroupAction/Hom.lean`（`MulActionHom`）
  - `Mathlib/GroupTheory/Perm/Subgroup.lean`（`Equiv.Perm.subgroupOfMulAction`）
  - `Mathlib/Data/Matrix/Basic.lean`（`Matrix` とその積）
-/

open CategoryTheory Opposite

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

-- ═══════════════════════════════════════════════════════════════════════════
-- 前提: 演習が使う Mathlib の定義
-- ═══════════════════════════════════════════════════════════════════════════

namespace Recap

variable {C : Type u₁} [Category.{v₁} C]

-- 系2.2.8 の共変米田埋め込み よ : C ↪ Set^Cᵒᵖ。本文の定義と一致するため写し、
-- statement では Mathlib のものを使う。`↾` は関数を Type 圏の射とみなす `asHom`
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj Y := (unop Y) ⟶ X
      map f := ↾fun g ↦ f.unop ≫ g }
  map f :=
    { app _ := ↾fun g ↦ g ≫ f }

-- 反変米田埋め込み よ : Cᵒᵖ ↪ Set^C。Mathlib では yoneda の flip として実装される。
-- `coyoneda.obj (op c)` が本の C(c,−) に当たる
abbrev coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ := yoneda.flip

-- 例1.3.9・1.4.4 の「BG 上の関手 = G-set、自然変換 = 同変写像」の Mathlib 側の語彙。
-- `X →[M] Y` は `MulActionHom (@id M) X Y` の記法で、`map_smul'` が自然性に当たる
structure MulActionHom {M N : Type u₂} (φ : M → N)
    (X : Type u₂) [SMul M X] (Y : Type u₂) [SMul N Y] where
  toFun : X → Y
  map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

-- 演習2.2.iii の ω = (ℕ, ≤) を圏にする仕組み。hom は不等式の証明を universe 0 に
-- 持ち上げたもの。Mathlib ではインスタンスとして登録済み（二重登録を避けるため
-- ここでは abbrev として写す）
abbrev smallCategory (α : Type u₂) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans f.down.down g.down.down⟩⟩

end Recap

-- ═══════════════════════════════════════════════════════════════════════════
-- 本体
-- ═══════════════════════════════════════════════════════════════════════════

-- ── Part A: ウォームアップ（命題2.2.3） ─────────────────────────────────────

-- 命題2.2.3。左作用つきの G 自身から G-set X への同変写像は ϕ ↦ ϕ(e) で X の要素と
-- 一対一。Mathlib に一般の対応物はなく、X = G の場合だけが以下（モノイド一般、Gᵐᵒᵖ 値）
#check @MulActionHom.End.equivMulOpposite

example {G X : Type u₂} [Group G] [MulAction G X] :
    Function.Bijective (fun ϕ : G →[G] X => ϕ 1) := sorry

-- ── Part B: 定理2.2.4（米田の補題、共変版） ─────────────────────────────────

-- 定理2.2.4 の逆写像 Ψ。要素 x ∈ Fc から自然変換 Ψ(x) : C(c,−) ⇒ F を構成する
#check @CategoryTheory.coyonedaEquiv

def myCoyonedaNatTrans {F : C ⥤ Type v₁} {c : C} (x : F.obj c) :
    coyoneda.obj (op c) ⟶ F := sorry

-- 定理2.2.4 の全単射のうち、Ψ が ev_id の右逆であること
#check @CategoryTheory.coyonedaEquiv

example {F : C ⥤ Type v₁} {c : C} (x : F.obj c) :
    (myCoyonedaNatTrans x).app c (𝟙 c) = x := sorry

-- 定理2.2.4 の全単射のうち、Ψ が ev_id の左逆であること
#check @CategoryTheory.coyonedaEquiv

example {F : C ⥤ Type v₁} {c : C} (α : coyoneda.obj (op c) ⟶ F) :
    myCoyonedaNatTrans (α.app c (𝟙 c)) = α := sorry

-- 定理2.2.4 の自然性のうち、関手 F についての自然性
#check @CategoryTheory.coyonedaEquiv_comp

example {F G : C ⥤ Type v₁} {c : C} (α : coyoneda.obj (op c) ⟶ F) (β : F ⟶ G) :
    (α ≫ β).app c (𝟙 c) = β.app c (α.app c (𝟙 c)) := sorry

-- 定理2.2.4 の自然性のうち、対象 c についての自然性
#check @CategoryTheory.coyonedaEquiv_naturality

example {F : C ⥤ Type v₁} {c d : C} (f : c ⟶ d) (α : coyoneda.obj (op c) ⟶ F) :
    (coyoneda.map f.op ≫ α).app d (𝟙 d) = F.map f (α.app c (𝟙 c)) := sorry

-- 注意2.2.7 の二変数の自然同型への畳み込みは Mathlib では
-- `coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C`。Remark のため演習にしない

-- ── Part C: 演習2.2.i（双対米田、反変版） ───────────────────────────────────

-- 演習2.2.i の逆写像。要素 x ∈ Fc から自然変換 Ψ(x) : C(−,c) ⇒ F を構成する
#check @CategoryTheory.yonedaEquiv

def myYonedaNatTrans {F : Cᵒᵖ ⥤ Type v₁} {c : C} (x : F.obj (op c)) :
    yoneda.obj c ⟶ F := sorry

-- 演習2.2.i の全単射のうち、Ψ が ev_id の右逆であること
#check @CategoryTheory.yonedaEquiv

example {F : Cᵒᵖ ⥤ Type v₁} {c : C} (x : F.obj (op c)) :
    (myYonedaNatTrans x).app (op c) (𝟙 c) = x := sorry

-- 演習2.2.i の全単射のうち、Ψ が ev_id の左逆であること
#check @CategoryTheory.yonedaEquiv

example {F : Cᵒᵖ ⥤ Type v₁} {c : C} (α : yoneda.obj c ⟶ F) :
    myYonedaNatTrans (α.app (op c) (𝟙 c)) = α := sorry

-- 演習2.2.i の自然性のうち、関手 F についての自然性
#check @CategoryTheory.yonedaEquiv_comp

example {F G : Cᵒᵖ ⥤ Type v₁} {c : C} (α : yoneda.obj c ⟶ F) (β : F ⟶ G) :
    (α ≫ β).app (op c) (𝟙 c) = β.app (op c) (α.app (op c) (𝟙 c)) := sorry

-- 演習2.2.i の自然性のうち、対象 c についての自然性
#check @CategoryTheory.yonedaEquiv_naturality

example {F : Cᵒᵖ ⥤ Type v₁} {c d : C} (f : c ⟶ d) (α : yoneda.obj d ⟶ F) :
    (yoneda.map f ≫ α).app (op c) (𝟙 c) = F.map f.op (α.app (op d) (𝟙 d)) := sorry

-- ── Part D: 系2.2.8（米田埋め込み）と演習2.2.iii ────────────────────────────

-- 系2.2.8 のうち、共変米田埋め込み よ : C ↪ Set^Cᵒᵖ の充満性
#check @CategoryTheory.Yoneda.yoneda_full

example : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full := sorry

-- 系2.2.8 のうち、共変米田埋め込みの忠実性
#check @CategoryTheory.Yoneda.yoneda_faithful

example : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful := sorry

-- 系2.2.8 のうち、反変米田埋め込み よ : Cᵒᵖ ↪ Set^C の充満性
#check @CategoryTheory.Coyoneda.coyoneda_full

example : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full := sorry

-- 系2.2.8 のうち、反変米田埋め込みの忠実性
#check @CategoryTheory.Coyoneda.coyoneda_faithful

example : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful := sorry

-- 演習2.2.iii のうち、ω = (ℕ, ≤) 上の米田埋め込みの充満性。米田の補題を使わない
--    直接証明が趣旨（ωᵒᵖ 添字の族としての記述の前段は形式化しない）
#check @CategoryTheory.Yoneda.yoneda_full

example : (yoneda : ℕ ⥤ ℕᵒᵖ ⥤ Type).Full := sorry

-- 演習2.2.iii のうち、同じ埋め込みの忠実性
#check @CategoryTheory.Yoneda.yoneda_faithful

example : (yoneda : ℕ ⥤ ℕᵒᵖ ⥤ Type).Faithful := sorry

-- ── Part E: 応用（系2.2.10・系2.2.11） ──────────────────────────────────────

-- 系2.2.10。n 行の行列全体への操作の族 φ が右乗法と可換（= Hom(−,n) の自然自己変換）
--    なら、φ は φ_n(1) の左乗法で与えられる。Mathlib に対応物なし
example {R : Type u₂} [Ring R] {n : ℕ}
    (φ : ∀ m : ℕ, Matrix (Fin n) (Fin m) R → Matrix (Fin n) (Fin m) R)
    (hφ : ∀ {m m' : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin m') R),
      φ m' (A * B) = φ m A * B)
    {m : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    φ m A = φ n 1 * A := sorry

-- 系2.2.11（Cayley の定理）。任意の群は、ある置換群の部分群と同型である
#check @Equiv.Perm.subgroupOfMulAction

example {G : Type u₂} [Group G] : ∃ H : Subgroup (Equiv.Perm G), Nonempty (G ≃* H) := sorry

-- ── Part F: Lean で述べにくい節末問題 ───────────────────────────────────────
--
-- 以下は statement を置かず、問題文だけを残す。
--
-- 演習2.2.ii: 米田の補題が「任意の集合値関手から表現された関手への自然変換」の分類には
--   双対化しない理由を説明する。説明問題であり、statement の形にならない。
--
-- 演習2.2.iv: iso : Cat → Set は mor : Cat → Set の部分関手である。米田の補題を使って、
--   対応する単射自然変換を誘導する表現対象の間の関手 I → 2 を定義する。Cat の対象として
--   圏 I・2 を持ち回る構成が重く、形式化しない。
--
-- 演習2.2.v: 反変冪集合関手 P : Setᵒᵖ → Set の自然自己変換は表現対象 Ω = {⊥, ⊤} の
--   自己射4つと対応する。それぞれの自然自己変換を記述し、共変冪集合関手の自然自己変換を
--   誘導するか判定する。記述が答えそのものであり、statement を置くと問題が成立しない。
--
-- 演習2.2.vi: 単位区間 I = [0,1] の自己同相と、道の関手 Path : Top → Set の自然自己同型
--   （パラメータの取り替え）の関係を米田の補題で説明する。Top と Path の設営が重く、
--   説明問題でもあるため形式化しない。
--
-- 演習2.2.vii: 忘却関手 U : Top → Set・U : Vect_k → Set の自然自己変換をすべて特徴づけ、
--   恒等関手 id_Top・id_Vect の自然自己変換に精密化する。特徴づけの主張の形自体が答えの
--   一部になるため、statement を置かない。
