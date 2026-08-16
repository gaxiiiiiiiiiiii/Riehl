import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.Perm.Subgroup

-- ═══════════════════════════════════════════════════════════════════════════
-- 概要
-- ═══════════════════════════════════════════════════════════════════════════
/-!
# 2.2 米田の補題

集合値関手 F : C ⥤ Set への自然変換 C(c,−) ⇒ F が要素 x ∈ Fc と一対一に対応する
ことを示す節。中心は定理2.2.4（米田の補題）と系2.2.8（米田埋め込みの充満忠実性）で、
2.3 の普遍性、2.4 の要素の圏、3章の極限、4章の随伴の一意性すべての土台になる。

本の Set 値関手は `Type v₁` 値関手（hom と同じ宇宙）に翻訳する。逆写像 Ψ（式(2.2.5)）
は式を見つけること自体が演習の核心なので、`myΨ` は data ごと丸ごと `sorry` にする
（1.7 の data 先渡し方式と逆の選択。経緯は companion の「形式化のズレの背景」参照）。

ファイル構成:
  Recap: `yoneda`・`coyoneda`（表現可能関手と米田埋め込み）・`MulActionHom`・
    `Preorder.smallCategory`（演習2.2.iii の ω を圏にする instance）の写し
  本体:
    Part A: 命題2.2.3（ウォームアップ: G-集合）
    Part B: 定理2.2.4（Ψ の構成・全単射・二重の自然性）
    Part C: 系2.2.8（米田埋め込み）
    Part D: 系2.2.10・系2.2.11（行列圏と Cayley の定理）
    Part E: 節末問題

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Yoneda.lean`
    （`yoneda`・`coyoneda`・`yonedaEquiv`・`coyonedaEquiv`・`coyonedaLemma`）
  - `Mathlib/GroupTheory/GroupAction/Hom.lean`（`MulActionHom`）
  - `Mathlib/GroupTheory/Perm/Subgroup.lean`（`Equiv.Perm.subgroupOfMulAction`）
  - `Mathlib/CategoryTheory/Preadditive/Mat.lean`（`Mat`）
  - `Mathlib/CategoryTheory/Category/Preorder.lean`（`Preorder.smallCategory`）
-/

open CategoryTheory Opposite

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

-- ═══════════════════════════════════════════════════════════════════════════
-- 前提: 演習が使う Mathlib の定義
-- ═══════════════════════════════════════════════════════════════════════════

namespace Recap

variable {C : Type u₁} [Category.{v₁} C]

-- 共変米田埋め込み よ : C ↪ Set^(Cᵒᵖ)。対象 X を反変表現可能関手 C(−, X) に送り、
-- 射には後合成（例1.4.9 の f₊）で作用する
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj Y := unop Y ⟶ X
      map f := ↾fun g ↦ f.unop ≫ g }
  map f := { app _ := ↾fun g ↦ g ≫ f }

-- 反変米田埋め込み よ : Cᵒᵖ ↪ Set^C。Mathlib は独立に定義せず二変数 hom 関手の
-- flip として得る（演習1.7.vii の「共通の二変数関手の二つの化身」がそのまま実装）
abbrev coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ :=
  yoneda.flip

-- 例1.4.4(iv) の同変写像。φ を単位写像 id にした記法が `X →[M] Y` で、
-- 命題2.2.3 は `G →[G] X` の形で使う
structure MulActionHom {M N : Type u₁} (φ : M → N)
    (X : Type u₁) [SMul M X] (Y : Type u₁) [SMul N Y] where
  toFun : X → Y
  map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

-- 演習2.2.iii の statement が暗黙に使う、preorder を圏と見る instance。hom は X ≤ Y の
-- 証明を `Prop` の外へ包んだ `ULift (PLift (X ≤ Y))`。二重登録を避けて写しは def にする
@[instance_reducible]
def Preorder.smallCategory (α : Type u₁) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans f.down.down g.down.down⟩⟩

end Recap

-- ═══════════════════════════════════════════════════════════════════════════
-- 本体
-- ═══════════════════════════════════════════════════════════════════════════

-- ── Part A: ウォームアップ（命題2.2.3） ─────────────────────────────────────

-- 命題2.2.3。左正則作用の G-集合 G からの同変写像 ϕ : G → X は、単位元の像 ϕ(e) と
--    一対一。全単射になる写像 ϕ ↦ ϕ(e) を固定して述べる。Mathlib の対応物は
--    X = M（モノイド一般）の特殊形で、値が反対モノイド Mᵐᵒᵖ に落ちる。
#check @MulActionHom.End.equivMulOpposite

example {G : Type u₁} [Group G] {X : Type u₂} [MulAction G X] :
    Function.Bijective (fun ϕ : G →[G] X => ϕ (1 : G)) := sorry

-- ── Part B: 米田の補題（定理2.2.4） ─────────────────────────────────────────

-- 式(2.2.5) の Ψ。要素 x ∈ Fc から自然変換 Ψ(x) : C(c,−) ⇒ F を作る。
--    成分の式を見つけるところからが演習（Mathlib では `coyonedaEquiv` の逆方向）。
#check @CategoryTheory.coyonedaEquiv

def myΨ (F : C ⥤ Type v₁) (c : C) (x : F.obj c) : coyoneda.obj (op c) ⟶ F := sorry

-- 定理2.2.4 の全単射のうち「Ψ は ev_id の右逆」。ev_id(Ψ(x)) = x を示す。
--    Mathlib では `coyonedaEquiv` の `right_inv` に相当。
#check @CategoryTheory.coyonedaEquiv

example (F : C ⥤ Type v₁) (c : C) (x : F.obj c) :
    (myΨ F c x).app c (𝟙 c) = x := sorry

-- 定理2.2.4 の全単射のうち「Ψ は ev_id の左逆」。Ψ(ev_id(α)) = α を示す。
--    Mathlib では `coyonedaEquiv` の `left_inv` に相当。
#check @CategoryTheory.coyonedaEquiv

example (F : C ⥤ Type v₁) (c : C) (α : coyoneda.obj (op c) ⟶ F) :
    myΨ F c (α.app c (𝟙 c)) = α := sorry

-- 定理2.2.4 の自然性のうち関手方向。β : F ⇒ G と縦合成してから評価しても、
--    評価してから成分 β_c で送っても同じ。
#check @CategoryTheory.coyonedaEquiv_comp

example {F G : C ⥤ Type v₁} (c : C) (β : F ⟶ G) (α : coyoneda.obj (op c) ⟶ F) :
    (α ≫ β).app c (𝟙 c) = β.app c (α.app c (𝟙 c)) := sorry

-- 定理2.2.4 の自然性のうち対象方向。f : c → d の前合成 f* で引き戻してから評価しても、
--    評価してから F f で送っても同じ。
#check @CategoryTheory.coyonedaEquiv_naturality

example (F : C ⥤ Type v₁) {c d : C} (f : c ⟶ d) (α : coyoneda.obj (op c) ⟶ F) :
    (coyoneda.map f.op ≫ α).app d (𝟙 d) = F.map f (α.app c (𝟙 c)) := sorry

-- 注意2.2.7 に対応する Mathlib の宣言は `coyonedaPairing`・`coyonedaEvaluation` と
-- 両者の自然同型 `coyonedaLemma`（C × Set^C 上の関手として述べた米田の補題）。
-- 本文の SET の但し書きは、値を `Type (max u₁ v₁)` に持ち上げる `uliftFunctor` が
-- 受け持つ。

-- ── Part C: 米田埋め込み（系2.2.8） ─────────────────────────────────────────

-- 系2.2.8 のうち共変埋め込み よ : C ↪ Set^(Cᵒᵖ) の充満性。
#check @CategoryTheory.Yoneda.yoneda_full

example : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full := sorry

-- 系2.2.8 のうち共変埋め込みの忠実性。
#check @CategoryTheory.Yoneda.yoneda_faithful

example : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful := sorry

-- 系2.2.8 のうち反変埋め込み よ : Cᵒᵖ ↪ Set^C の充満性。
#check @CategoryTheory.Coyoneda.coyoneda_full

example : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full := sorry

-- 系2.2.8 のうち反変埋め込みの忠実性。
#check @CategoryTheory.Coyoneda.coyoneda_faithful

example : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful := sorry

-- ── Part D: 充満性の応用（系2.2.10・系2.2.11） ──────────────────────────────

-- 系2.2.10。行列圏では表現可能関手の自然な自己変換が必ず「𝟙 n の像との合成」になる。
--    Mathlib の `Mat R` は射 m ⟶ n が m×n 行列（本の Mat_R の転置）なので、本の
--    「行演算＝左乗算」は「列演算＝右乗算」の形になる。Mathlib に対応物なし。
example {R : Type} [Ring R] {m n : Mat R} (α : yoneda.obj n ⟶ yoneda.obj n) (M : m ⟶ n) :
    α.app (op m) M = M ≫ α.app (op n) (𝟙 n) := sorry

-- 系2.2.11（Cayley の定理）。任意の群は、ある置換群の部分群と同型。
--    Mathlib の対応物は忠実な作用一般への一般化（X = G が本の場合）。
#check @Equiv.Perm.subgroupOfMulAction

example (G : Type u₁) [Group G] :
    ∃ (X : Type u₁) (H : Subgroup (Equiv.Perm X)), Nonempty (G ≃* H) := sorry

-- ── Part E: 節末問題 ────────────────────────────────────────────────────────

-- 演習2.2.i。定理2.2.4 の双対（反変版）を Part B と同じ分割で置く。C(−,c) への
--    自然変換が Fc の要素と対応する。まず逆写像の構成。
#check @CategoryTheory.yonedaEquiv

def myΨop (F : Cᵒᵖ ⥤ Type v₁) (c : C) (x : F.obj (op c)) : yoneda.obj c ⟶ F := sorry

-- 演習2.2.i の全単射のうち「右逆」。
#check @CategoryTheory.yonedaEquiv

example (F : Cᵒᵖ ⥤ Type v₁) (c : C) (x : F.obj (op c)) :
    (myΨop F c x).app (op c) (𝟙 c) = x := sorry

-- 演習2.2.i の全単射のうち「左逆」。
#check @CategoryTheory.yonedaEquiv

example (F : Cᵒᵖ ⥤ Type v₁) (c : C) (α : yoneda.obj c ⟶ F) :
    myΨop F c (α.app (op c) (𝟙 c)) = α := sorry

-- 演習2.2.i の自然性のうち関手方向。
#check @CategoryTheory.yonedaEquiv_comp

example {F G : Cᵒᵖ ⥤ Type v₁} (c : C) (β : F ⟶ G) (α : yoneda.obj c ⟶ F) :
    (α ≫ β).app (op c) (𝟙 c) = β.app (op c) (α.app (op c) (𝟙 c)) := sorry

-- 演習2.2.i の自然性のうち対象方向。
#check @CategoryTheory.yonedaEquiv_naturality

example (F : Cᵒᵖ ⥤ Type v₁) {c d : C} (g : d ⟶ c) (α : yoneda.obj c ⟶ F) :
    (yoneda.map g ≫ α).app (op d) (𝟙 d) = F.map g.op (α.app (op c) (𝟙 c)) := sorry

-- 演習2.2.ii。米田の補題は「任意の集合値関手から表現可能関手への自然変換
--    F ⇒ C(−,c)」の分類には双対化しない。その理由を説明する問題。説明問題なので
--    statement は置かない。

-- 演習2.2.iii。米田埋め込み よ : ω ↪ Set^(ωᵒᵖ) を「ωᵒᵖ 添字の集合族と自然変換の族」
--    として記述し、米田の補題に訴えず充満忠実性を直接示す問題。記述の前半は形式化せず、
--    ω を ℕ の順序圏として後半のみ置く。Mathlib には一般の系2.2.8 のインスタンス
--    しかない（本問は ω への特殊化）。

-- 演習2.2.iii のうち充満性。
#check @CategoryTheory.Yoneda.yoneda_full

example : (yoneda : ℕ ⥤ ℕᵒᵖ ⥤ Type).Full := sorry

-- 演習2.2.iii のうち忠実性。
#check @CategoryTheory.Yoneda.yoneda_faithful

example : (yoneda : ℕ ⥤ ℕᵒᵖ ⥤ Type).Faithful := sorry

-- 演習2.2.iv。部分関手 iso ⊆ mor : Cat → Set のモニックな自然変換を、表現対象 I と 2
--    の間の関手から誘導する問題。walking isomorphism の圏 I が Mathlib になく、
--    「表現対象の間の射が自然変換を誘導する」構図の再現も重いため、問題文のみ残す。
--    Mathlib に対応物なし。

-- 演習2.2.v。反変冪集合関手 P : Setᵒᵖ → Set の自然な自己変換は、表現対象 Ω = {⊥,⊤}
--    の自己射 4 つと対応する。それぞれを記述し、共変冪集合関手にも自然な自己変換を
--    誘導するか問う問題。記述の形自体が答えの一部になるため statement は置かない
--    （演習1.5.vii と同じ扱い）。

-- 演習2.2.vi。単位区間 I = [0,1] の自己同相と、道関手 Path : Top → Set の自然な
--    自己同型（reparameterization）の関係を米田の補題で説明する問題。説明問題なので
--    statement は置かない。

-- 演習2.2.vii。忘却関手 U : Top → Set・U : Vect_k → Set と恒等関手 id_Top・
--    id_Vect_k の自然な自己変換をそれぞれ特徴づける問題。特徴づけの主張の形自体が
--    答えの一部になるため statement は置かない（演習1.5.vii と同じ扱い）。
