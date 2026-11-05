import Mathlib.CategoryTheory.Category.Preorder

/-!
# 前順序と、射が高々 1 本の圏

本は前順序を、反射的かつ推移的な二項関係 ≤ を持つ集合と定義し、例1.1.4 (iii) でそれを圏と
見る。脚注10 は、前順序がまさに、2 対象の間に異なる平行な射の対を持たない圏のことだと言い
換えるが、証明は与えていない。この言い換えを、前順序から圏への対応と圏から前順序への対応が
互いに逆であることとして確かめる。節に対応しない話題なので解説資料はない。
-/

open CategoryTheory

namespace Riehl

universe v u

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 前順序から圏へ（例1.1.4 (iii)）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
前順序 (P, ≤) を圏と見ると、どの 2 対象 x, y ∈ P の間にも射は高々 1 本である。

構成: 圏は 2.2 で組んだ `Preorder.smallCategory`。射が高々 1 本であることは 3.7 で使った
      `Quiver.IsThin` で書く。
-/

#check Preorder.smallCategory

theorem isThin_of_preorder (P : Type u) [Preorder P] : Quiver.IsThin P := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 圏から前順序へ（脚注10）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の圏 C について、対象の間の関係「x ≤ y ⇔ x から y への射が存在する」は前順序である。

構成: 関係は脚注10 の言い換えから読み取れるので書き、反射律と推移律を演習にする。この関係が
      前順序であることに、射が高々 1 本であることは使わない。
-/

abbrev preorderOfCategory (C : Type u) [Category.{v} C] : Preorder C where
  le x y := Nonempty (x ⟶ y)
  le_refl := sorry
  le_trans := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 前順序 → 圏 → 前順序
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 前順序 (P, ≤) を圏と見て、そこから前順序を作ると、元の前順序 ≤ に戻る。

theorem preorderOfCategory_eq (P : Type u) [inst : Preorder P] :
    preorderOfCategory P = inst :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 圏 → 前順序 → 圏
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
どの 2 対象の間にも射が高々 1 本しかない圏 C から前順序を作り、それを圏と見ると、C と同型な
圏が得られる。すなわち、互いに逆な関手 C → P と P → C がある。ここで P は C の対象に
`preorderOfCategory C` の前順序を入れたものを圏と見たもの。

構成: P は、C と同じ対象を持ち C の圏の構造を忘れた型 `AsPreorder C` に、前順序
      `preorderOfCategory C` を入れたもの。その圏の構造は `Preorder.smallCategory`。
      二つの関手を組み、合成がそれぞれ恒等関手に等しいことを示す。C → P は射が高々 1 本で
      あることを使わずに組める。
-/

def AsPreorder (C : Type u) : Type u := C

instance (C : Type u) [Category.{v} C] : Preorder (AsPreorder C) := preorderOfCategory C

def toAsPreorder (C : Type u) [Category.{v} C] : C ⥤ AsPreorder C := sorry

noncomputable def fromAsPreorder (C : Type u) [Category.{v} C] [Quiver.IsThin C] :
    AsPreorder C ⥤ C :=
  sorry

theorem toAsPreorder_comp_fromAsPreorder (C : Type u) [Category.{v} C] [Quiver.IsThin C] :
    toAsPreorder C ⋙ fromAsPreorder C = 𝟭 C :=
  sorry

theorem fromAsPreorder_comp_toAsPreorder (C : Type u) [Category.{v} C] [Quiver.IsThin C] :
    fromAsPreorder C ⋙ toAsPreorder C = 𝟭 (AsPreorder C) :=
  sorry

end Riehl
