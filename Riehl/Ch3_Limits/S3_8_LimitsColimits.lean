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
Mathlib の `IsCardinalFiltered`）は載せない。(3.8.2) の余極限の半分は双対なので載せない。
定理3.8.9 の後の、代数理論のモデルの圏についての段落は、定理5.6.5 に依存するので載せない。
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
図式 F : I × J → C について、各 i ∈ I で limit F(i, -) が存在し、図式 i ↦ limit F(i, -) の極限
が存在するならば、F は極限を持ち、limit F はこの繰り返し極限と同型である。さらに、各 j ∈ J で
limit F(-, j) が存在し、図式 j ↦ limit F(-, j) の極限も存在するならば、二つの繰り返し極限は
同型である。

構成: F を I → C^J と見たものは `curry.obj F`（演習1.7.vi）、図式 i ↦ limit F(i, -) は
      それに極限関手 `lim`（命題3.3.1）を合成した `curry.obj F ⋙ lim`。変数を入れ替えた
      図式 J × I → C は `CategoryTheory.Prod.swap J I ⋙ F`。結論の「極限を持つ」「同型」「二つの繰り返し
      極限の同型」を 3 つの宣言に分ける。
-/

-- 積圏の成分を入れ替える関手 J × I → I × J
#check CategoryTheory.Prod.swap

theorem hasLimit_of_hasLimit_curry_comp_lim (F : I × J ⥤ C) [HasLimitsOfShape J C]
    [HasLimit (curry.obj F ⋙ lim)] : HasLimit F :=
  sorry

#check limitIsoLimitCurryCompLim

noncomputable def limitIsoLimitCurryCompLim' (F : I × J ⥤ C) [HasLimitsOfShape J C]
    [HasLimit (curry.obj F ⋙ lim)] [HasLimit F] : limit F ≅ limit (curry.obj F ⋙ lim) :=
  sorry

#check limitCurrySwapCompLimIsoLimitCurryCompLim

noncomputable def limitCurrySwapCompLimIsoLimitCurryCompLim' (F : I × J ⥤ C)
    [HasLimitsOfShape I C] [HasLimitsOfShape J C] [HasLimit (curry.obj F ⋙ lim)]
    [HasLimit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim)] :
    limit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ lim) ≅ limit (curry.obj F ⋙ lim) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- (3.8.2)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C が I 型と J 型の極限を持つとき、二通りの合成 C^{I×J} → C^I → C と C^{I×J} → C^J → C の
極限関手は自然同型である。

構成: C^{I×J} は同型な (C^J)^I（演習1.7.vi）で取る。C^{I×J} → C^I は、各 i で J 方向の極限を
      取る関手で、`lim` を後ろから合成する関手 `(whiskeringRight I (J ⥤ C) C).obj lim`。
      C^{I×J} → C^J は、(C^J)^I を (C^I)^J に移す同型 `flipping.functor` の後に、各 j で
      I 方向の極限を取る関手を続けたもの。
-/

-- 関手 G に関手 H を後ろから合成する操作 G ↦ G ⋙ H を関手にしたもの
#check whiskeringRight
-- 2 変数の関手 I → J → C を J → I → C に移す圏同型
#check flipping
-- 対象ごとの Mathlib の対応物
#check limitFlipCompLimIsoLimitCompLim

noncomputable def limCompLimIso [HasLimitsOfShape I C] [HasLimitsOfShape J C] :
    (whiskeringRight I (J ⥤ C) C).obj lim ⋙ lim ≅
      flipping.functor ⋙ (whiskeringRight J (I ⥤ C) C).obj lim ⋙ lim :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.8.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
双関手 F : I × J → C について、C が J 型の極限と I 型の余極限を持つならば、標準的な射
κ : colimit (i ↦ limit F(i, -)) → limit (j ↦ colimit F(-, j)) があり、その成分は
κ_{i,j} = ι_{i,j} ∘ π_{i,j} である。

構成: κ を与える宣言と、κ の成分が ι_{i,j} ∘ π_{i,j} であることの宣言に分ける。後者が「標準的」
      の中身で、Lean では左辺を余極限の脚 i と極限の脚 j で挟んで書く。図式
      j ↦ colimit F(-, j) は `curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ colim`。Mathlib の対応物は
      F を J × I から取るので、一致は `CategoryTheory.Prod.swap J I ⋙ F` について述べる。
-/

-- 余極限関手。命題3.3.1 の双対
#check colim

noncomputable def colimLimComparison (F : I × J ⥤ C) [HasLimitsOfShape J C]
    [HasColimitsOfShape I C] :
    colimit (curry.obj F ⋙ lim) ⟶ limit (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ colim) :=
  sorry

theorem ι_colimLimComparison_π (F : I × J ⥤ C) [HasLimitsOfShape J C]
    [HasColimitsOfShape I C] (i : I) (j : J) :
    colimit.ι (curry.obj F ⋙ lim) i ≫ colimLimComparison F ≫
        limit.π (curry.obj (CategoryTheory.Prod.swap J I ⋙ F) ⋙ colim) j =
      limit.π ((curry.obj F).obj i) j ≫
        colimit.ι ((curry.obj (CategoryTheory.Prod.swap J I ⋙ F)).obj j) i :=
  sorry

#check colimitLimitToLimitColimit

theorem colimLimComparison_eq (F : I × J ⥤ C) [HasLimitsOfShape J C]
    [HasColimitsOfShape I C] :
    colimLimComparison F = colimitLimitToLimitColimit (CategoryTheory.Prod.swap J I ⋙ F) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系3.8.4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の集合 X, Y と関数 f : X × Y → ℝ について、下限 a x = inf_y f(x, y)、上限 s = sup_x a x、
上限 b y = sup_x f(x, y)、下限 t = inf_y b y が存在するならば、s ≤ t である。

構成: 「存在するならば」を、それぞれが下限・上限であるという仮定 `IsGLB`・`IsLUB`（3.6）で
      書く。
-/

-- 完備束での Mathlib の対応物
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
圏 J がフィルター圏であるとは、J の任意の有限な図式 F : K → J の下に錐があることである。

構成: 有限な図式は、対象と射が有限個の小圏 K（`FinCategory`）で添字づけた図式。Mathlib の
      `IsFiltered` は、空でないこと、2 対象の下の錐、平行な対を等しくする射の 3 条件で
      定義されているので、本の定義との同値を示す。
-/

-- 対象の型と各 hom 型が有限な圏
#check FinCategory
#check IsFiltered

def IsFiltered' (D : Type u) [Category.{v} D] : Prop :=
  ∀ (K : Type v) [SmallCategory K] [FinCategory K] (F : K ⥤ D), Nonempty (Cocone F)

theorem isFiltered'_iff (D : Type u) [Category.{v} D] : IsFiltered' D ↔ IsFiltered D := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- フィルター余極限の記述（定理3.8.9 の前）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小さなフィルター圏 J で添字づけた図式 F : J → Set について、x ∈ F j と y ∈ F k が colimit F で
等しいことと、J の射 f : j → t と g : k → t で F f(x) = F g(y) となるものが存在することは
同値である。

構成: 「より一般に、有限個の要素が共通の F t に送られる」という続きは、この主張を有限回
      使って得られるので置かない。
-/

#check Types.FilteredColimit.colimit_eq_iff

theorem colimit_eq_iff' [IsFiltered J] (F : J ⥤ Type v) {j k : J} (x : F.obj j) (y : F.obj k) :
    colimit.ι F j x = colimit.ι F k y ↔ ∃ (t : J) (f : j ⟶ t) (g : k ⟶ t), F.map f x = F.map g y :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.8.9
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
有限な圏 I と小さなフィルター圏 J について、任意の関手 F : I × J → Set の標準的な射
κ : colimit (j ↦ limit F(-, j)) → limit (i ↦ colimit F(i, -)) は同型である。

構成: κ は補題3.8.3 の Mathlib の対応物 `colimitLimitToLimitColimit`。これは F を I × J から
      取り、I 方向の極限と J 方向の余極限を比べるので、本の向きそのまま。
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
-- 冪等射の分裂が任意の形の極限・余極限と交換することを、演習3.4.vi から結論する問題。冪等射の
-- 分裂を図式の極限として述べるには、冪等射を 1 つ持つ 1 対象圏が要るが、Mathlib になく、
-- 3.4 でもレトラクトの条件式で扱ったので、形式化が不自然になり置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.8.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
G と H が位数の互いに素な有限群ならば、任意の関手 F : BG × BH → Set について、標準的な射
κ : colimit (h ↦ limit F(-, h)) → limit (g ↦ colimit F(g, -)) は同型である。

構成: BG は `SingleObj G`（例3.2.10）。群の位数は `Nat.card`。
-/

theorem colimitLimitToLimitColimit_isIso_of_coprime {G H : Type v} [Group G] [Group H]
    [Finite G] [Finite H] (hGH : Nat.Coprime (Nat.card G) (Nat.card H))
    (F : SingleObj G × SingleObj H ⥤ Type v) :
    IsIso (colimitLimitToLimitColimit F) :=
  sorry

end Riehl
