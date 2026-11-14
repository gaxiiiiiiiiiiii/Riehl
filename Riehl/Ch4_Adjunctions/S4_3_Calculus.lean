import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Equivalence

/-!
# 4.3 随伴の計算

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 節冒頭の引用、Remark 4.3.9（構文的な証明と米田流の証明の適用範囲）、
脚注6〜9 は載せない。
-/

open CategoryTheory Functor

namespace Riehl

universe v u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

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

#check Adjunction.leftAdjointUniq

-- 自然同型 θ : F ≅ F′
def leftAdjointUniq' {F F' : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (τ : F' ⊣ G) : F ≅ F' :=
  sorry

#check Adjunction.unit_leftAdjointUniq_hom

-- Gθ ⋅ η = η′
theorem unit_leftAdjointUniq_hom' {F F' : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (τ : F' ⊣ G) :
    σ.unit ≫ whiskerRight (leftAdjointUniq' σ τ).hom G = τ.unit :=
  sorry

#check Adjunction.leftAdjointUniq_hom_counit

-- ε′ ⋅ θG = ε
theorem leftAdjointUniq_hom_counit' {F F' : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (τ : F' ⊣ G) :
    whiskerLeft G (leftAdjointUniq' σ τ).hom ≫ τ.counit = σ.counit :=
  sorry

-- Gθ ⋅ η = η′ を満たす自然変換は θ に限る
theorem eq_leftAdjointUniq_hom_of_unit {F F' : C ⥤ D} {G : D ⥤ C} (σ : F ⊣ G) (τ : F' ⊣ G)
    (θ : F ⟶ F') (h : σ.unit ≫ whiskerRight θ G = τ.unit) :
    θ = (leftAdjointUniq' σ τ).hom :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 随伴 F ⊣ G（F : C ⇄ D : G）と F′ ⊣ G′（F′ : D ⇄ E : G′）が与えられたとき、合成 F′F は
-- 合成 GG′ の左随伴である。

#check Adjunction.comp

-- F′F ⊣ GG′
def compAdjunction {E : Type u₃} [Category.{v} E] {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E}
    {G' : E ⥤ D} (σ : F ⊣ G) (τ : F' ⊣ G') : F ⋙ F' ⊣ G' ⋙ G :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
向かい合う関手 F : C ⇄ D : G と自然変換 η : id_C ⇒ GF, ε : FG ⇒ id_D について、合成
φ ≔ εF ⋅ Fη : F ⇒ F と ψ ≔ Gε ⋅ ηG : G ⇒ G がどちらも可逆ならば、F ⊣ G であり、η を単位に
選ぶことも、ε を余単位に選ぶこともできる。

φ と ψ が可逆であるという仮定は、成分 φ_c = ε_{Fc} ∘ F(η_c) と ψ_d = G(ε_d) ∘ η_{Gd} が
すべて同型であることとして書く。η を単位に選ぶ場合と ε を余単位に選ぶ場合を別の宣言にし、
それぞれ、随伴と、その単位または余単位が与えられたものに等しいことを別の宣言にする。
-/

-- η を単位とする随伴 F ⊣ G
noncomputable def adjunctionOfUnit {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (ε : G ⋙ F ⟶ 𝟭 D) [∀ c, IsIso (F.map (η.app c) ≫ ε.app (F.obj c))]
    [∀ d, IsIso (η.app (G.obj d) ≫ G.map (ε.app d))] : F ⊣ G :=
  sorry

-- その単位は η
theorem adjunctionOfUnit_unit {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (ε : G ⋙ F ⟶ 𝟭 D) [∀ c, IsIso (F.map (η.app c) ≫ ε.app (F.obj c))]
    [∀ d, IsIso (η.app (G.obj d) ≫ G.map (ε.app d))] :
    (adjunctionOfUnit η ε).unit = η :=
  sorry

-- ε を余単位とする随伴 F ⊣ G
noncomputable def adjunctionOfCounit {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (ε : G ⋙ F ⟶ 𝟭 D) [∀ c, IsIso (F.map (η.app c) ≫ ε.app (F.obj c))]
    [∀ d, IsIso (η.app (G.obj d) ≫ G.map (ε.app d))] : F ⊣ G :=
  sorry

-- その余単位は ε
theorem adjunctionOfCounit_counit {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (ε : G ⋙ F ⟶ 𝟭 D) [∀ c, IsIso (F.map (η.app c) ≫ ε.app (F.obj c))]
    [∀ d, IsIso (η.app (G.obj d) ≫ G.map (ε.app d))] :
    (adjunctionOfCounit η ε).counit = ε :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系4.3.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の圏同値 F : C ⇄ D : G, η : id_C ≅ GF, ε : FG ≅ id_D は、最初に指定された自然同型の
どちらか一方を新しい単位または余単位に置き換えることで、自然同型が三角等式を満たす随伴同値に
取り替えることができる。

圏同値は 1.5 の定義1.5.4 の形で、F, G, η, ε を別々の引数にして与える。単位を置き換える場合と
余単位を置き換える場合を別の宣言にし、それぞれ、新しい自然同型と、それが満たす三角等式
ε_{Fc} ∘ F(η_c) = 1_{Fc} を別の宣言にする。Mathlib の `C ≌ D` は、この三角等式をフィールド
`functor_unitIso_comp` に持つ。`Equivalence.mk` は、単位を置き換えて `C ≌ D` を作る。
-/

#check Equivalence.adjointifyη

-- ε と三角等式を満たす新しい単位 id_C ≅ GF
def adjointifyη' {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    𝟭 C ≅ F ⋙ G :=
  sorry

#check Equivalence.adjointify_η_ε

-- 新しい単位と ε の三角等式
theorem adjointify_η_ε' {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) (c : C) :
    F.map ((adjointifyη' η ε).hom.app c) ≫ ε.hom.app (F.obj c) = 𝟙 (F.obj c) :=
  sorry

-- η と三角等式を満たす新しい余単位 FG ≅ id_D
def adjointifyε {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    G ⋙ F ≅ 𝟭 D :=
  sorry

-- η と新しい余単位の三角等式
theorem η_adjointifyε {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) (c : C) :
    F.map (η.hom.app c) ≫ (adjointifyε η ε).hom.app (F.obj c) = 𝟙 (F.obj c) :=
  sorry

-- 圏同値 F の逆 G は、F の右随伴でも左随伴でもある。Mathlib の `e : C ≌ D` では
-- `e.toAdjunction` と `e.symm.toAdjunction` で済むので宣言を置かない。
#check Equivalence.toAdjunction

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
随伴 F ⊣ G（F : C ⇄ D : G）が与えられたとき、任意の小圏 J について、F と G を後ろに合成する
関手は随伴 F_∗ ⊣ G_∗（F_∗ : C^J ⇄ D^J : G_∗）をなし、任意の局所小圏 E について、F と G を
前に合成する関手は随伴 G^∗ ⊣ F^∗（G^∗ : E^C ⇄ E^D : F^∗）をなす。

J と E の大きさについての仮定は、関手圏を局所小にするためのもので、宣言には置かない。

statement の項 := 本の記法
  (whiskeringRight J C D).obj F    := F_∗ : C^J → D^J, H ↦ FH
  (whiskeringRight J D C).obj G    := G_∗ : D^J → C^J, H ↦ GH
  (whiskeringLeft D C E).obj G     := G^∗ : E^C → E^D, H ↦ HG
  (whiskeringLeft C D E).obj F     := F^∗ : E^D → E^C, H ↦ HF
-/

#check Adjunction.whiskerRight

-- F_∗ ⊣ G_∗
def whiskerRightAdjunction (J : Type u₃) [Category.{v} J] {F : C ⥤ D} {G : D ⥤ C}
    (σ : F ⊣ G) : (whiskeringRight J C D).obj F ⊣ (whiskeringRight J D C).obj G :=
  sorry

#check Adjunction.whiskerLeft

-- G^∗ ⊣ F^∗
def whiskerLeftAdjunction (E : Type u₃) [Category.{v} E] {F : C ⥤ D} {G : D ⥤ C}
    (σ : F ⊣ G) : (whiskeringLeft D C E).obj G ⊣ (whiskeringLeft C D E).obj F :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.3.8
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
一対の随伴 F ⊣ G（F : C ⇄ D : G）と F′ ⊣ G′（F′ : C′ ⇄ D′ : G′）、および関手 H : C′ → C と
K : D′ → D が与えられたとき、自然変換 α♯ : FH ⇒ KF′ と自然変換 α♭ : HG′ ⇒ GK の間に、
2 つの随伴による転置で与えられる全単射がある。対応する α♯ と α♭ を互いのメイトという。

全単射を、α♯ から α♭ を得る写像、α♭ から α♯ を得る写像、この 2 つが互いに逆であることを述べる
2 つの等式の、4 つの宣言にする。Mathlib の `mateEquiv` は、2 つの型を `TwoSquare` で書いた
同じ全単射である。

H と K が恒等関手の場合の全単射で対応する自然変換 α♯ : F ⇒ F′ と α♭ : G′ ⇒ G を、互いの共役と
いう。この場合は 1 つの全単射として宣言する。

statement の項 := 本の記法
  H ⋙ F ⟶ F' ⋙ K     := FH ⇒ KF′
  G' ⋙ H ⟶ K ⋙ G     := HG′ ⇒ GK
-/

section

variable {C' : Type u₃} [Category.{v} C'] {D' : Type u₄} [Category.{v} D']

#check mateEquiv

-- α♯ : FH ⇒ KF′ のメイト α♭ : HG′ ⇒ GK
def rightAdjointMate {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'} {H : C' ⥤ C}
    {K : D' ⥤ D} (σ : F ⊣ G) (τ : F' ⊣ G') (α : H ⋙ F ⟶ F' ⋙ K) : G' ⋙ H ⟶ K ⋙ G :=
  sorry

-- α♭ : HG′ ⇒ GK のメイト α♯ : FH ⇒ KF′
def leftAdjointMate {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'} {H : C' ⥤ C}
    {K : D' ⥤ D} (σ : F ⊣ G) (τ : F' ⊣ G') (β : G' ⋙ H ⟶ K ⋙ G) : H ⋙ F ⟶ F' ⋙ K :=
  sorry

-- α♯ のメイトのメイトは α♯
theorem leftAdjointMate_rightAdjointMate {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'}
    {G' : D' ⥤ C'} {H : C' ⥤ C} {K : D' ⥤ D} (σ : F ⊣ G) (τ : F' ⊣ G')
    (α : H ⋙ F ⟶ F' ⋙ K) : leftAdjointMate σ τ (rightAdjointMate σ τ α) = α :=
  sorry

-- α♭ のメイトのメイトは α♭
theorem rightAdjointMate_leftAdjointMate {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'}
    {G' : D' ⥤ C'} {H : C' ⥤ C} {K : D' ⥤ D} (σ : F ⊣ G) (τ : F' ⊣ G')
    (β : G' ⋙ H ⟶ K ⋙ G) : rightAdjointMate σ τ (leftAdjointMate σ τ β) = β :=
  sorry

end

#check conjugateEquiv

-- 共役。α♯ : F ⇒ F′ と α♭ : G′ ⇒ G の全単射
def conjugateEquiv' {F F' : C ⥤ D} {G G' : D ⥤ C} (σ : F ⊣ G) (τ : F' ⊣ G') :
    (F ⟶ F') ≃ (G' ⟶ G) :=
  sorry

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
-- hom 集合の間の自然な全単射を使って、命題4.3.7 の前半 F_∗ ⊣ G_∗ を証明せよ。宣言は
-- 命題4.3.7 のセクションの `whiskerRightAdjunction` である。

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

-- α♯ の共役が同型 ⇔ α♯ が同型
theorem isIso_conjugateEquiv_iff {F F' : C ⥤ D} {G G' : D ⥤ C} (σ : F ⊣ G) (τ : F' ⊣ G')
    (α : F ⟶ F') : IsIso (conjugateEquiv τ σ α) ↔ IsIso α :=
  sorry

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
