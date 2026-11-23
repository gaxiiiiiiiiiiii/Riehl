import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Category.Pointed

/-!
# 4.4 反変随伴関手と多変数随伴関手

節の数学的な内容は同名の HTML にある。

載せない例と Remark: 節冒頭の引用、節の導入の双対性（Mathlib の `Adjunction.op`・`Adjunction.unop`）、
反単調ガロア接続の記述、例4.4.2（零点集合と消える多項式。
`MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection`）、例4.4.3（構文と意味論の間のガロア接続）、
例4.4.8（両側加群のテンソル積）、例4.4.9（集合の積と写像の集合。`Types.tensorProductAdjunction`）、
Fin と Cat がデカルト閉であることの記述、例4.4.14（空間の便利な圏）、例4.4.15（テンソル積と hom）、
例4.4.18（ループ空間と懸垂）、閉モノイダル圏と n 変数随伴の記述、脚注10〜12 は載せない。
-/

open CategoryTheory Functor Opposite Limits

namespace Riehl

universe v u₁ u₂ u₃

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義4.4.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
一対の反変関手 F : Cᵒᵖ → D と G : Dᵒᵖ → C は、c ∈ C と d ∈ D について自然な同型
Hom(Fc, d) ≅ Hom(Gd, c) が存在するとき互いに左随伴であるといい、c ∈ C と d ∈ D について自然な同型
Hom(d, Fc) ≅ Hom(c, Gd) が存在するとき互いに右随伴であるという。

自然性は、定義4.1.1 と同じく、変数ごとの射の等式で書く。

Mathlib はこの 2 つの概念を通常の随伴で書く。互いに左随伴は `F ⊣ G.rightOp`、互いに右随伴は
`F.rightOp ⊣ G` である。

statement の項 := 本の記法
  F.obj (op c)    := Fc
  G.rightOp       := d ↦ Gd : D → Cᵒᵖ
  F.rightOp       := c ↦ Fc : C → Dᵒᵖ
-/

section

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

-- 互いに左随伴 : c, d について自然な全単射 Hom(Fc, d) ≅ Hom(Gd, c)
structure MutualLeftAdjoint (F : Cᵒᵖ ⥤ D) (G : Dᵒᵖ ⥤ C) where
  homEquiv : ∀ c d, (F.obj (op c) ⟶ d) ≃ (G.obj (op d) ⟶ c)
  homEquiv_naturality_left : ∀ {c c' d} (h : c ⟶ c') (f : F.obj (op c) ⟶ d),
    homEquiv c' d (F.map h.op ≫ f) = homEquiv c d f ≫ h
  homEquiv_naturality_right : ∀ {c d d'} (f : F.obj (op c) ⟶ d) (k : d ⟶ d'),
    homEquiv c d' (f ≫ k) = G.map k.op ≫ homEquiv c d f

-- 互いに右随伴 : c, d について自然な全単射 Hom(d, Fc) ≅ Hom(c, Gd)
structure MutualRightAdjoint (F : Cᵒᵖ ⥤ D) (G : Dᵒᵖ ⥤ C) where
  homEquiv : ∀ c d, (d ⟶ F.obj (op c)) ≃ (c ⟶ G.obj (op d))
  homEquiv_naturality_left : ∀ {c' c d} (h : c' ⟶ c) (f : d ⟶ F.obj (op c)),
    homEquiv c' d (f ≫ F.map h.op) = h ≫ homEquiv c d f
  homEquiv_naturality_right : ∀ {c d d'} (k : d' ⟶ d) (f : d ⟶ F.obj (op c)),
    homEquiv c d' (k ≫ f) = homEquiv c d f ≫ G.map k.op

variable {F : Cᵒᵖ ⥤ D} {G : Dᵒᵖ ⥤ C}

#check Functor.rightOp

-- 互いに左随伴な対から、随伴 F ⊣ (d ↦ Gd)
def adjunctionRightOpOfMutualLeftAdjoint (σ : MutualLeftAdjoint F G) : F ⊣ G.rightOp :=
  sorry

-- 随伴 F ⊣ (d ↦ Gd) から、互いに左随伴な対
def mutualLeftAdjointOfAdjunctionRightOp (σ : F ⊣ G.rightOp) : MutualLeftAdjoint F G :=
  sorry

-- 互いに右随伴な対から、随伴 (c ↦ Fc) ⊣ G
def rightOpAdjunctionOfMutualRightAdjoint (σ : MutualRightAdjoint F G) : F.rightOp ⊣ G :=
  sorry

-- 随伴 (c ↦ Fc) ⊣ G から、互いに右随伴な対
def mutualRightAdjointOfRightOpAdjunction (σ : F.rightOp ⊣ G) : MutualRightAdjoint F G :=
  sorry

end

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.4.4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
関手 F : A → B について、各 b ∈ B に対して対象 Gb ∈ A と、a ∈ A について自然な同型

  Hom(Fa, b) ≅ Hom(a, Gb)        (4.4.5)

が与えられたとき、対応 G : ob B → ob A を関手 G : B → A に拡張して、同型の族 (4.4.5) が b ∈ B に
ついても自然になるようにする方法が、ただ 1 つ存在する。このとき (4.4.5) は随伴 F ⊣ G をなす。

仮定の a についての自然性は、射 h : a′ → a と f : Fa → b についての等式で書く。一意性は、(4.4.5) を
b について自然にする射の対応 b → b′ ↦ Gb → Gb′ が 1 つに限ることとして書く。
-/

section

variable {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B]

variable {F : A ⥤ B} {G : B → A}

#check Adjunction.rightAdjointOfEquiv

-- 対応 G : ob B → ob A を拡張した関手 G : B → A
def rightAdjointOfEquiv' (e : ∀ a b, (F.obj a ⟶ b) ≃ (a ⟶ G b))
    (he : ∀ {a' a b} (h : a' ⟶ a) (f : F.obj a ⟶ b), e a' b (F.map h ≫ f) = h ≫ e a b f) :
    B ⥤ A where
  obj := G
  map := sorry
  map_id := sorry
  map_comp := sorry

#check Adjunction.adjunctionOfEquivRight

-- (4.4.5) のなす随伴 F ⊣ G
def coreHomEquivOfEquivRight (e : ∀ a b, (F.obj a ⟶ b) ≃ (a ⟶ G b))
    (he : ∀ {a' a b} (h : a' ⟶ a) (f : F.obj a ⟶ b), e a' b (F.map h ≫ f) = h ≫ e a b f) :
    Adjunction.CoreHomEquiv F (rightAdjointOfEquiv' e he) where
  homEquiv := e
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

-- (4.4.5) を b について自然にする射の対応は f ↦ Gf に限る
theorem eq_rightAdjointOfEquiv_map (e : ∀ a b, (F.obj a ⟶ b) ≃ (a ⟶ G b))
    (he : ∀ {a' a b} (h : a' ⟶ a) (f : F.obj a ⟶ b), e a' b (F.map h ≫ f) = h ≫ e a b f)
    (γ : ∀ {b b' : B}, (b ⟶ b') → (G b ⟶ G b'))
    (hγ : ∀ {a b b'} (f : F.obj a ⟶ b) (k : b ⟶ b'), e a b' (f ≫ k) = e a b f ≫ γ k)
    {b b' : B} (k : b ⟶ b') : γ k = (rightAdjointOfEquiv' e he).map k :=
  sorry

/-
双対の主張は、関手 G : B → A について、各 a ∈ A に対して対象 Fa ∈ B と、b ∈ B について自然な同型
Hom(Fa, b) ≅ Hom(a, Gb) が与えられたとき、対応 F : ob A → ob B が G の左随伴に一意に拡張される
ことである。Mathlib の次の 2 つで済むので宣言を置かない。
-/

#check Adjunction.leftAdjointOfEquiv
#check Adjunction.adjunctionOfEquivLeft

end

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.4.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
双関手 F : A × B → C について、次が成り立つ。
(i) 各 a ∈ A について関手 F(a, −) : B → C が右随伴 G_a : C → B を持つならば、G(a, −) ≔ G_a を
    満たし、同型 Hom(F(a, b), c) ≅ Hom(b, G(a, c)) が 3 つの変数すべてについて自然であるような
    双関手 G : Aᵒᵖ × C → B が、ただ 1 つ存在する。
(ii) 各 b ∈ B について関手 F(−, b) : A → C が右随伴 H_b : C → A を持つならば、H(b, −) ≔ H_b を
    満たし、同型 Hom(F(a, b), c) ≅ Hom(a, H(b, c)) が 3 つの変数すべてについて自然であるような
    双関手 H : Bᵒᵖ × C → A が、ただ 1 つ存在する。
(iii) (i) と (ii) の仮定がどちらも成り立つとき、各 c ∈ C について、関手 G(−, c) : Aᵒᵖ → B と
    H(−, c) : Bᵒᵖ → A は互いに右随伴である。

双関手は、積圏からの関手 A × B → C でなく、関手圏への関手 A → C^B で書く。Mathlib の 2 変数の
随伴がこの形を使う。b と c についての自然性は、a ごとの同型が随伴 F(a, −) ⊣ G_a の同型である
ことに含まれるので、宣言にするのは a についての自然性である。一意性は、同型を a について自然に
する自然変換の対応 a → a′ ↦ G_{a′} ⇒ G_a が 1 つに限ることとして書く。

(ii) は、(i) を F の 2 つの変数を入れ替えた双関手に当てはめたものなので、宣言を置かない。

statement の項 := 本の記法
  F.obj a                         := F(a, −)
  F.flip.obj b                    := F(−, b)
  (rightAdjoint₂ σ).flip.obj c    := G(−, c)
  (rightAdjoint₂ τ).flip.obj c    := H(−, c)
-/

section

variable {A : Type u₁} [Category.{v} A] {B : Type u₂} [Category.{v} B]
  {C : Type u₃} [Category.{v} C]

variable {F : A ⥤ B ⥤ C} {G : A → C ⥤ B}

-- G(a, −) ≔ G_a を満たす双関手 G : Aᵒᵖ × C → B
def rightAdjoint₂ (σ : ∀ a, F.obj a ⊣ G a) : Aᵒᵖ ⥤ C ⥤ B where
  obj a := G (unop a)
  map := sorry
  map_id := sorry
  map_comp := sorry

-- 同型 Hom(F(a, b), c) ≅ Hom(b, G(a, c)) は a について自然
theorem homEquiv_naturality_rightAdjoint₂_map (σ : ∀ a, F.obj a ⊣ G a) {a a' : A} (f : a ⟶ a')
    {b : B} {c : C} (g : (F.obj a').obj b ⟶ c) :
    (σ a).homEquiv b c ((F.map f).app b ≫ g) =
      (σ a').homEquiv b c g ≫ ((rightAdjoint₂ σ).map f.op).app c :=
  sorry

-- 同型を a について自然にする自然変換の対応は f ↦ G(f, −) に限る
theorem eq_rightAdjoint₂_map (σ : ∀ a, F.obj a ⊣ G a)
    (γ : ∀ {a a' : A}, (a ⟶ a') → (G a' ⟶ G a))
    (hγ : ∀ {a a' : A} (f : a ⟶ a') {b : B} {c : C} (g : (F.obj a').obj b ⟶ c),
      (σ a).homEquiv b c ((F.map f).app b ≫ g) = (σ a').homEquiv b c g ≫ (γ f).app c)
    {a a' : A} (f : a ⟶ a') : γ f = (rightAdjoint₂ σ).map f.op :=
  sorry

-- G(−, c) と H(−, c) は互いに右随伴
def flipObjRightOpAdjunction {H : B → C ⥤ A} (σ : ∀ a, F.obj a ⊣ G a)
    (τ : ∀ b, F.flip.obj b ⊣ H b) (c : C) :
    ((rightAdjoint₂ σ).flip.obj c).rightOp ⊣ (rightAdjoint₂ τ).flip.obj c :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義4.4.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
2 変数随伴とは、3 つの双関手 F : A × B → C, G : Aᵒᵖ × C → B, H : Bᵒᵖ × C → A に、a ∈ A, b ∈ B,
c ∈ C について自然な同型 Hom(F(a, b), c) ≅ Hom(b, G(a, c)) ≅ Hom(a, H(b, c)) を添えたものである。
F がモノイダル積であるとき、G を F の左閉包、H を F の右閉包という。両方の閉包が存在する F を
双閉といい、F : C × C → C が双閉で 2 つの引数について自然に対称であるとき、F は閉であるという。

Mathlib の `F ⊣₂ G` は、F と G だけについての構造 `ParametrizedAdjunction F G` の記法である。
これは a ごとの随伴 F(a, −) ⊣ G(a, −) の族で、同型 Hom(F(a, b), c) ≅ Hom(b, G(a, c)) が a に
ついても自然なものである。2 変数随伴は `F ⊣₂ G` と `F.flip ⊣₂ H` の組で書く。

`ParametrizedAdjunction` は、a についての自然性を随伴の単位の等式で持つ。同型の等式から単位の
等式を得るのが `ParametrizedAdjunction.mk'` で、逆が
`ParametrizedAdjunction.homEquiv_naturality_one` である。
-/

#print ParametrizedAdjunction
#check ParametrizedAdjunction.mk'
#check ParametrizedAdjunction.homEquiv_naturality_one

-- 2 変数随伴
structure TwoVariableAdjunction (F : A ⥤ B ⥤ C) (G : Aᵒᵖ ⥤ C ⥤ B) (H : Bᵒᵖ ⥤ C ⥤ A) where
  -- Hom(F(a, b), c) ≅ Hom(b, G(a, c))
  adj₁ : F ⊣₂ G
  -- Hom(F(a, b), c) ≅ Hom(a, H(b, c))
  adj₂ : F.flip ⊣₂ H

-- 変数ごとの右随伴を持つ双関手から命題4.4.6 によって得られる 2 変数随伴
def twoVariableAdjunctionOfRightAdjoints {H : B → C ⥤ A} (σ : ∀ a, F.obj a ⊣ G a)
    (τ : ∀ b, F.flip.obj b ⊣ H b) :
    TwoVariableAdjunction F (rightAdjoint₂ σ) (rightAdjoint₂ τ) :=
  sorry

end

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義4.4.10
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
デカルト閉圏とは、有限積を持つ圏 C であって、積の双関手 − × − : C × C → C が閉であるものをいう。

積の双関手は 2 つの引数について自然に対称なので、閉であることは双閉であること、すなわち
2 変数随伴の F であることである。

Mathlib は、デカルト閉圏を、積をテンソル積とするモノイダル圏 `CartesianMonoidalCategory C` が
`MonoidalClosed C` であることとして書く。

statement の項 := 本の記法
  prod.functor    := − × − : C × C → C
-/

#check prod.functor

-- デカルト閉圏
structure CartesianClosed (C : Type u₁) [Category.{v} C] [HasFiniteProducts C] where
  leftClosure : Cᵒᵖ ⥤ C ⥤ C
  rightClosure : Cᵒᵖ ⥤ C ⥤ C
  adj : TwoVariableAdjunction prod.functor leftClosure rightClosure

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題4.4.11
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の小圏 C について、関手圏 Set^C はデカルト閉である。

本文の証明は、関手 F, G : C → Set に対して関手 G^F : C → Set を

  G^F(c) ≔ {Hom(c, −) × F ⇒ G}        (4.4.13)

で定義し、自然変換 ev : G^F × F ⇒ G を定義して、β : H ⇒ G^F を ev ⋅ (β × F) : H × F ⇒ G に
送る写像が全単射

  {H × F ⇒ G} ≅ {H ⇒ G^F}        (4.4.12)

であることを示す。

関手 H, F : C → Set の積 H × F は、対象ごとの積 c ↦ Hc × Fc で書く。Mathlib の
`FunctorToTypes.prod H F` である。Mathlib は G^F を `F.functorHom G` と書き、(4.4.12) を
`FunctorToTypes.functorHomEquiv` に持つ。

`FunctorToTypes.prod.fst` と `FunctorToTypes.prod.snd` は積 H × F の 2 つの射影で、
`FunctorToTypes.prod.lift` は自然変換の対 K ⇒ H, K ⇒ F から K ⇒ H × F を得る。

statement の項 := 本の記法
  FunctorToTypes.prod H F    := H × F
  FunctorToTypes.prod.lift (FunctorToTypes.prod.fst ≫ β) FunctorToTypes.prod.snd
                             := β × F : H × F ⇒ G^F × F
-/

section

variable {C : Type v} [SmallCategory C]

#check FunctorToTypes.prod
#check Functor.functorHom

-- G^F : c ↦ {Hom(c, −) × F ⇒ G}
def functorExp (F G : C ⥤ Type v) : C ⥤ Type v :=
  sorry

-- ev : G^F × F ⇒ G
def functorExpEv (F G : C ⥤ Type v) : FunctorToTypes.prod (functorExp F G) F ⟶ G :=
  sorry

#check FunctorToTypes.functorHomEquiv

-- (4.4.12) の全単射 {H × F ⇒ G} ≅ {H ⇒ G^F}
def functorExpHomEquiv (F G H : C ⥤ Type v) :
    (FunctorToTypes.prod H F ⟶ G) ≃ (H ⟶ functorExp F G) :=
  sorry

#check @FunctorToTypes.prod.fst
#check @FunctorToTypes.prod.snd
#check @FunctorToTypes.prod.lift

-- β : H ⇒ G^F の転置は ev ⋅ (β × F)
theorem functorExpHomEquiv_symm_apply (F G H : C ⥤ Type v) (β : H ⟶ functorExp F G) :
    (functorExpHomEquiv F G H).symm β =
      FunctorToTypes.prod.lift (FunctorToTypes.prod.fst ≫ β) FunctorToTypes.prod.snd ≫
        functorExpEv F G :=
  sorry

#check FunctorToTypes.monoidalClosed

-- Set^C はデカルト閉
def cartesianClosedFunctorToType : CartesianClosed (C ⥤ Type v) :=
  sorry

end

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.4.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義4.2.5 を双対化して、互いに左随伴な対と互いに右随伴な対を、自然変換を備えた反変関手の
-- 対として定義する問題で、statement を書くことが解答になるので宣言を置かない。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.4.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題4.4.6 を証明せよ。宣言は命題4.4.6 のセクションの `rightAdjoint₂`、
-- `homEquiv_naturality_rightAdjoint₂_map`、`eq_rightAdjoint₂_map`、`flipObjRightOpAdjunction`
-- である。

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.4.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
反変冪集合関手 P : Setᵒᵖ → Set は、自分自身と互いに右随伴である。

P は例1.3.7(i) の関手で、集合 X を X の部分集合の集合に送り、写像 f を f による逆像に送る。

問題の後半（例2.1.6(i) を使って他の圏についての同様の例を見つけよ）は、どの例を選ぶかが解答に
含まれるので宣言を置かない。
-/

-- 反変冪集合関手 P : Setᵒᵖ → Set
def powersetOp : (Type u₁)ᵒᵖ ⥤ Type u₁ :=
  sorry

-- P は自分自身と互いに右随伴
def powersetOpRightOpAdjunction : powersetOp.{u₁}.rightOp ⊣ powersetOp :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.4.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
(i) 双関手 Hom_∗ : Set_∗ᵒᵖ × Set_∗ → Set_∗ は、各 (X, x) ∈ Set_∗ について Hom_∗((X, x), −) が
左随伴を持ち、その左随伴を束ねた双関手 ∧ : Set_∗ × Set_∗ → Set_∗ とともに 2 変数随伴をなす。

Hom_∗((X, x), (Y, y)) は基点を保つ写像 (X, x) → (Y, y) の集合で、y に値を取る定値写像を基点と
する。Set_∗ は Mathlib の `Pointed` である。

(ii)（∧ が演習3.6.iii(iii) のスマッシュ積と同型であること）は、演習3.6.iii に宣言を置いていない
ので宣言を置かない。最後の問い（例4.4.18 の設定での同様の 2 変数随伴）は、便利な圏を宣言にして
いないので宣言を置かない。
-/

#check Pointed

-- Hom_∗ : Set_∗ᵒᵖ × Set_∗ → Set_∗
def pointedHom : Pointed.{u₁}ᵒᵖ ⥤ Pointed.{u₁} ⥤ Pointed.{u₁} :=
  sorry

-- ∧ : Set_∗ × Set_∗ → Set_∗
def pointedSmash : Pointed.{u₁} ⥤ Pointed.{u₁} ⥤ Pointed.{u₁} :=
  sorry

-- ∧ と Hom_∗ のなす 2 変数随伴
def pointedSmashHomAdjunction : TwoVariableAdjunction pointedSmash.{u₁} pointedHom pointedHom :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習4.4.v
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 加群の圏と鎖複体の圏の hom の双関手について変数ごとの随伴を定義する問題で、どの双関手を
-- 左随伴に取るかが解答に含まれるので宣言を置かない。

end Riehl
