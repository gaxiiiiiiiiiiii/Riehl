import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Fin
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Limits.Elements
import Mathlib.CategoryTheory.Limits.Types.Limits


/-!
# 3.1 普遍錐としての極限と余極限

節の数学的な内容は本文 §3.1 にある。このファイルは本の主張を出現順に並べたもので、主張と
定理群の構成は各セクションの冒頭に、形式化の判断は下の表に、Mathlib の対応物は各
statement の直前の `#check` にある。

形式化の判断:
  universe     添字圏 J と圏 C の universe は独立に取る（`J : Type u₂`・`C : Type u₁`）。
               本の脚注1（J が小さく C が局所小）は「錐の全体が集合をなす」ための仮定だが、
               Mathlib は錐の型を `Type (max u₂ v₁)` に置き、`RepresentableBy` が universe の
               異なる型どうしの全単射を許すので、この仮定なしで述べられる
  定義3.1.2    本は錐を自然変換 Δc ⇒ F と定義し、続けて「脚の族で、各三角形が可換なもの」と
               言い換える。Mathlib の `Cone` は前者（`pt` と `π : (const J).obj pt ⟶ F`）。
               後者を `MyCone` として自前で置き、両者の全単射を演習にする。余錐も同様
  極限の3つの  本は極限を「Cone(−,F) の表現」（定義3.1.5）と「錐の圏の終対象」（定義3.1.6）
  持ち方       の2通りで定義する。Mathlib の `IsLimit` はそのどちらでもなく、「どの錐からも
               一意な錐の射がある」ことを `lift`・`fac`・`uniq` で直接持つ。本の2つの定義は
               それぞれ `IsLimit` との往復として演習に置く。以降の statement は `IsLimit` で
               述べる
  定義3.1.5    表現は 2.1 と同じ `Functor.RepresentableBy` で持つ。Cone(−,F) は Mathlib の
               `Functor.cones`。表現から極限錐を取り出す `myLimitCone`（𝟙 に対応する錐。
               2.3 の普遍要素にあたる）は定義の写しなので data を書いて渡す
  定義3.1.5 の 本は「λ が同型 C(−, lim F) ≅ Cone(−,F) を定める」と述べるだけで、この同型の
  補足         成分についての主張は本にない。`IsLimit` の `lift`・`fac`・`uniq` が同型のどの部分に
               あたるかを追えるよう、同型を `IsLimit.homEquiv` で持ち、逆方向についての3つを
               演習にした。順方向が f ↦ λ·Δf であることは定義を展開するだけなので置かない。
               脚と両立する射の一意性に対応する Mathlib の宣言はない
  定義3.1.6    錐の圏は Mathlib の `Cone.category`（射は `ConeMorphism`）を使い、終対象は
               `IsTerminal t`（`t : Cone F`）で述べる
  命題3.1.7 と 本は命題3.1.7 を錐の圏の終対象と補題1.6.16 から出し、演習3.1.ii で普遍性から
  演習3.1.ii   直接示せと言う。この違いを statement に写し、3.1.7 は錐の圏の終対象
               （`IsTerminal`）について、3.1.ii は `IsLimit` について述べる
  図式の形     等化子・引き戻し・逆極限と定義3.1.23 の双対は、添字圏と図式を自前で組み、その上の
               錐と極限錐として定義する。平行対の圏は対象と射を inductive で、余スパンとスパンは
               3点の半順序集合として置く（本の「poset category」）。ωᵒᵖ と ω は第1章の ℕ の順序
               による圏を使う。図式の対象への値は書いて渡し、射への値と関手則を `sorry` にする。
               この節の主張は自前の定義で述べる。Mathlib の `Fork`・`PullbackCone` なども同じ錐
               だが、添字圏が読者の組んだものとは別の型になるため。節末問題は Mathlib の語彙で
               述べる。本が「錐とはこのデータのことである」と言い換える部分を `Cone ... ≃ Σ ...`
               として置く（対応する Mathlib の宣言はない）。普遍性は `Nonempty (IsLimit t) ↔ ∃! ...`
               として置く。`IsLimit` はデータなので、命題にするには `Nonempty` で包む
  HasLimit     Mathlib は極限の存在を `HasLimit F`（Prop）、選ばれた極限対象を `limit F` で持つ。
               本の lim F はこの `limit F` にあたる。本節の statement は個々の錐について述べるので
               `HasLimit` は注意3.1.27 の `HasProduct`・`HasCoproduct` にしか現れない
  定義3.1.23   双対は定義と普遍性の形だけを置き、錐の言い換えは置かない。余積は定義3.1.9 の
               `MyFan` の双対、余等化子の添字圏は定義3.1.13 の平行対の圏を使う
  注意3.1.27   余積から積への射を成分の行列で与える全単射を置く。直和と行列の積は加法圏の話
               なので載せない。Mathlib は双積について `biproduct.matrix` を持つ
  演習3.1.i    前順序集合は `Preorder.smallCategory` で圏とみなす。極限は `IsGLB`、余極限は
               `IsLUB` で述べる。Mathlib は完備束について `CompleteLattice.limit_eq_iInf` を持つ
  演習3.1.iii  本の「コンマ圏 Δ ↓ F（F : 𝟙 → C^J）」は Mathlib の `CostructuredArrow (const J) F`
               （定義は `Comma S (Functor.fromPUnit T)`）そのもの。本は「同型」と言うが Mathlib の
               対応物が `≌` なので `≌` で述べる（2.4 と同じ扱い）
  演習3.1.vii  始対象を頂点とする錐は定義の写しなので data を書き、自然性だけ `sorry` にする。
               後半の「後続順序数で添字づけられた図式の余極限」は、`Fin (n + 1)` の `Fin.last n`
               が終対象であることに帰着するので、その形で置く
  演習3.1.ix   本の仮定どおり零対象で述べる。Mathlib の `isSplitMono_sigma_ι` は零射だけを仮定
               しており、本の「他の文脈に拡張できるか」の答えにあたる
  演習3.1.x    圏の圏 `Cat` の対象は `Cat.of C`、射は関手を `Functor.toCatHom` で包んだもの。
               Mathlib は `Cat` の極限を一般に構成する（`Cat.HasLimits.limitConeIsLimit`）だけで、
               `C × D` が二項積であるという宣言は持たない。族の積は本が定義を求めているので
               `MyPi` として自前で置く。Mathlib の `∀ i, C i` の圏構造と衝突しないよう型の別名にする
  演習3.1.xii  `Cone.whisker` は錐の脚を E で添字づけ直したもの（頂点は同じ）

statement を置かない節末問題:
  3.1.viii  ℤ 上の具体的な計算で、答えが (−a, −b) という組そのもの。後半は説明問題
  3.1.xi    群・アーベル群・可換環の余積を答える問題で、対象の記述が答えになる。Mathlib では
            可換環の余積が `CommRingCat.coproductCocone`（テンソル積）、群の自由積が
            `Monoid.Coprod`、加群の余積が `ModuleCat.coprodIsoDirectSum`

本文中の例（例3.1.10・3.1.12・3.1.14・3.1.18・3.1.19・3.1.22・3.1.24・3.1.25・3.1.26）と
注意3.1.8、引き戻しによるファイバーの定義 (3.1.17) は載せない。注意3.1.8 の J◁・J▷ は Mathlib の
`WithInitial J`・`WithTerminal J`。

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Functor/Const.lean`（`Functor.const`）
  - `Mathlib/CategoryTheory/Limits/Cones.lean`（`Cone`・`Cocone`・`ConeMorphism`・
    `Functor.cones`・`Functor.cocones`・`Cone.whiskeringEquivalence`）
  - `Mathlib/CategoryTheory/Limits/IsLimit.lean`（`IsLimit`・`IsColimit`・`hom_ext`・
    `conePointUniqueUpToIso`・`representableBy`・`ofRepresentableBy`）
  - `Mathlib/CategoryTheory/Limits/ConeCategory.lean`（`Cone.isLimitEquivIsTerminal`・
    `Cone.equivCostructuredArrow`）
  - `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean`（`IsTerminal`・`isTerminalEquivUnique`・
    `limitOfDiagramInitial`）
  - `Mathlib/CategoryTheory/Limits/Shapes/Products.lean`（`Fan`・`Pi.lift`・`Sigma.desc`）
  - `Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean`（`Fork`・`Fork.IsLimit.mk'`・
    `mono_of_isLimit_fork`）
  - `Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean`（`PullbackCone`・
    `PullbackCone.IsLimit.mk`）
  - `Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean`（`IsPullback`・
    `IsPullback.paste_horiz_iff`）
  - `Mathlib/CategoryTheory/Functor/OfSequence.lean`（`Functor.ofSequence`・`Functor.ofOpSequence`）
  - `Mathlib/CategoryTheory/Limits/Lattice.lean`（`CompleteLattice.limit_eq_iInf`）
-/

open CategoryTheory Limits Opposite

universe v₁ v₂ u₁ u₂

-- variable {J : Type u₁} [Category.{v₂} J] {C : Type u₁} [Category.{v₁} C]
variable {C : Type u₁} [Category.{v₁, u₁} C] {J : Type v₁} [Category.{v₂, v₁} J]
variable (F : J ⥤ C)

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  前提: 演習が使う Mathlib の定義
-- ╚═════════════════════════════════════════════════════════════════════════

namespace Recap

variable {J : Type u₂} [Category.{v₂} J] {C : Type u₁} [Category.{v₁} C]

-- 定義3.1.1 の定数図式関手 Δ : C → C^J
@[simps, implicit_reducible]
def const (J : Type u₂) [Category.{v₂} J] : C ⥤ J ⥤ C where
  obj X :=
    { obj := fun _ => X
      map := fun _ => 𝟙 X }
  map f := { app := fun _ => f }

-- 定義3.1.2 の錐。頂点と、定数関手からの自然変換
structure Cone (F : J ⥤ C) where
  pt : C
  π : (const J).obj pt ⟶ F

-- 定義3.1.2 の余錐。底と、定数関手への自然変換
structure Cocone (F : J ⥤ C) where
  pt : C
  ι : F ⟶ (const J).obj pt

-- 定義3.1.5 の Cone(−,F) : Cᵒᵖ → Set。Mathlib は Δ の反対と米田の合成で持つ
def Functor.cones (F : J ⥤ C) : Cᵒᵖ ⥤ Type (max u₂ v₁) :=
  (const J).op ⋙ yoneda.obj F

-- 定義3.1.5 の Cone(F,−) : C → Set
def Functor.cocones (F : J ⥤ C) : C ⥤ Type (max u₂ v₁) :=
  const J ⋙ coyoneda.obj (op F)

-- 定義3.1.6 の錐の射。頂点の射で、各脚と両立するもの
structure ConeMorphism {F : J ⥤ C} (A B : Cone F) where
  hom : A.pt ⟶ B.pt
  w (j : J) : hom ≫ B.π.app j = A.π.app j := by cat_disch

attribute [reassoc (attr := simp)] ConeMorphism.w

-- 定義3.1.6 の錐の圏。Mathlib はこの instance で `Cone F` を圏にする
instance Cone.category {F : J ⥤ C} : Category (Cone F) where
  Hom A B := ConeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

-- Mathlib の極限錐。本の2つの定義（表現・終対象）のどちらでもなく、
-- 「どの錐からも錐の射がただ一つある」ことを直接持つ
structure IsLimit {F : J ⥤ C} (t : Cone F) where
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j
  uniq : ∀ (s : Cone F) (m : s.pt ⟶ t.pt), (∀ j : J, m ≫ t.π.app j = s.π.app j) → m = lift s

structure IsColimit {F : J ⥤ C} (t : Cocone F) where
  desc : ∀ s : Cocone F, t.pt ⟶ s.pt
  fac : ∀ (s : Cocone F) (j : J), t.ι.app j ≫ desc s = s.ι.app j
  uniq : ∀ (s : Cocone F) (m : t.pt ⟶ s.pt), (∀ j : J, t.ι.app j ≫ m = s.ι.app j) → m = desc s

-- 定義3.1.11 の伏線。Mathlib は終対象を「空図式の極限」として定義する
def asEmptyCone (X : C) : Cone (Functor.empty.{0} C) where
  pt := X
  π := { app := fun ⟨j⟩ => j.elim }

abbrev IsTerminal (X : C) := IsLimit (asEmptyCone X)

end Recap



-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
対象 c に対し、定数関手 Δc : J → C はすべての対象を c に、すべての射を id_c に送る。
定数図式関手 Δ : C → C^J は c を Δc に、射 f : c → c' を各成分が f である自然変換 Δf に送る。

構成: 定数関手と定数図式関手を順に組む。
-/

#check @CategoryTheory.Functor.const

def myConstObj (J : Type u₂) [Category.{v₂} J] (c : C) : J ⥤ C where
  obj i := c
  map g := 𝟙 c


def myConst (J : Type u₂) [Category.{v₂} J] : C ⥤ J ⥤ C where
  obj c := myConstObj _ c
  map {c c'} f := {
    app i := f
    naturality {i j} f := by
      simp [myConstObj]
  }
  map_id X := by ext; simp [myConstObj]
  map_comp {X Y Z} f g := by
    ext i; rfl



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
図式 F : J → C の上の錐（頂点 c）とは自然変換 λ : Δc ⇒ F のことで、成分 λ_j : c → Fj を脚と
いう。言い換えると、脚の族 (λ_j) が錐をなすのは、J の各射 f : j → k について三角形
Ff ∘ λ_j = λ_k が可換なとき、かつそのときに限る。双対に、F の下の錐（底 c）は自然変換
F ⇒ Δc で、条件は λ_k ∘ Ff = λ_j。F の下の錐は F : Jᵒᵖ → Cᵒᵖ の上の錐にほかならない。

構成: 「脚と三角形」による定義を自前で置き、Mathlib の自然変換による定義との全単射を
上と下それぞれで示す。最後に、下の錐と反対圏での上の錐との対応を述べる。
-/

-- 本の言い換え: 脚の族と三角形の可換性
structure MyCone where
  summit : C
  leg (j : J) : summit ⟶ F.obj j
  w {j k : J} (f : j ⟶ k) : leg j ≫ F.map f = leg k

structure MyCocone where
  nadir : C
  leg (j : J) : F.obj j ⟶ nadir
  w {j k : J} (f : j ⟶ k) : F.map f ≫ leg k = leg j

#check @CategoryTheory.Limits.Cone.w

def def_3_1_2_cone : MyCone F ≃ Cone F := sorry

#check @CategoryTheory.Limits.Cocone.w

def def_3_1_2_cocone : MyCocone F ≃ Cocone F := sorry

#check @CategoryTheory.Limits.coconeEquivalenceOpConeOp

def def_3_1_2_op : Cocone F ≌ (Cone F.op)ᵒᵖ := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.5（極限と余極限 I）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
図式 F : J → C に対し、関手 Cone(−,F) := Hom(Δ(−),F) : Cᵒᵖ → Set は c を頂点 c の錐の集合に
送り、f : c → d を脚の前合成 f^* に送る。F の極限とは Cone(−,F) の表現である。米田の補題に
より、極限は対象 lim F と普遍錐 λ : Δ lim F ⇒ F の組からなり、C(−, lim F) ≅ Cone(−,F) を
定める。双対に、Cone(F,−) := Hom(F,Δ(−)) : C → Set の表現が余極限である。

構成: 関手 Cone(−,F)・Cone(F,−) を組む。次に、Mathlib の極限錐から表現を作り、逆に表現から
極限錐（𝟙 に対応する錐）を取り出してそれが極限錐であることを示す。余極限も同様。
-/


#check @CategoryTheory.Functor.cones
def myCones : Cᵒᵖ ⥤ Type _ where
  obj c' := (Functor.const J).obj c'.unop ⟶ F
  map {c c'} f := by
    apply TypeCat.ofHom
    intro σ
    refine {
      app i := f.unop ≫ (σ.app i)
      naturality {i j} g := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
        rw [<- σ.naturality g]; simp
    }
  map_id x := by
    ext σ i; simp
  map_comp {x y z} f g := by
    ext σ i; simp


#check Limits.HasLimit
class myHasLimit where
  limit : C
  hasLimit : F.cones.RepresentableBy limit


def myLimitCone [myHasLimit F] : Cone F where
  pt := myHasLimit.limit F
  π := myHasLimit.hasLimit.homEquiv (𝟙 (myHasLimit.limit F))

-- 極限錐から表現を作る
#check @Limits.IsLimit.representableBy
def myRepresentableByOfIsLimit {F : J ⥤ C} {t : Cone F} (h : IsLimit t) :
    F.cones.RepresentableBy t.pt where
  homEquiv {X} := {
    toFun := fun f => (Functor.const J).map f ≫ t.π
    invFun := fun σ => h.lift ⟨X, σ⟩
    left_inv := by
      intro f; simp only [Functor.op_obj]
      symm
      apply h.uniq { pt := X, π := (Functor.const J).map f ≫ t.π }
      intro j; simp
    right_inv := by
      intro c; simp only [Functor.cones_obj, Functor.op_obj]
      ext i; simp
  }
  homEquiv_comp {x y} f g := by simp


-- 表現から取り出した錐が極限錐であること
#check @CategoryTheory.Limits.IsLimit.ofRepresentableBy
def myIsLimitOfRepresentableBy [HF : myHasLimit F] : IsLimit (myLimitCone F) where
  lift s := HF.hasLimit.homEquiv.symm s.π
  fac s j := by
    simp only [myLimitCone]
    set g :=  HF.hasLimit.homEquiv.symm s.π
    have E :=  HF.hasLimit.homEquiv_comp g (𝟙 _)
    simp only [Functor.cones_obj, Category.comp_id, Functor.cones_map, Quiver.Hom.unop_op,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk] at E
    conv at E => arg 1; simp [g]
    rw [E]; simp
  uniq s (m : s.pt ⟶ HF.limit) w := by
    apply HF.hasLimit.homEquiv.injective
    apply NatTrans.ext; ext j
    simp only [Functor.op_obj, Functor.const_obj_obj, Functor.cones_obj, Equiv.apply_symm_apply]
    rw [<- w j]
    simp only [myLimitCone, Functor.cones_obj]
    have Em := HF.hasLimit.homEquiv_comp m (𝟙 _)
    simp only [Functor.cones_obj, Category.comp_id, Functor.cones_map, Quiver.Hom.unop_op,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk] at Em
    rw [Em]; simp

-- HasLimit から普遍性（3.1.5 の自然同型）を取り出す
noncomputable def limitRepresentableBy [HasLimit F] : F.cones.RepresentableBy (limit F) :=
  (limit.isLimit F).representableBy

#check @CategoryTheory.Functor.representableByEquiv













#check @CategoryTheory.Functor.cocones
def myCocones : C ⥤ Type v₁ := sorry


#check Limits.HasColimit
class myHasColimit where
  colimit : C
  hasColimit : F.cocones.CorepresentableBy colimit


def myColimitCocone [myHasColimit F] : Cocone F := sorry

-- 余極限錐から表現を作る
#check @CategoryTheory.Limits.IsColimit.corepresentableBy

def myCorepresentableByOfIsColimit {F : J ⥤ C} {t : Cocone F} (h : IsColimit t) :
    F.cocones.CorepresentableBy t.pt := sorry

-- 表現から取り出した錐が余極限錐であること
#check @CategoryTheory.Limits.IsColimit.ofCorepresentableBy

def myIsColimitOfCorepresentableBy [myHasColimit F] :
    IsColimit (myColimitCocone F) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.5 の補足（極限錐が定める同型の成分）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
極限錐 λ : Δℓ ⇒ F が定める同型 C(−, ℓ) ≅ Cone(−,F) について、逆方向で錐から得た射は脚と
両立し、脚と両立する射は逆方向で得た射に限られ、逆方向は頂点の取り替え f^* と両立する。

構成: 逆方向と脚の両立、脚と両立する射の一意性、逆方向と f^* の両立を順に置く。
-/

noncomputable def yonedaLimitIso [HasLimit F] : yoneda.obj (limit F) ≅ F.cones :=
  Functor.representableByEquiv (limitRepresentableBy F)

example [HasLimit F] :
    (limit.isLimit F).homEquiv (𝟙 (limit F)) = (limit.cone F).π := by
  apply NatTrans.ext; ext j
  simp [IsLimit.homEquiv]

example [HasLimit F] (s : Cone F) :
   (limit.isLimit F).homEquiv.symm s.π = limit.lift F s := by
  simp [IsLimit.homEquiv]

#check IsLimit.homEquiv_symm_naturality
#print Cone.extend

#check @CategoryTheory.Limits.IsLimit.homEquiv
#check @CategoryTheory.Limits.IsLimit.homEquiv_symm_π_app

lemma homEquiv_symm_comp_π {t : Cone F} (h : IsLimit t) {W : C}
    (σ : (Functor.const J).obj W ⟶ F) (j : J) :
    h.homEquiv.symm σ ≫ t.π.app j = σ.app j := by
  have E := h.representableBy.homEquiv_comp (h.homEquiv.symm σ) (𝟙 _)
  have E' := NatTrans.congr_app E j
  conv at E' =>
    arg 1; arg 1; change h.homEquiv (h.homEquiv.symm σ ≫ 𝟙 t.pt);
    simp only [Category.comp_id,Equiv.apply_symm_apply]
  simp only [Functor.op_obj, Functor.const_obj_obj, Functor.cones_map, Quiver.Hom.unop_op,
    Functor.cones_obj, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, NatTrans.comp_app,
    Functor.const_map_app] at E'
  rw [E']; congr 1
  simp [IsLimit.representableBy]



lemma eq_homEquiv_symm_of_comp_π {t : Cone F} (h : IsLimit t) {W : C}
    (σ : (Functor.const J).obj W ⟶ F) (m : W ⟶ t.pt)
    (w : ∀ j, m ≫ t.π.app j = σ.app j) :
    m = h.homEquiv.symm σ := by
  apply h.homEquiv.injective
  simp only [IsLimit.homEquiv_apply, Cone.extend_π, Equiv.apply_symm_apply]
  apply NatTrans.ext; ext j
  simp only [Functor.const_obj_obj, NatTrans.comp_app, Functor.const_map_app]
  rw [w]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.6（極限と余極限 II）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
図式 F の極限とは、F の上の錐の圏 ∫Cone(−,F) の終対象である。錐の圏の対象は任意の頂点を
持つ錐、錐 λ : Δc ⇒ F から μ : Δd ⇒ F への射は、各 j について μ_j ∘ f = λ_j をみたす射
f : c → d である。双対に、余極限は F の下の錐の圏の始対象である。

構成: Mathlib の極限錐であることと、錐の圏（Recap の `Cone.category`）の終対象であることの
全単射を示す。余極限も同様。
-/



example :
  F.cones.Elements ≅ Cone F
where
  hom := ↾ fun c => ⟨c.fst.unop, c.snd⟩
  inv := ↾ fun c => ⟨op c.pt, c.π⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

example :
  CostructuredArrow (Functor.const J) F ≅ Cone F
where
  hom := ↾ fun c => ⟨c.left, c.hom⟩
  inv := ↾ fun c => ⟨c.pt, ⟨PUnit.unit⟩, c.π⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

example : HasLimit F ↔ HasTerminal (Cone F) where
  mp H := by
    apply @hasTerminal_of_unique _ _ (Limits.limit.cone F) ?_ ?_
    · intro s; constructor
      use limit.lift F s
      simp
    · intro s; constructor
      intro ⟨f, Hf⟩ ⟨g, Hg⟩; ext
      simp only [limit.cone_x, limit.cone_π] at Hf Hg ⊢
      apply limit.hom_ext; intro j
      rw [Hf, Hg]
  mpr H := by
    constructor; constructor
    use Limits.terminal (Cone F)
    refine {
      lift s := (Limits.terminal.from s).hom
      fac := by
        intro s i
        exact (Limits.terminal.from s).w i
      uniq s m w := by
        let m' : s ⟶ ⊤_ Cone F := ⟨m, w⟩
        have := Limits.terminal.hom_ext m' (terminal.from s)
        rw [<- this]
    }

example :
  F.cocones.Elements ≅ Cocone F
where
  hom := ↾ fun c => ⟨c.fst, c.snd⟩
  inv := ↾ fun c => ⟨c.pt, c.ι⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

example :
  StructuredArrow F (Functor.const J) ≅ Cocone F
where
  hom := ↾ fun c => ⟨c.right, c.hom⟩
  inv := ↾ fun c => ⟨⟨PUnit.unit⟩, c.pt, c.ι⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

example : HasColimit F ↔ HasInitial (Cocone F) := sorry




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.1.7（極限と余極限の本質的一意性）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
共通の図式 F の上の2つの極限錐 λ : Δℓ ⇒ F と λ' : Δℓ' ⇒ F に対し、脚と両立する同型
ℓ ≅ ℓ' がただ一つ存在する。また、極限錐 λ と両立する ℓ の自己同型は恒等射だけである。

構成: 本の証明にならい、錐の圏の終対象として述べる。錐の圏の同型が「脚と両立する頂点の
同型」であることは `ConeMorphism` の定義そのもの。続けて自己同型についての注意を、余極限に
ついての双対を置く。
-/

#check IsLimit.uniqueUpToIso

def LimitConeIso (s t : LimitCone F) :
  s.cone ≅ t.cone
where
  hom := {hom := t.isLimit.lift s.cone}
  inv := {hom := s.isLimit.lift t.cone}
  hom_inv_id := by
    ext
    apply s.isLimit.hom_ext
    intro j; simp
  inv_hom_id := by
    ext
    apply t.isLimit.hom_ext
    simp

def LimitIso (s t : LimitCone F) : s.cone.pt ≅ t.cone.pt :=
  (Cone.forget F).mapIso (LimitConeIso F s t)


lemma LimitConeIso_uniq (s t : LimitCone F) (σ : s.cone ≅ t.cone) :
  σ = LimitConeIso F s t
:= by
  ext; simp only [LimitConeIso]
  apply t.isLimit.hom_ext
  intro i
  rw [t.isLimit.fac s.cone i]
  rw [σ.hom.w]

def ColimitCoconeIso (s t : ColimitCocone F) :
  s.cocone ≅ t.cocone
:= sorry

def ColimitIso (s t : ColimitCocone F) : s.cocone.pt ≅ t.cocone.pt := sorry

lemma ColimitCoconeIso_uniq (s t : ColimitCocone F) (σ : s.cocone ≅ t.cocone) :
  σ = ColimitCoconeIso F s t
:= sorry






-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.9（積）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
積とは、離散圏で添字づけられた図式の極限である。離散圏 J で添字づけられた図式は対象の族
(F_j)_{j∈J} にすぎず、その上の錐は制約のない射の族 (λ_j : c → F_j)。極限 ∏ F_j の脚
π_k : ∏ F_j → F_k を射影といい、普遍性は射影との合成が自然同型
C(c, ∏ F_j) ≅ ∏ C(c, F_k) を定めることを言う。

構成: 離散圏上の錐が制約のない射の族と一対一であることを示し、極限錐の普遍性を hom の
全単射として述べる。
-/


#check Discrete.functor
def MyDiscreteFunctor [Category I] (F : I → C) :
  Discrete I ⥤ C
where
  obj := F ∘ Discrete.as
  map {i j} f := eqToHom (congrArg F f.down.down)

#print Limits.Fan
def MyFan [Category I] (f : I → C) :=
  Cone (Discrete.functor f)

-- abbrev fans [Category I] (f : I → C) : Cᵒᵖ ⥤ Type _ :=
  -- (Discrete.functor f).cones

#check Limits.HasProduct
def HasProd [Category I] (f : I → C) := -- : Cᵒᵖ ⥤ Type (max u_1 v₁) :=
  HasLimit (Discrete.functor f)


noncomputable def yonedaFansIso {I : Type v₁} (f : I → C) [Hf : Limits.HasProduct f] :
    yoneda.obj (∏ᶜ f) ≅ (Discrete.functor f).cones :=
  yonedaLimitIso (Discrete.functor f)

noncomputable def prodRepresentable {I : Type v₁} (f : I → C) [Hf : Limits.HasProduct f] :
    (Discrete.functor f).cones.RepresentableBy (∏ᶜ f) :=
  (limit.isLimit (Discrete.functor f)).representableBy









-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.11（終対象）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
終対象は添字圏が空の積である。空図式の上の錐は頂点だけからなり、頂点の間のどの射も
錐の射なので、空図式の錐の圏は C 自身と同型で、空図式の極限は定義1.6.14 の終対象である。

構成: 空図式の錐の圏と C の同値、および空図式の極限錐であることと定義1.6.14 の条件との
全単射を示す。
-/

#check @CategoryTheory.Functor.empty
example :
  Discrete PEmpty.{u_1 + 1} ⥤ C
:= Discrete.functor PEmpty.elim

#check CategoryTheory.Limits.asEmptyCone
example (X : C) :
  Cone (Functor.empty C)
where
  pt := X
  π := {
    app a := PEmpty.elim a.as
    naturality := by simp
  }


#check Limits.IsTerminal
def MyIsTerminal (X : C) :=
  IsLimit (asEmptyCone X)



#check @CategoryTheory.Limits.isTerminalEquivUnique

def def_3_1_11 (X : C) : IsLimit (asEmptyCone X) ≃ ∀ Y : C, Unique (Y ⟶ X) where
  toFun H Y := {
    default := H.lift (Limits.asEmptyCone Y)
    uniq f := by
      apply H.hom_ext
      intro i
      exact i.as.elim
  }
  invFun H := {
    lift s := (H s.pt).default
    fac s e := e.as.elim
    uniq s m w := (H s.pt).uniq m
  }
  left_inv := by
    intro H; simp only
    rcases H with ⟨l, f, u⟩
    simp only [IsLimit.mk.injEq, asEmptyCone_pt]
    ext s
    symm
    apply Unique.uniq
  right_inv := by
    intro H; simp only [asEmptyCone_pt]








-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.13（等化子）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
等化子とは、平行対の圏 • ⇉ •（対象2つと、平行な非恒等射2本からなる圏）で添字づけられた
図式の極限である。この形の図式は平行な射の対 f, g : A ⇉ B にすぎない。その上の錐（頂点 c）は
fa = b と ga = b をみたす射の対 a : c → A, b : c → B からなり、b は a で決まるので、fa = ga を
みたす一本の射 a : c → A で表される。等化子の脚 h : E → A はこの性質をもつ普遍的な射で、
fa = ga をみたす任意の a は h を通って一意に分解する。

構成: 平行対の圏、f, g が定める図式、その上の錐、等化子を順に定義する。続けて、錐が射の対
(a, b) で表されること、一本の射 a で表されること、等化子の普遍性を置く。
-/

#check @CategoryTheory.Limits.WalkingParallelPair

inductive MyParallelPairObj : Type
  | zero
  | one

#check @CategoryTheory.Limits.WalkingParallelPairHom

inductive MyParallelPairHom : MyParallelPairObj → MyParallelPairObj → Type
  | id X : MyParallelPairHom X X
  | left : MyParallelPairHom .zero .one
  | right : MyParallelPairHom .zero .one

instance : Category MyParallelPairObj where
  Hom := MyParallelPairHom
  id := MyParallelPairHom.id
  comp {X Y Z} f g :=
    match X, Y, Z, f, g with
    | _, _, _, .id _, g' => g'
    | _, _, _, f', .id _ => f'
  id_comp {X Y} f :=
    match X, Y, f with
    | X', _, .id _ => by simp
    | _, _, _ => by simp
  comp_id {X Y} f :=
    match X, Y , f with
    | X', _, .id _ => by simp
    | _, _, .left => by simp
    | _, _, .right => by simp
  assoc {W X Y Z} f g h := by
    rcases g<;> rcases f<;> simp



#check @CategoryTheory.Limits.parallelPair

def myParallelPair {A B : C} (f g : A ⟶ B) : MyParallelPairObj ⥤ C where
  obj
    | .zero => A
    | .one => B
  map {x y} h :=
    match h with
    | .id c =>
      match c with
      | .zero => 𝟙 A
      | .one => 𝟙 B
    | .left => f
    | .right => g
  map_id {x} := by
    rcases x<;> simp [CategoryStruct.id]
  map_comp {X Y Z} f g := by
    rcases f<;> rcases g<;> simp [CategoryStruct.comp]
    rcases X<;> simp



#check @CategoryTheory.Limits.Fork

#check Cone.π

abbrev MyFork {A B : C} (f g : A ⟶ B) := Cone (myParallelPair f g)

def MyIsEqualizer {A B : C} {f g : A ⟶ B} (t : MyFork f g) := IsLimit t


--  f g : X ⟶ Y

#check Limits.equalizer.ι -- equalizer f g ⟶ X
#check Limits.equalizer.condition -- equalizer f g ≫ f = equalizer f g ≫ g




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.15（引き戻し）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
引き戻しとは、余スパン（半順序集合の圏 • → • ← • で添字づけられた図式）の極限である。
余スパン X --f--> Z <--g-- Y の上の錐は、添字圏の対象ごとの3本の脚からなり、2つの三角形が
可換になるものである。Z への脚は他の2本から決まるので、錐は可換な正方形 fb = gd を定める
射の対 X <--b-- P --d--> Y で表される。引き戻しはこの形の普遍的な錐で、任意の可換正方形の
脚は引き戻しの頂点を通って一意に分解する。記号「⌟」は、可換正方形が単に可換なだけでなく
引き戻し（極限図式）であることを表す。

構成: 余スパンの添字圏、f, g が定める図式、その上の錐、引き戻しを順に定義し、可換正方形を
錐とみたものと、それが引き戻しであること（⌟）を定義する。続けて、錐が3本の脚で表される
こと、可換正方形で表されること、引き戻しの普遍性を置く。
-/

#check @CategoryTheory.Limits.WalkingCospan

inductive MyCospanObj : Type
  | left
  | right
  | apex

instance : PartialOrder MyCospanObj where
  le x y := x = y ∨ y = .apex
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

#check @CategoryTheory.Limits.cospan

def myCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : MyCospanObj ⥤ C where
  obj
    | .left => X
    | .right => Y
    | .apex => Z
  map := sorry
  map_id := sorry
  map_comp := sorry

#check @CategoryTheory.Limits.PullbackCone

abbrev MyPullbackCone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) := Cone (myCospan f g)

def MyIsPullback {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : MyPullbackCone f g) := IsLimit t

#check @CategoryTheory.Limits.PullbackCone.mk

def myPullbackConeOfSquare {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (b : P ⟶ X) (d : P ⟶ Y) (w : b ≫ f = d ≫ g) : MyPullbackCone f g where
  pt := P
  π :=
    { app
        | .left => b
        | .right => d
        | .apex => b ≫ f
      naturality := sorry }

#check @CategoryTheory.IsPullback

def MyIsPullbackSquare {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (b : P ⟶ X) (d : P ⟶ Y) (w : b ≫ f = d ≫ g) : Prop :=
  Nonempty (MyIsPullback (myPullbackConeOfSquare b d w))

def def_3_1_15_cone_legs {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    MyPullbackCone f g ≃
      Σ P : C, { p : (P ⟶ X) × (P ⟶ Y) × (P ⟶ Z) // p.1 ≫ f = p.2.2 ∧ p.2.1 ≫ g = p.2.2 } :=
  sorry

def def_3_1_15_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    MyPullbackCone f g ≃ Σ P : C, { p : (P ⟶ X) × (P ⟶ Y) // p.1 ≫ f = p.2 ≫ g } := sorry

#check @CategoryTheory.Limits.PullbackCone.IsLimit.mk

theorem def_3_1_15_isLimit {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : MyPullbackCone f g) :
    Nonempty (MyIsPullback t) ↔
      ∀ {P : C} (b : P ⟶ X) (d : P ⟶ Y), b ≫ f = d ≫ g →
        ∃! k : P ⟶ t.pt, k ≫ t.π.app .left = b ∧ k ≫ t.π.app .right = d := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.21（逆極限）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏 ωᵒᵖ で添字づけられた図式の極限を、塔（射の列）の逆極限という。ωᵒᵖ で添字づけられた
図式は対象と射の列 ⋯ → F_3 → F_2 → F_1 → F_0 に、合成と恒等射を合わせたものである。
その上の錐は「左端に新しい対象」をすべての三角形が可換になるように付け加えたもので、
逆極限はその終錐である。

構成: 射の列から ωᵒᵖ で添字づけられた図式を組み、その上の錐が「対象と、隣り合う三角形の
可換性」のデータで表されることを置く。最後に逆極限を定義する。
-/

#check @CategoryTheory.Functor.ofOpSequence

def myOfOpSequence {X : ℕ → C} (f : ∀ n, X (n + 1) ⟶ X n) : ℕᵒᵖ ⥤ C where
  obj n := X n.unop
  map := sorry
  map_id := sorry
  map_comp := sorry

def def_3_1_21_cone {X : ℕ → C} (f : ∀ n, X (n + 1) ⟶ X n) :
    Cone (myOfOpSequence f) ≃
      Σ c : C, { π : ∀ n, c ⟶ X n // ∀ n, π (n + 1) ≫ f n = π n } := sorry

def MyIsInverseLimit {X : ℕ → C} {f : ∀ n, X (n + 1) ⟶ X n} (t : Cone (myOfOpSequence f)) :=
  IsLimit t

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.23（余積・始対象・余等化子・押し出し・逐次余極限）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
定義3.1.9・3.1.11・3.1.13・3.1.15・3.1.21 を双対化する。余積 ∐ A_j は離散圏で添字づけられた
図式の余極限で、余極限錐の脚 ι_k を余積の包含という。始対象は空図式の余極限。余等化子は
平行対の圏で添字づけられた図式の余極限で、f, g : A ⇉ B の余等化子は hf = hg をみたす普遍的な
h : B → C。押し出しはスパン（半順序集合の圏 • ← • → • で添字づけられた図式）の余極限で、
f, g の下の普遍的な可換正方形。記号「⌜」は可換正方形が押し出しであることを表す。ω で
添字づけられた図式の余極限を逐次余極限または順極限といい、その図式を ω + 𝟙 の形の図式に
延ばす普遍的なものである。

構成: 余積・始対象・余等化子・押し出し・逐次余極限を、それぞれの添字圏上の図式の下の錐と
余極限錐として定義し、普遍性を置く。余等化子の添字圏は定義3.1.13 の平行対の圏を使う。
-/

#check @CategoryTheory.Limits.Cofan

abbrev MyCofan {I : Type u₂} (f : I → C) := Cocone (Discrete.functor f)

def MyIsCoproduct {I : Type u₂} {f : I → C} (t : MyCofan f) := IsColimit t

#check @CategoryTheory.Limits.Sigma.desc

def def_3_1_23_coproduct {I : Type u₂} {f : I → C} {t : MyCofan f} (h : MyIsCoproduct t)
    (c : C) : (t.pt ⟶ c) ≃ ∀ k, f k ⟶ c := sorry

#check @CategoryTheory.Limits.IsInitial

def MyIsInitial (X : C) := IsColimit (asEmptyCocone X)

#check @CategoryTheory.Limits.isInitialEquivUnique

def def_3_1_23_initial (X : C) : IsColimit (asEmptyCocone X) ≃ ∀ Y : C, Unique (X ⟶ Y) := sorry

#check @CategoryTheory.Limits.Cofork

abbrev MyCofork {A B : C} (f g : A ⟶ B) := Cocone (myParallelPair f g)

def MyIsCoequalizer {A B : C} {f g : A ⟶ B} (t : MyCofork f g) := IsColimit t

#check @CategoryTheory.Limits.Cofork.IsColimit.existsUnique
#check @CategoryTheory.Limits.Cofork.IsColimit.mk'

theorem def_3_1_23_coequalizer {A B : C} {f g : A ⟶ B} (t : MyCofork f g) :
    Nonempty (MyIsCoequalizer t) ↔
      ∀ {c : C} (h : B ⟶ c), f ≫ h = g ≫ h → ∃! k : t.pt ⟶ c, t.ι.app .one ≫ k = h := sorry

#check @CategoryTheory.Limits.WalkingSpan

inductive MySpanObj : Type
  | left
  | right
  | apex

instance : PartialOrder MySpanObj where
  le x y := x = y ∨ x = .apex
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

#check @CategoryTheory.Limits.span

def mySpan {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : MySpanObj ⥤ C where
  obj
    | .left => Y
    | .right => Z
    | .apex => X
  map := sorry
  map_id := sorry
  map_comp := sorry

#check @CategoryTheory.Limits.PushoutCocone

abbrev MyPushoutCocone {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) := Cocone (mySpan f g)

def MyIsPushout {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : MyPushoutCocone f g) := IsColimit t

#check @CategoryTheory.Limits.PushoutCocone.mk

def myPushoutCoconeOfSquare {P X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (i : Y ⟶ P) (j : Z ⟶ P) (w : f ≫ i = g ≫ j) : MyPushoutCocone f g where
  pt := P
  ι :=
    { app
        | .left => i
        | .right => j
        | .apex => f ≫ i
      naturality := sorry }

#check @CategoryTheory.IsPushout

def MyIsPushoutSquare {P X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (i : Y ⟶ P) (j : Z ⟶ P) (w : f ≫ i = g ≫ j) : Prop :=
  Nonempty (MyIsPushout (myPushoutCoconeOfSquare i j w))

#check @CategoryTheory.Limits.PushoutCocone.IsColimit.mk

theorem def_3_1_23_pushout {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : MyPushoutCocone f g) :
    Nonempty (MyIsPushout t) ↔
      ∀ {P : C} (i : Y ⟶ P) (j : Z ⟶ P), f ≫ i = g ≫ j →
        ∃! k : t.pt ⟶ P, t.ι.app .left ≫ k = i ∧ t.ι.app .right ≫ k = j := sorry

#check @CategoryTheory.Functor.ofSequence

def myOfSequence {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1)) : ℕ ⥤ C where
  obj n := X n
  map := sorry
  map_id := sorry
  map_comp := sorry

def MyIsSequentialColimit {X : ℕ → C} {f : ∀ n, X n ⟶ X (n + 1)}
    (t : Cocone (myOfSequence f)) := IsColimit t

theorem def_3_1_23_sequential {X : ℕ → C} {f : ∀ n, X n ⟶ X (n + 1)}
    (t : Cocone (myOfSequence f)) :
    Nonempty (MyIsSequentialColimit t) ↔
      ∀ {c : C} (ι : ∀ n, X n ⟶ c), (∀ n, f n ≫ ι (n + 1) = ι n) →
        ∃! k : t.pt ⟶ c, ∀ n, t.ι.app n ≫ k = ι n := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 注意3.1.27（積と余積の普遍性）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
余積をもつ圏では、射 f : ∐ A_i → X は射の族 (f_i : A_i → X) と自然に一対一に対応し、
積をもつ圏では、射 g : X → ∏ B_j は射の族 (g_j : X → B_j) と一対一に対応する。両者を
合わせると、余積から積への射 ∐ A_i → ∏ B_j は成分の行列 (f_(i,j) : A_i → B_j) で決まる。

構成: 余積から積への射と成分の行列との全単射を述べる。
-/

#check @CategoryTheory.Limits.Sigma.desc
#check @CategoryTheory.Limits.Pi.lift

def rem_3_1_27 {ι κ : Type u₂} (A : ι → C) (B : κ → C) [HasCoproduct A] [HasProduct B] :
    (∐ A ⟶ ∏ᶜ B) ≃ ∀ (i : ι) (j : κ), A i ⟶ B j := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.1.28
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
極限対象への平行な射の対は、極限錐の脚との合成が等しいとき、かつそのときに限り等しい。
双対に、余極限対象からの平行な射の対は、余極限錐の脚との合成が等しいとき、かつそのときに
限り等しい。

構成: 極限と余極限のそれぞれについて、同値として述べる。
-/

#check @CategoryTheory.Limits.IsLimit.hom_ext

theorem lemma_3_1_28_limit {F : J ⥤ C} {t : Cone F} (h : IsLimit t) {X : C}
    (f g : X ⟶ t.pt) : f = g ↔ ∀ j, f ≫ t.π.app j = g ≫ t.π.app j := sorry

#check @CategoryTheory.Limits.IsColimit.hom_ext

theorem lemma_3_1_28_colimit {F : J ⥤ C} {t : Cocone F} (h : IsColimit t) {X : C}
    (f g : t.pt ⟶ X) : f = g ↔ ∀ j, t.ι.app j ≫ f = t.ι.app j ≫ g := sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
半順序集合 (P, ≤) に値を取る図式 F : J → P の極限と余極限を、順序の言葉で特徴づける。

構成: 錐が極限錐であることが頂点が下限であることと同値、余錐が余極限錐であることが底が
上限であることと同値、として述べる。
-/

#check @CategoryTheory.Limits.CompleteLattice.limit_eq_iInf

theorem ex_3_1_i_limit {P : Type u₁} [Preorder P] {F : J ⥤ P} (t : Cone F) :
    Nonempty (IsLimit t) ↔ IsGLB (Set.range F.obj) t.pt := sorry

#check @CategoryTheory.Limits.CompleteLattice.colimit_eq_iSup

theorem ex_3_1_i_colimit {P : Type u₁} [Preorder P] {F : J ⥤ P} (t : Cocone F) :
    Nonempty (IsColimit t) ↔ IsLUB (Set.range F.obj) t.pt := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
2つの極限錐 λ : Δℓ ⇒ F と λ' : Δℓ' ⇒ F の普遍性を使って、脚と両立する一意な同型 ℓ ≅ ℓ' を
直接構成し、命題3.1.7 を証明する。

構成: 錐の圏を経由せず、`IsLimit` から頂点の同型の一意存在を述べる。
-/

#check @CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso
#check @CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp

theorem ex_3_1_ii {F : J ⥤ C} {t t' : Cone F} (h : IsLimit t) (h' : IsLimit t') :
    ∃! e : t.pt ≅ t'.pt, ∀ j, e.hom ≫ t'.π.app j = t.π.app j := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
F ∈ C^J の上の錐の圏は、定数図式関手 Δ : C → C^J と F : 𝟙 → C^J から作るコンマ圏 Δ ↓ F に
同型である。双対に、F の下の錐の圏はコンマ圏 F ↓ Δ である。

構成: 上の錐の圏と `CostructuredArrow (const J) F`、下の錐の圏と `StructuredArrow F (const J)`
の圏同値を述べる。
-/

#check @CategoryTheory.CostructuredArrow
#check @CategoryTheory.Limits.Cone.equivCostructuredArrow

def ex_3_1_iii_over : Cone F ≌ CostructuredArrow (Functor.const J) F := sorry

#check @CategoryTheory.Limits.Cocone.equivStructuredArrow

def ex_3_1_iii_under : Cocone F ≌ StructuredArrow F (Functor.const J) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- h : E → A が f, g : A ⇉ B の等化子図式をなすなら、h は単射である。

#check @CategoryTheory.Limits.mono_of_isLimit_fork

theorem ex_3_1_iv {A B : C} {f g : A ⟶ B} {t : Fork f g} (h : IsLimit t) : Mono t.ι := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.v
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 引き戻しの正方形において f が単射なら、f の対辺 k も単射である。

#check @CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono

theorem ex_3_1_v {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : PullbackCone f g} (h : IsLimit t)
    [Mono f] : Mono t.snd := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
右の正方形が引き戻しである可換な長方形において、左の正方形が引き戻しであることと、
長方形全体が引き戻しであることは同値である（引き戻しの合成と消去）。

構成: `IsPullback` を使い、右の正方形が引き戻しで左の正方形が可換という仮定のもとで、
同値として述べる。
-/

#check @CategoryTheory.IsPullback.paste_horiz_iff

theorem ex_3_1_vi {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C}
    {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
    {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶ X₂₂} {v₁₃ : X₁₃ ⟶ X₂₃}
    (right : IsPullback h₁₂ v₁₂ v₁₃ h₂₂) (comm : h₁₁ ≫ v₁₂ = v₁₁ ≫ h₂₁) :
    IsPullback h₁₁ v₁₁ v₁₂ h₂₁ ↔ IsPullback (h₁₁ ≫ h₁₂) v₁₁ v₁₃ (h₂₁ ≫ h₂₂) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.vii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
J が始対象をもつなら、J で添字づけられた任意の関手の極限は、始対象での値である。
この双対を、後続順序数で添字づけられた図式の余極限の記述に適用する。

構成: 始対象での値を頂点とする錐を組み、それが極限錐であることを示す。双対に、終対象での
値を底とする余錐が余極限錐であることを示す。最後に、後続順序数 n + 1（`Fin (n + 1)`）の
最大元が終対象であることを示す。これで `Fin (n + 1)` で添字づけられた図式の余極限が
最大元での値になる。
-/

#check @CategoryTheory.Limits.coneOfDiagramInitial

def myConeOfDiagramInitial {X : J} (hX : IsInitial X) : Cone F where
  pt := F.obj X
  π :=
    { app := fun j => F.map (hX.to j)
      naturality := sorry }

#check @CategoryTheory.Limits.limitOfDiagramInitial

def ex_3_1_vii_limit {X : J} (hX : IsInitial X) :
    IsLimit (myConeOfDiagramInitial F hX) := sorry

#check @CategoryTheory.Limits.coconeOfDiagramTerminal

def myCoconeOfDiagramTerminal {X : J} (hX : IsTerminal X) : Cocone F where
  pt := F.obj X
  ι :=
    { app := fun j => F.map (hX.from j)
      naturality := sorry }

#check @CategoryTheory.Limits.colimitOfDiagramTerminal

def ex_3_1_vii_colimit {X : J} (hX : IsTerminal X) :
    IsColimit (myCoconeOfDiagramTerminal F hX) := sorry

#check @Fin.isTerminalLast

def ex_3_1_vii_succ (n : ℕ) : IsTerminal (Fin.last n) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.ix
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 零対象をもつ圏では、余積錐の脚は分裂単射である。

#check @CategoryTheory.Limits.HasZeroObject
#check @CategoryTheory.IsSplitMono
#check @CategoryTheory.Limits.isSplitMono_sigma_ι

theorem ex_3_1_ix {ι : Type u₂} [HasZeroObject C] (f : ι → C) [HasCoproduct f] (k : ι) :
    IsSplitMono (Sigma.ι f k) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.x
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
定義1.3.12 の圏の積 C × D が、圏の圏における積を定めることを示す。添字づけられた圏の族の
積を同様に定義する。

構成: 二項の場合に、射影関手を脚とする `Cat` の錐が極限錐であることを述べる。続けて、
圏の族の積とその射影関手を定義し、それらが `Cat` の積を定めることを述べる。
-/

#check @CategoryTheory.Cat
#check @CategoryTheory.Functor.toCatHom
#check @CategoryTheory.Prod.fst
#check @CategoryTheory.Cat.HasLimits.limitConeIsLimit

-- Mathlib に対応物なし
def ex_3_1_x_binary (C D : Type u₁) [Category.{v₁} C] [Category.{v₁} D] :
    IsLimit (BinaryFan.mk (P := Cat.of (C × D))
      (CategoryTheory.Prod.fst C D).toCatHom (CategoryTheory.Prod.snd C D).toCatHom) := sorry

#check @CategoryTheory.pi

def MyPi {ι : Type u₁} (C : ι → Type u₁) := ∀ i, C i

instance {ι : Type u₁} (C : ι → Type u₁) [∀ i, Category.{u₁} (C i)] :
    Category.{u₁} (MyPi C) where
  Hom X Y := ∀ i, X i ⟶ Y i
  id := sorry
  comp := sorry
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

#check @CategoryTheory.Pi.eval

def myPiEval {ι : Type u₁} (C : ι → Type u₁) [∀ i, Category.{u₁} (C i)] (i : ι) :
    MyPi C ⥤ C i where
  obj X := X i
  map f := f i
  map_id := sorry
  map_comp := sorry

-- Mathlib に対応物なし
def ex_3_1_x_family {ι : Type u₁} (C : ι → Type u₁) [∀ i, Category.{u₁} (C i)] :
    IsLimit (Fan.mk (Cat.of (MyPi C)) fun i => (myPiEval C i).toCatHom) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.xii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小圏の同値 E : I ≃ J と図式 F : J → C について、F の上の J 型の錐の圏は FE の上の I 型の
錐の圏と同値である。この同値を使って、F の極限と FE の極限の関係を記述する。

構成: 錐の圏の同値を述べ、次に錐が極限錐であることと E で添字づけ直した錐
（`Cone.whisker`）が極限錐であることの全単射を述べる。
-/

#check @CategoryTheory.Limits.Cone.whiskeringEquivalence

def ex_3_1_xii_cones {I : Type u₂} [Category.{v₂} I] (E : I ≌ J) :
    Cone F ≌ Cone (E.functor ⋙ F) := sorry

#check @CategoryTheory.Limits.Cone.whisker
#check @CategoryTheory.Limits.IsLimit.whiskerEquivalenceEquiv

def ex_3_1_xii_isLimit {I : Type u₂} [Category.{v₂} I] (E : I ≌ J) {F : J ⥤ C} (t : Cone F) :
    IsLimit t ≃ IsLimit (t.whisker E.functor) := sorry
