import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.Perm.Subgroup

/-!
# 2.2 米田の補題

節の数学的な内容は同名の HTML にある。このファイルは本の主張を出現順に並べたもので、主張と
定理群の構成は各セクションの冒頭に、形式化の判断は下の表に、Mathlib の対応物は各
statement の直前の `#check` にある。

形式化の判断:
  Set 値関手   hom 集合と同じ universe に値を取る関手として書く。本が圏に課す locally
               small の仮定が、この universe の一致にあたる
  定理2.2.4    Ψ は成分の式を見つけること自体が中身なので、data ごと丸ごと `sorry` に
               する（1.7 の「data を書いて proof obligation だけ残す」とは逆の選択）
  定理2.2.4 の 「c と F の双方に自然」を、注意2.2.7 のパッケージングで述べる。両辺を積圏
  自然性     上の関手として比べる形は universe が `max u₁ v₁` に上がり `ULift` を伴う
               ので、C を小さく取って curried 形で述べ、それを避ける。本が SET を導入して
               扱う規模の会計を、小ささの仮定に置き換えたことになる
  評価関手     data は Mathlib と同じだが、`map` の自然性と `map_id` が `rfl` で閉じない
               ので自前で組む。statement では Mathlib の `evaluation` を使う
  自然同型の   ev_id を自然変換として先に置く。c 成分の `myEvIdApp`（F 方向の自然性）と、
  組み方       それを束ねる `myEvId`（c 方向の自然性）の2段で、義務は1つずつ。
               `myCoyonedaLemma` は組み立てだけで、成分の同型は `coyonedaEquiv` から、
               自然性は2つの `naturality` フィールドから渡す。Mathlib は
               `curriedCoyonedaLemma` の中で自然変換を無名で与えていて対応する宣言を
               持たないため、自前の2つを参照する
  注意2.2.7 の Remark なので演習は置かないが、本の出現順の位置にセクションだけ作り、中身は
  セクション   Recap にしてある。米田の補題の Mathlib での主張は
               `coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C` で、両辺の
               2つの関手の中身を見ないと statement が読めないため、そこだけを写した。
               Recap は本来「その節が導入するのではない知識」の置き場なので、これは例外。
               `coyonedaLemma` は statement だけを写し、証明は Mathlib のものに委ねる。
               演習 `myCoyonedaLemma` と同じ対象なので、実装を写すと答えになるため
  命題2.2.3    Mathlib の対応物は自己準同型（X = G）の場合だけで、値も反対モノイド Gᵐᵒᵖ
               の側に落ちる
  系2.2.8 の   本は「C は表現された関手が張る充満部分圏と同型」と述べる。Mathlib では
  言い換え     本質像 `EssImageSubcategory` への同値として述べる
  系2.2.8      充満・忠実は定義1.5.7 と一致するので `Functor.Full`・`Functor.Faithful` で
               述べる
  系2.2.10     行演算そのものには定義がないので、本の証明が使う「表現された関手の自然な
               自己変換との同一視」を statement 側に織り込む。`Mat R` の射 X ⟶ Y は X 行
               Y 列で本の Mat_R とは転置なので、本の Hom(−,n) にあたるのは
               `coyoneda.obj (op n)` の側になる。Mathlib に対応物なし
  系2.2.11     Mathlib の対応物は、群が忠実に作用する集合を一般に取った形。本の主張は
               その集合を群自身に取った場合
  演習2.2.iii  Mathlib には一般の系2.2.8 しかないので、`#check` もそれになる

statement を置かない節末問題:
  2.2.ii   説明問題
  2.2.iv   walking isomorphism の圏 I は Mathlib では `WalkingIso`
           （`Mathlib/AlgebraicTopology/SimplicialSet/CoherentIso.lean`）にあるだけで、
           iso・mor を表現された関手として組むところからになる
  2.2.v    4つの自己変換を記述する、その形自体が答えの一部になる
  2.2.iii  前半（よ を集合と写像の族として書き下す）。後半の充満忠実性のみ置く
  2.2.vi   説明問題
  2.2.vii  特徴づけの主張の形自体が答えの一部になる

本文中の例（例2.2.1・例2.2.2・例2.2.9）は載せない。注意2.2.7 は Remark なので演習は置かない
が、定理2.2.4 の自然性に中身のある statement を与えるのがこのパッケージングなので、上記の
とおりセクションと Recap は置く。要素レベルの自然性は Mathlib にも `coyonedaEquiv_comp`・
`coyonedaEquiv_naturality` としてあるが、前者は縦合成の定義そのもので `rfl` で閉じるため
定理としては置かない。反変側は `yonedaEvaluation`・`yonedaPairing`・`yonedaLemma`・
`curriedYonedaLemma`。

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Yoneda.lean`（`yoneda`・`coyoneda`・`yonedaEquiv`・
    `coyonedaEquiv`・`Yoneda.yoneda_full`・`Coyoneda.coyoneda_full`・`coyonedaLemma`）
  - `Mathlib/CategoryTheory/Opposites.lean`（`Functor.rightOp`）
  - `Mathlib/CategoryTheory/Products/Basic.lean`（`evaluation`）
  - `Mathlib/CategoryTheory/EssentialImage.lean`（`Functor.toEssImage`）
  - `Mathlib/CategoryTheory/Category/Preorder.lean`（`Preorder.smallCategory`）
  - `Mathlib/CategoryTheory/Preadditive/Mat.lean`（`Mat`）
  - `Mathlib/GroupTheory/GroupAction/Hom.lean`（`MulActionHom`）
  - `Mathlib/GroupTheory/Perm/Subgroup.lean`（`Equiv.Perm.subgroupOfMulAction`）
-/

open CategoryTheory Opposite

universe v₁ u₁ u₂

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

-- 演習1.3.v の読み替え。Cᵒᵖ ⥤ D の関手を C ⥤ Dᵒᵖ と見る
def Functor.rightOp {D : Type u₂} [Category.{v₂} D] (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ where
  obj X := op (F.obj (op X))
  map f := (F.map f.op).op

-- 例1.4.4(iv) の同変写像。`X →[M] Y` は φ を恒等写像に取ったときの記法
structure MulActionHom {M N : Type*} (φ : M → N) (X : Type*) [SMul M X] (Y : Type*)
    [SMul N Y] where
  protected toFun : X → Y
  protected map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

-- ℕ を順序で圏と見る instance。二重登録を避けて写しは `def` にする
@[instance_reducible]
def Preorder.smallCategory (α : Type u₁) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U ≤ V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans f.down.down g.down.down⟩⟩

-- 本の Mat_R にあたる圏。対象は有限型、射 X ⟶ Y は X 行 Y 列の行列、合成は行列の積
set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] FintypeCat.fintype in
open scoped Classical in
@[instance_reducible]
noncomputable def matCategory (R : Type u₁) [Semiring R] : Category (Mat R) where
  Hom X Y := Matrix X Y R
  id X := (1 : Matrix X X R)
  comp {X Y Z} f g := (show Matrix X Y R from f) * (show Matrix Y Z R from g)
  assoc := by intros; simp [Matrix.mul_assoc]

end Recap

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題2.2.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
左正則作用の G から G-集合 X への同変写像 φ は、φ ↦ φ(e) を通じて X の要素と一対一に
対応する。
-/

#check @MulActionHom.End.equivMulOpposite

theorem prop_2_2_3 {G : Type u₁} [Group G] {X : Type u₂} [MulAction G X] :
    Function.Bijective (fun φ : G →[G] X => φ (1 : G)) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理2.2.4（米田の補題）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
自然変換 α : C(c,−) ⇒ F を、その c 成分での恒等射の像 α_c(id_c) ∈ Fc に送る写像 ev_id
は全単射で、しかも c と F の双方に自然である。

構成: Ψ : Fc → Hom(C(c,−), F) を構成して ev_id との全単射を組み、評価関手を構成して、
      ev_id が両変数についての自然同型をなすことを示す。
-/

#check @CategoryTheory.coyonedaEquiv

def ψ (F : C ⥤ Type v₁) (c : C) (x : F.obj c) : coyoneda.obj (op c) ⟶ F where
  app c' := by
    apply TypeCat.ofHom
    intro f; exact F.map f x
  naturality {X Y} f:= by ext g; simp


#check @CategoryTheory.coyonedaEquiv
example (F : C ⥤ Type v₁) (c : C) :
  (coyoneda.obj (op c) ⟶ F) ≃ F.obj c
where
  toFun f := f.app c (𝟙 c)
  invFun x := ψ F c x

  left_inv := by
    intro f; simp only [Functor.flip_obj_obj, yoneda_obj_obj]
    ext c' g; simp only [Functor.flip_obj_obj, yoneda_obj_obj, ψ, TypeCat.hom_ofHom,
      TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk]
    rw [<- comp_apply, <- f.naturality g]
    simp
  right_inv := by
    intro x; simp [Functor.flip_obj_obj, yoneda_obj_obj, ψ]







#check @CategoryTheory.evaluation

def myEvaluation (C : Type u₁) [SmallCategory C] (D : Type u₁) [SmallCategory D] :
    C ⥤ (C ⥤ D) ⥤ D where
  obj X :=
    { obj := fun F => F.obj X
      map := fun α => α.app X
      map_id F := by simp
      map_comp {Y Z W} F G := by simp
    }
  map {X Y} f :=
    { app := fun F =>  F.map f
      naturality {F G} α := by rw [α.naturality]
    }
  map_id c := by ext F; simp
  map_comp {X Y Z} α β := by ext F; simp

#check @CategoryTheory.curriedCoyonedaLemma

def myEvIdApp (C : Type u₁) [SmallCategory C] (c : C) :
    (coyoneda.rightOp ⋙ coyoneda).obj c ⟶ (evaluation C (Type u₁)).obj c where
  app F := ↾fun α => coyonedaEquiv (X := c) (F := F) α
  naturality f := by
    #check coyoneda.rightOp
    #check coyoneda (C := C ⥤ Type u₁)　

def myEvId (C : Type u₁) [SmallCategory C] :
    coyoneda.rightOp ⋙ coyoneda ⟶ evaluation C (Type u₁) where
  app c := myEvIdApp C c
  naturality F G α := sorry

def myCoyonedaLemma (C : Type u₁) [SmallCategory C] :
    coyoneda.rightOp ⋙ coyoneda ≅ evaluation C (Type u₁) :=
  NatIso.ofComponents
    (fun c => NatIso.ofComponents
      (fun F => Equiv.toIso (coyonedaEquiv (X := c) (F := F)))
      (fun β => (myEvIdApp C c).naturality β))
    (fun f => (myEvId C).naturality f)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 注意2.2.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
ev_id が c と F の双方に自然であることは、対 (c, F) を積圏 C × Set^C の対象と見た
2つの関手のあいだの自然同型として、一枚の主張にまとまる。

このセクションは Recap のみで、演習は置かない。
-/

namespace Recap

-- ev : (c, F) ↦ ULift (Fc)
def coyonedaEvaluation (C : Type u₁) [Category.{v₁} C] :
    C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  evaluationUncurried C (Type v₁) ⋙ uliftFunctor

-- Hom(よ(−),−) : (c, F) ↦ Hom(C(c,−), F)
def coyonedaPairing (C : Type u₁) [Category.{v₁} C] :
    C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

-- ev_id : Hom(よ(−),−) ≅ ev
def coyonedaLemma (C : Type u₁) [Category.{v₁} C] :
    coyonedaPairing C ≅ coyonedaEvaluation C :=
  CategoryTheory.coyonedaLemma C

end Recap

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系2.2.8（米田埋め込み）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- c ↦ C(−,c) と c ↦ C(c,−) の二つの埋め込み よ は、どちらも充満忠実である。

#check @CategoryTheory.Yoneda.yoneda_full

theorem cor_2_2_8_yoneda_full : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full := sorry

#check @CategoryTheory.Yoneda.yoneda_faithful

theorem cor_2_2_8_yoneda_faithful : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful := sorry

#check @CategoryTheory.Coyoneda.coyoneda_full

theorem cor_2_2_8_coyoneda_full : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full := sorry

#check @CategoryTheory.Coyoneda.coyoneda_faithful

theorem cor_2_2_8_coyoneda_faithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系2.2.8 の言い換え
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 表現された関手の間の自然変換は表現対象の間の射とちょうど対応するので、C は前層の圏の
-- うち表現された関手が張る充満部分圏と同型である。

#check @CategoryTheory.Functor.toEssImage

theorem cor_2_2_8_essImage : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).toEssImage.IsEquivalence := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系2.2.10
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- n 行の行列に対する行演算は、単位行列にその行演算を施した行列の左乗算に一致する。

theorem cor_2_2_10 {R : Type u₁} [Ring R] {n : Mat R}
    (α : coyoneda.obj (op n) ⟶ coyoneda.obj (op n)) {m : Mat R} (M : n ⟶ m) :
    α.app m M = α.app n (𝟙 n) ≫ M := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系2.2.11（Cayley の定理）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 任意の群は、ある置換群の部分群と同型である。

#check @Equiv.Perm.subgroupOfMulAction

theorem cor_2_2_11 (G : Type u₁) [Group G] :
    ∃ (X : Type u₁) (H : Subgroup (Equiv.Perm X)), Nonempty (G ≃* H) := sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.2.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
定理2.2.4 の双対。反変関手 F : Cᵒᵖ ⥤ Set に対し、自然変換 C(−,c) ⇒ F は F の c での値の
要素と一対一に対応する。

構成: Ψ : Fc → Hom(C(−,c), F) を構成し、定理2.2.4 と同じ4つを示す。
-/

#check @CategoryTheory.yonedaEquiv

def myΨContra (F : Cᵒᵖ ⥤ Type v₁) (c : C) (x : F.obj (op c)) : yoneda.obj c ⟶ F := sorry

#check @CategoryTheory.yonedaEquiv

theorem ex_2_2_i_right_inv (F : Cᵒᵖ ⥤ Type v₁) (c : C) (x : F.obj (op c)) :
    (myΨContra F c x).app (op c) (𝟙 c) = x := sorry

#check @CategoryTheory.yonedaEquiv

theorem ex_2_2_i_left_inv (F : Cᵒᵖ ⥤ Type v₁) (c : C) (α : yoneda.obj c ⟶ F) :
    myΨContra F c (α.app (op c) (𝟙 c)) = α := sorry

#check @CategoryTheory.yonedaEquiv_comp

theorem ex_2_2_i_nat_functor {F G : Cᵒᵖ ⥤ Type v₁} (c : C) (β : F ⟶ G)
    (α : yoneda.obj c ⟶ F) :
    (α ≫ β).app (op c) (𝟙 c) = β.app (op c) (α.app (op c) (𝟙 c)) := sorry

#check @CategoryTheory.yonedaEquiv_naturality

theorem ex_2_2_i_nat_object (F : Cᵒᵖ ⥤ Type v₁) {c d : C} (g : d ⟶ c)
    (α : yoneda.obj c ⟶ F) :
    (yoneda.map g ≫ α).app (op d) (𝟙 d) = F.map g.op (α.app (op c) (𝟙 c)) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.2.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
よ : ω ↪ Set^(ωᵒᵖ) を集合と写像の族として書き下し、米田の補題に訴えずに、充満忠実性を
直接証明する。
-/

#check @CategoryTheory.Yoneda.yoneda_full

theorem ex_2_2_iii_full : (yoneda : ℕ ⥤ ℕᵒᵖ ⥤ Type).Full := sorry

#check @CategoryTheory.Yoneda.yoneda_faithful

theorem ex_2_2_iii_faithful : (yoneda : ℕ ⥤ ℕᵒᵖ ⥤ Type).Faithful := sorry
