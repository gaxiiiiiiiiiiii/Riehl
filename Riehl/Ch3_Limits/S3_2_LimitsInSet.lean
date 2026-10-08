import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Elements

/-!
# 3.2 集合の圏における極限

節の数学的な内容は同名の HTML にある。このファイルは本の主張を出現順に並べたもので、主張と
定理群の構成は各セクションの冒頭に、形式化の判断は下の表に、Mathlib の対応物と包装は各
statement の直前の `#check`・`#print` にある。

形式化の判断:
  Set と一点    Set は `Type (max w v)`、一点集合 ∗ は `PUnit`。添字圏の universe w を
  集合          Set の universe から切り離した。3.1 は J を Set と同じ universe に取って
                いるが、この節はその約束を外す。本が「小図式」と呼ぶもののうち
                `WalkingParallelPair`・`WalkingCospan`・`ℕᵒᵖ`・`SingleObj G` は Mathlib
                で `Type 0` に固定されていて、J を Set と同じ universe に取ると例3.2.7
                以降が書けないためである。w := v と置けば元の形に戻るので、主張は狭まって
                いない。Mathlib の `Types.limitCone` が同じ形（`J ⥤ Type (max v u)`）。
                頂点 ∗ の錐の集合 Cone(∗, F) は `Type (max w v)` に落ち、Set の対象になる
  定義3.2.1     完備性は本の定義どおり「すべての小図式が極限錐を持つ」で自前実装する。
                Mathlib の `HasLimits` は `HasLimit`・`HasLimitsOfShape`・`HasLimitsOfSize`
                の 3 段に分かれているが、中身は同じ存在命題なので statement は Mathlib で
                述べる
  (3.2.2)       極限錐の頂点と Cone(∗, F) の全単射として置く。Mathlib は同じ内容を
                `F.sections`（対象ごとの要素の族で両立条件を満たすもの）を経由して持つ
  定義3.2.3     lim F := Cone(∗, F) を本の定義どおりに組む。脚が錐をなすこと（自然性）は
                本が直後に検証しているので演習。Mathlib の `Types.limitCone` は
                `F.sections` を頂点に取るので持ち方が違い、定理3.2.4 は自前の錐について
                述べる
  定理3.2.4     「Set は完備」を、自前の錐が極限錐であることと、
                `HasLimitsOfSize.{w, w} (Type (max w v))` の 2 本に割る。添字圏の universe
                を分けたので、Mathlib 側も `HasLimits`（`HasLimitsOfSize.{v, v}`）ではなく
                サイズを明示した形で述べる
  例3.2.5       規約では例を載せないが、定理3.2.11 の証明が名指しで引用するので載せる。
                本文どおり、定義3.2.3 を離散図式に当てはめた錐 `myProd` を置き、その頂点が
                J-組の集合 `Π j, F j` と全単射であることを演習にする。Mathlib の
                `Types.productLimitCone` は頂点 `∀ j, F j` と射影を直接与える形で、
                定義3.2.3 を経由しないので持ち方が違う
  例3.2.6       空図式は `Functor.empty`（`Discrete PEmpty`）で取る。Mathlib の
                `Types.terminalIso` は `⊤_ Type u ≅ PUnit` で、極限の頂点ではなく終対象に
                ついて述べた形なので持ち方が違う
  例3.2.7       平行対は `parallelPair` で取る。`WalkingParallelPair` が `Type 0` なので
                w := 0 で使う。Mathlib の `Types.equalizerLimit` は頂点 `{x // g x = h x}`
                と包含を直接与える形で、定義3.2.3 を経由しない
  例3.2.8       図式圏は `ℕᵒᵖ`（w := 0）。本文の記述は隣り合う射についての条件しか課して
                いないので、全単射を作るには ℕ の一般の `≤` へ帰納法で延ばす必要がある。
                この延長がこの例の中身で、他の例にはない。Mathlib に対応物なし
  例3.2.9       余スパンは `cospan` で取る（w := 0）。頂点は本文どおり X × Y の部分型で
                置く。Mathlib の `Types.pullbackLimitCone` も同じ部分型を頂点に取るが、
                定義3.2.3 を経由しない
  例3.2.10      BG は `SingleObj G` で取る。`SingleObj.category` が `Category.{u, 0}` な
                ので、`SmallCategory` にするには G を `Type 0` に取る必要がある。本の
                「群 G」より狭いが、この節で G の大きさは論点ではない。Mathlib に対応物
                なし
  定理3.2.11    2 つの積は本の証明と同じく例3.2.5 の記述（関数の族）で取る。平行対 c・d は
                本の証明どおり明示的に書き切り、圏論的な定義は注意3.2.13 側に置く。
                等化子図式の錐（lim F からの写像とその等化条件）を組み、極限錐であることを
                演習にする。Mathlib の対応物 `buildIsLimit` は任意の圏で積と等化子から
                極限を組む定理3.5.11 側の形
  注意3.2.13    積の普遍性による c・d を組み、定理3.2.11 の明示的な記述と一致することを
                演習にする。本文が「要素への作用を見れば一致が確かめられる」と述べている
                部分にあたる。普遍性は Mathlib の `Types.productLimitCone` の `isLimit`
                から取る
  演習3.2.iii   非恒等射を `p.2.2 ≠ eqToHom h`（域と余域が等しい h があっても恒等射で
                ない）で述べる。積は定理3.2.11 と同じく関数の族で取る
  演習3.2.vi    自然変換の集合 Hom(F, G) は `F ⟶ G`。C は局所小なので hom が `Type v` に
                あり、J で添字づけた積は `Type (max w v)` に落ちる。2 つの積は関数の族で
                取る。Mathlib に対応物なし
  演習3.2.vii   Π の切断を、関手 s : J ⥤ ∫F で s ⋙ Π = 𝟭 J を満たすものとして述べる。
                関手の等式は同型より強いが、本の「切断」の字義に合わせた。Mathlib に
                対応物なし
  宣言の名前    規約の種別（def・lemma・prop・thm・cor・ex）に例と注意が無いので、例を
                `eg_`、注意を `rem_` で始める
  本にない      次は本に対応する概念がなく、Mathlib の道具として statement に使う。
  Mathlib の    `Fork`・`Fork.ofι`（等化子図式の錐）、`Functor.Elements.π`（要素の圏
  道具          からの射影。演習3.2.vii）

statement を置かない節末問題:
  3.2.i    グラフを積と等化子で記述する問題で、記述そのものが答えになる。後半の余グラフも
           同じ
  3.2.ii   小圏を Set の図式として定義し直す問題。定義を組むこと自体が問題で、statement を
           書くと答えになる
  3.2.iii  後半（原子的な射に絞れることを論ずる）は説明問題。前半のみ置く
  3.2.iv   可換四角形の集合を引き戻しとして構成する問題で、どの余スパンの引き戻しかが
           答えになる
  3.2.v    Hom(F, G) を極限とする図式の添字圏 J§ を構成する問題で、図式の形が答えになる

例3.2.14（冪等射の分裂）と、定理3.2.11 の前の「引き戻しは積の等化子である」の観察は載せ
ない。3.2.14 の図式圏（冪等な自己射を 1 本持つ一点圏）は Mathlib になく、自前で組むとこの
節の主題から外れる。観察のほうは定理3.2.11 の特別な場合で、独立した主張ではない。

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Limits/HasLimits.lean`（`HasLimit`・`HasLimitsOfShape`・
    `HasLimitsOfSize`・`HasLimits`）
  - `Mathlib/CategoryTheory/Types/Basic.lean`（`Functor.sections`）
  - `Mathlib/CategoryTheory/Limits/Types/Limits.lean`（`Types.limitCone`・
    `Types.limitConeIsLimit`・`Types.isLimitEquivSections`・`Types.hasLimitsOfSize`）
  - `Mathlib/CategoryTheory/Limits/Types/Products.lean`（`Types.productLimitCone`）
  - `Mathlib/CategoryTheory/Limits/Types/Equalizers.lean`（`Types.equalizerLimit`）
  - `Mathlib/CategoryTheory/Limits/Types/Pullbacks.lean`（`Types.pullbackLimitCone`）
  - `Mathlib/CategoryTheory/SingleObj.lean`（`SingleObj`・`SingleObj.star`。例3.2.10）
  - `Mathlib/CategoryTheory/Yoneda.lean`（`Functor.sectionsEquivHom`）
  - `Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`
    （`HasLimitOfHasProductsOfHasEqualizers.buildIsLimit`）
  - `Mathlib/CategoryTheory/Elements.lean`（`Functor.Elements`・`Functor.Elements.π`）
-/

open CategoryTheory Opposite Limits

universe v u w

variable {J : Type w} [SmallCategory J]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.2.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 図式が小さいとは添字圏が小圏であること。圏が完備とはすべての小図式の極限を持つこと、
-- 余完備とはすべての小図式の余極限を持つことである。


#print SmallCategory
#check @CategoryTheory.Limits.HasLimits

class MyComplete (C : Type u) [Category.{v} C] : Prop where
  hasLimit : ∀ {J : Type w} [SmallCategory J] (F : J ⥤ C),
    ∃ t : Cone F, Nonempty (IsLimit t)

#check @CategoryTheory.Limits.HasColimits

class MyCocomplete (C : Type u) [Category.{v} C] : Prop where
  hasColimit : ∀ {J : Type w} [SmallCategory J] (F : J ⥤ C),
    ∃ t : Cocone F, Nonempty (IsColimit t)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- (3.2.2)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 小図式 F : J → Set の極限は、一点集合 ∗ が恒等関手を表現することから、頂点 ∗ を持つ
-- F 上の錐の集合と一対一に対応する。

#check @CategoryTheory.Limits.Types.isLimitEquivSections
#check @CategoryTheory.Functor.sectionsEquivHom



#check  Functor.CorepresentableBy.id
def CorepresentableById : (𝟭 (Type v)).CorepresentableBy PUnit.{v + 1} := {
  homEquiv {X} := {
    toFun f := f.hom PUnit.unit
    invFun x := homOfElement x
    left_inv := by
      intro f; simp only
      rfl
    right_inv := by
      intro x; simp only [Functor.id_obj]
      rfl
  }
}

def def_3_2_2 {F : J ⥤ Type (max w v)} {t : Cone F} (ht : IsLimit t) :
    t.pt ≃ F.cones.obj (op PUnit.{max w v + 1}) := by
  apply Equiv.trans
  · exact Functor.CorepresentableBy.id.homEquiv.symm
  · exact (ht.representableBy.homEquiv (X := PUnit.{max w v + 1}))





-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.2.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小図式 F : J → Set に対し、lim F := Cone(∗, F) と定め、脚 λ_j : lim F → Fj を、錐 μ をその
j 番目の脚 μ_j ∈ Fj に送る関数とする。この脚の族は F 上の錐をなす。

構成: 頂点 lim F と脚の族を組み、脚が三角形 (3.1.3) を可換にすることを示す。
-/



#print Types.limitCone
#print Functor.sections
#print Functor.const

def myLimitCone (F : J ⥤ Type (max w v)) : Cone F where
  --   ( _ ↦ * ) ⟶ F
  --   (Functor.const J).obj PUnit ⟶ F
  pt := F.cones.obj (op PUnit.{max w v + 1})
  π := {
    app j := ↾fun μ => μ.app j PUnit.unit
    naturality {i j} f := by
      ext σ; simp at σ
      simp only [Functor.cones_obj, Functor.const_obj_obj, Functor.const_obj_map, Functor.op_obj,
        Category.id_comp, TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk,
        comp_apply]
      rw [<- comp_apply (σ.app i) (F.map f), <- σ.naturality]
      simp
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.2.4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏 Set は完備である。すなわち、定義3.2.3 の錐はすべての小図式について極限錐である。

構成: 定義3.2.3 の錐が極限錐であることを示し、Set がすべての小さな極限を持つことを示す。
-/

#check Types.limitConeIsLimit

def thm_3_2_4 (F : J ⥤ Type (max w v)) : IsLimit (myLimitCone F) where
  lift s := ↾ fun x => {
    app j := ↾ fun _ => s.π.app j x
    naturality {i j} f := by
      simp only [Functor.op_obj, Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      ext u; simp only [TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk, comp_apply]
      rw [<- comp_apply, <- s.π.naturality]
      simp
  }
  fac s j := by
    ext x;
    simp [myLimitCone]
  uniq s m w := by
    ext x; apply NatTrans.ext; ext j u
    simp only [Functor.op_obj, Functor.const_obj_obj, TypeCat.Fun.toFun_apply,
      ConcreteCategory.hom_ofHom]
    exact ConcreteCategory.congr_hom (w j) x



#check @CategoryTheory.Limits.Types.hasLimitsOfSize
theorem thm_3_2_4_complete : HasLimitsOfSize.{w, w} (Type (max w v)) := ⟨
  fun _ _  => ⟨
    fun F => ⟨⟨{
      cone := Types.limitCone F
      isLimit := Types.limitConeIsLimit F
    }⟩⟩
⟩⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 例3.2.5
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
Set における圏論的な積は通常のデカルト積と一致する。集合 β の要素 b で添字づけられた集合の
族 A_b に対し、∏_{b∈β} A_b は各 A_b から要素を一つずつ選んだ β-組の集合である。

構成: 頂点 ∀ b, A b と射影の族で離散図式上の錐を組み、それが極限錐であることを示す。
-/

#check @CategoryTheory.Limits.Types.productLimitCone
#print Types.productLimitCone

def myProd (F : J → Type (max w v)) :
  Cone (Discrete.functor F)
:= myLimitCone (Discrete.functor F)

example (F : J → Type (max w v)) :
    (myProd F).pt ≃ (Π j, F j) := by
  refine {
    toFun := fun σ i => σ.app ⟨i⟩ PUnit.unit
    invFun := fun f => {
      app x := ↾ fun _ => f x.as
      naturality {i j} g := by
        rcases i with ⟨i⟩
        rcases j with ⟨j⟩
        obtain ⟨⟨rfl⟩⟩ := g
        simp
    }
    left_inv := by
      intro σ
      apply NatTrans.ext
      ext i u; simp
      rcases u; simp
    right_inv := by
      intro f; simp
  }




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 例3.2.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
Set の終対象は、空図式上の頂点 ∗ を持つ錐の集合である。錐のデータは頂点の選択だけなので、
錐はただ一つしかない。

構成: 空図式上に定義3.2.3 の錐を置き、その頂点が一点集合であることを示す。
-/

#check @CategoryTheory.Limits.Types.terminalIso

def myTerminal : Cone (Functor.empty.{w} (Type (max w v))) :=
  myLimitCone (Functor.empty.{w} (Type (max w v)))

def eg_3_2_6 : (myTerminal.{v, w}).pt ≃ PUnit.{max w v + 1} where
  toFun x := PUnit.unit
  invFun u := {
    app x := ↾ fun u => isEmptyElim x.as
    naturality {i j}  f:= by
      obtain ⟨i⟩ := i
      obtain ⟨j⟩ := j
      obtain ⟨⟨rfl⟩⟩ := f
      simp
  }
  left_inv := by
    intro σ
    apply NatTrans.ext; ext e f
    exact e.as.elim
  right_inv := by
    intro u; simp






-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 例3.2.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
平行な関数の対 f, g : X ⇉ Y の等化子は、f(x) = g(x) を満たす x ∈ X の集合である。

構成: 平行対上に定義3.2.3 の錐を置き、その頂点が f と g の一致する要素の集合であることを
      示す。
-/

#check @CategoryTheory.Limits.Types.equalizerLimit

def myEqualizer {X Y : Type v} (f g : X ⟶ Y) : Cone (parallelPair f g) :=
  myLimitCone.{v, 0} (parallelPair f g)

def eg_3_2_7 {X Y : Type v} (f g : X ⟶ Y) :
    (myEqualizer f g).pt ≃ {x : X // f x = g x} where
  toFun σ := by
    simp [myEqualizer, myLimitCone] at σ
    use σ.app WalkingParallelPair.zero PUnit.unit
    rw [<- comp_apply, <- comp_apply]
    have Hl := σ.naturality WalkingParallelPairHom.left
    have Hr := σ.naturality WalkingParallelPairHom.right
    simp only [Functor.const_obj_obj, parallelPair_obj_one, Functor.const_obj_map, Category.id_comp,
      parallelPair_obj_zero, parallelPair_map_left, parallelPair_map_right] at Hl Hr
    rw [<- Hl, <- Hr]
  invFun x := {
    app p :=
      match p with
      | .zero => ↾ fun _ => x.val
      | .one => ↾ fun _ => f.hom x.val
    naturality a b h :=
      match h with
      | .id c =>
        match c with
        | .zero => by
          ext u; simp
        | .one => by
          ext u; simp
      | .left => by ext u; simp
      | .right => by ext u; exact x.prop
  }
  left_inv := by
    intro σ
    apply NatTrans.ext; ext x u
    rcases u
    rcases x
    · simp
    · simp only [parallelPair_obj_one, Functor.op_obj, Functor.const_obj_obj,
      parallelPair_obj_zero, TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk]
      rw [<- comp_apply]
      have Hl := σ.naturality WalkingParallelPairHom.left
      simp only [Functor.op_obj, Functor.const_obj_obj, parallelPair_obj_one, Functor.const_obj_map,
        Category.id_comp, parallelPair_obj_zero, parallelPair_map_left] at Hl
      rw [<- Hl]
  right_inv := by
    intro x; ext; simp






-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 例3.2.8
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
図式 F : ωᵒᵖ → Set の極限は、各三角形を可換にする要素の組 (x_n ∈ Fn)_{n∈ω} の集合である。

構成: ωᵒᵖ 上に定義3.2.3 の錐を置き、その頂点が、隣り合う射について両立する族の集合である
      ことを示す。
-/

def myInverseLimit (F : ℕᵒᵖ ⥤ Type v) : Cone F := myLimitCone.{v, 0} F

def eg_3_2_8 (F : ℕᵒᵖ ⥤ Type v) :
    (myInverseLimit F).pt ≃
      {x : ∀ n : ℕ, F.obj (op n) // ∀ n, F.map (homOfLE (Nat.le_succ n)).op (x (n + 1)) = x n} :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 例3.2.9
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
関数の余スパン X →f Z ←g Y の引き戻しは、f(x) = g(y) を満たす対 (x, y) ∈ X × Y の集合で
ある。

構成: 余スパン上に定義3.2.3 の錐を置き、その頂点が f と g で行き先の一致する対の集合で
      あることを示す。
-/

#check @CategoryTheory.Limits.Types.pullbackLimitCone

def myPullback {X Y Z : Type v} (f : X ⟶ Z) (g : Y ⟶ Z) : Cone (cospan f g) :=
  myLimitCone.{v, 0} (cospan f g)

def eg_3_2_9 {X Y Z : Type v} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (myPullback f g).pt ≃ {p : X × Y // f p.1 = g p.2} where
  toFun σ := by
    have H1 := σ.app WalkingCospan.one
    let x := (σ.app WalkingCospan.left).hom PUnit.unit
    let y := (σ.app WalkingCospan.right).hom PUnit.unit
    simp only [cospan_left, cospan_right] at x y
    use ⟨x, y⟩; simp only
    have Hl := σ.naturality WalkingCospan.Hom.inl
    have Hr := σ.naturality WalkingCospan.Hom.inr
    simp only [Functor.op_obj, Functor.const_obj_obj, cospan_one, Functor.const_obj_map,
      Category.id_comp, cospan_left, cospan_map_inl, cospan_right, cospan_map_inr] at Hl Hr
    have Hl' := congr_arg (fun a => a.hom PUnit.unit) Hl
    have Hr' := congr_arg (fun a => a.hom PUnit.unit) Hr
    simp only [comp_apply] at Hr' Hl'
    conv at Hl' => arg 2; arg 2; change x
    conv at Hr' => arg 2; arg 2; change y
    rw [<- Hl', <- Hr']
  invFun p := {
    app x :=
      match x with
      | none => ↾ fun _ => f.hom p.val.fst
      | some w =>
        match w with
        | .left => ↾ fun _ => p.val.fst
        | .right => ↾ fun _ => p.val.snd
    naturality a b h :=
      match h with
      | .id _ =>
        match a with
        | none => by ext u; simp
        | some w =>
          match w with
          | .left => by simp
          | .right => by simp
      | .term w =>
        match w with
        | .left => by ext u; simp
        | .right => by ext u; exact p.prop
  }
  left_inv := by
    intro σ
    apply NatTrans.ext; ext x u
    rcases u
    cases x with
    | none =>
      simp only [cospan_one, Functor.op_obj, Functor.const_obj_obj, cospan_left, TypeCat.hom_ofHom,
        TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk]
      rw [<- comp_apply]
      have Hl := σ.naturality WalkingCospan.Hom.inl
      simp only [Functor.op_obj, Functor.const_obj_obj, cospan_one, Functor.const_obj_map,
        Category.id_comp, cospan_left, cospan_map_inl] at Hl
      rw [<- Hl]
    | some w =>
      cases w with
      | left => simp
      | right => simp
  right_inv := by
    intro p; simp



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 例3.2.10
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
左 G-集合 X : BG → Set の極限は、すべての g ∈ G について g·x = x を満たす x の集合、すなわち
X の G-固定点の集合である。

構成: BG 上に定義3.2.3 の錐を置き、その頂点が G の作用で動かない要素の集合であることを
      示す。
-/

def myFixedPoints {G : Type} [Group G] (X : SingleObj G ⥤ Type v) : Cone X :=
  myLimitCone.{v, 0} X

def eg_3_2_10 {G : Type} [Group G] (X : SingleObj G ⥤ Type v) :
    (myFixedPoints X).pt ≃ {x : X.obj (SingleObj.star G) // ∀ g : G, X.map g x = x} := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定理3.2.11
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
Set における小さな極限は、積の間の写像の対の等化子である。小図式 F : J → Set に対し、
∏_{j∈ob J} Fj から ∏_{f∈mor J} F(cod f) への平行対 c（脚の族を (λ_{cod f})_f に送る）と
d（(Ff(λ_{dom f}))_f に送る）について、lim F は c と d の等化子図式 (3.2.12) をなす。

構成: 平行対 c・d を組む。lim F から ∏ Fj への写像を組み、それが c と d を等化することを
      示し、等化子図式が極限錐であることを示す。
-/



abbrev Obj (F : J ⥤ Type (max w v)) :=
  ∏ᶜ (fun j => F.obj j)
abbrev Cod (F : J ⥤ Type (max w v)) :=
  ∏ᶜ (fun p : (Σ j k : J, j ⟶ k) => F.obj p.2.1)

noncomputable def c (F : J ⥤ Type (max w v)) : Obj F ⟶ Cod F :=
  Pi.lift (fun x =>  Pi.π (fun j ↦ F.obj j) x.2.1 )

noncomputable def d (F : J ⥤ Type (max w v)) : Obj F ⟶ Cod F := by
  apply Pi.lift  (fun x => Pi.π (fun j ↦ F.obj j) x.1 ≫ F.map x.2.2 )

noncomputable def ι (F : J ⥤ Type (max w v)) :
  (myLimitCone F).pt ⟶ Obj F := Pi.lift (fun j => ↾ fun σ => σ.app j PUnit.unit)

lemma ι_condition  (F : J ⥤ Type (max w v)) :
    ι F ≫ c F = ι F ≫ d F := by
  apply Pi.hom_ext
  intro ⟨i, j, f⟩
  simp only [ι, Functor.op_obj, Functor.const_obj_obj, c, Category.assoc, limit.lift_π, Fan.mk_pt,
    Fan.mk_π_app, d, limit.lift_π_assoc, Discrete.functor_obj_eq_as]
  ext σ
  simp only [TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk, comp_apply]
  rw [<- comp_apply _ (F.map f), <- σ.naturality]
  simp

noncomputable abbrev fork (F : J ⥤ Type (max w v)) :
    Fork (c F) (d F) := Fork.ofι (ι F) (ι_condition F)

noncomputable def fork_lift (F : J  ⥤ Type (max w v)) (s : Fork (c F) (d F)) (x : s.pt) :
    (fork F).pt where
  app j := ↾ fun _ => Pi.π (fun j ↦ F.obj j) j ((s.π.app (WalkingParallelPair.zero)).hom x)
  naturality {i j} f := by
    ext u
    simp only [Functor.op_obj, Functor.const_obj_obj, Functor.const_obj_map, Fork.app_zero_eq_ι,
      parallelPair_obj_zero, Category.id_comp, TypeCat.hom_ofHom, TypeCat.Fun.toFun_apply,
      TypeCat.Fun.coe_mk, comp_apply]
    rw [<- comp_apply, <- comp_apply, <- comp_apply]
    have Hs := s.condition
    let pi := Pi.π (fun p : (Σ j k : J, j ⟶ k) => F.obj p.2.1) ⟨i, j, f⟩
    have E := congr_arg (fun f => (f ≫ pi).hom x) Hs
    rw [Category.assoc, Category.assoc] at E
    simp only [pi, c, d] at E
    rw [Pi.lift_comp_π,  Pi.lift_comp_π] at E
    apply E



noncomputable def fork_isLimit (F : J ⥤ Type (max w v)) :
    IsLimit (fork F) := by
  apply Fork.IsLimit.mk (fork F) ?_ ?_ ?_
  · intro s
    apply TypeCat.ofHom
    intro x
    exact fork_lift F s x
  · intro s; ext j x
    simp only [Category.assoc, TypeCat.Fun.toFun_apply, comp_apply, TypeCat.hom_ofHom,
      TypeCat.Fun.coe_mk]
    rw [<- comp_apply, <- comp_apply]
    simp only [fork]
    rw [Fork.ι_ofι]
    conv => arg 1; simp only [ι, Functor.op_obj, Functor.const_obj_obj, limit.lift_π, Fan.mk_pt,
      Fan.mk_π_app, TypeCat.hom_ofHom]; change (ConcreteCategory.hom ((fork_lift F s x).app j)) PUnit.unit
    simp [fork_lift]
  · intro s m w
    simp only [fork] at w
    rw [Fork.ι_ofι] at w
    ext x
    apply NatTrans.ext
    ext j u; rcases u
    simp only [Functor.op_obj, Functor.const_obj_obj, TypeCat.Fun.toFun_apply, fork_lift,
      Fork.app_zero_eq_ι, parallelPair_obj_zero, ConcreteCategory.hom_ofHom]
    conv => arg 2; arg 1; change ( ConcreteCategory.hom (↾fun x_1 ↦ (ConcreteCategory.hom (Pi.π (fun j ↦ F.obj j) j)) ((TypeCat.Hom.hom s.ι) x)))
    simp only [TypeCat.hom_ofHom, TypeCat.Fun.coe_mk]
    have E := congr_arg (fun f => (f ≫ Pi.π (fun j ↦ F.obj j) j).hom x) w
    simp only [Fork.ofι_pt, Category.assoc, comp_apply] at E
    rw [<- E]
    simp [ι]







-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.2.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
等化子図式 (3.2.12) の第二の積を非恒等射だけで添字づけても、lim F はなお等化子である。

構成: 非恒等射で添字づけた積と平行対を組み、lim F からの写像がそれを等化することを示し、
      等化子図式が極限錐であることを示す。
-/

def myNonIdentity (J : Type w) [SmallCategory J] : Type w :=
  {p : Σ j k : J, j ⟶ k // ¬ ∃ h : p.1 = p.2.1, p.2.2 = eqToHom h}

def myProdNonId (F : J ⥤ Type (max w v)) : Type (max w v) :=
  ∀ p : myNonIdentity J, F.obj p.1.2.1

def myC' (F : J ⥤ Type (max w v)) : myProdOb F ⟶ myProdNonId F :=
  ↾fun lam p => lam p.1.2.1

def myD' (F : J ⥤ Type (max w v)) : myProdOb F ⟶ myProdNonId F :=
  ↾fun lam p => F.map p.1.2.2 (lam p.1.1)

theorem ex_3_2_iii_condition (F : J ⥤ Type (max w v)) :
    thm_3_2_11_ι F ≫ myC' F = thm_3_2_11_ι F ≫ myD' F := sorry

def ex_3_2_iii (F : J ⥤ Type (max w v)) :
    IsLimit (Fork.ofι (thm_3_2_11_ι F) (ex_3_2_iii_condition F)) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.2.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小圏 J、局所小な圏 C、平行な関手の対 F, G : J ⇉ C に対し、自然変換の集合 Hom(F, G) は、
∏_{j} C(Fj, Gj) から ∏_{f : j→k} C(Fj, Gk) への平行対（成分の族 (α_j)_j を
(Ff ≫ α_k)_f に送る写像と (α_j ≫ Gf)_f に送る写像）の等化子である。

構成: 平行対を組む。Hom(F, G) から ∏ C(Fj, Gj) への写像を組み、それが平行対を等化する
      ことを示し、等化子図式が極限錐であることを示す。
-/

def myHomProdOb {C : Type u} [Category.{v} C] (F G : J ⥤ C) : Type (max w v) :=
  ∀ j : J, F.obj j ⟶ G.obj j

def myHomProdMor {C : Type u} [Category.{v} C] (F G : J ⥤ C) : Type (max w v) :=
  ∀ p : (Σ j k : J, j ⟶ k), F.obj p.1 ⟶ G.obj p.2.1

def myHomC {C : Type u} [Category.{v} C] (F G : J ⥤ C) : myHomProdOb F G ⟶ myHomProdMor F G :=
  ↾fun a p => F.map p.2.2 ≫ a p.2.1

def myHomD {C : Type u} [Category.{v} C] (F G : J ⥤ C) : myHomProdOb F G ⟶ myHomProdMor F G :=
  ↾fun a p => a p.1 ≫ G.map p.2.2

def ex_3_2_vi_ι {C : Type u} [Category.{v} C] (F G : J ⥤ C) : (F ⟶ G) ⟶ myHomProdOb F G :=
  ↾fun α j => α.app j

theorem ex_3_2_vi_condition {C : Type u} [Category.{v} C] (F G : J ⥤ C) :
    ex_3_2_vi_ι F G ≫ myHomC F G = ex_3_2_vi_ι F G ≫ myHomD F G := sorry

def ex_3_2_vi {C : Type u} [Category.{v} C] (F G : J ⥤ C) :
    IsLimit (Fork.ofι (ex_3_2_vi_ι F G) (ex_3_2_vi_condition F G)) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.2.vii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 小図式 F : J → Set の極限は、要素の圏からの射影 Π : ∫F → J の切断を定める関手 J → ∫F の
-- 集合と同型である。

#check @CategoryTheory.Functor.Elements.π

def ex_3_2_vii (F : J ⥤ Type (max w v)) :
    (myLimitCone F).pt ≃ {s : J ⥤ F.Elements // s ⋙ Functor.Elements.π F = 𝟭 J} := sorry
