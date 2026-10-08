import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# 3.1 普遍錐としての極限と余極限

節の数学的な内容は同名の HTML にある。このファイルは本の主張を出現順に並べたもので、主張と
定理群の構成は各セクションの冒頭に、形式化の判断は下の表に、Mathlib の対応物と包装は各
statement の直前の `#check`・`#print` にある。

形式化の判断:
  添字圏の      本の脚注1のとおり、J を小圏、C を局所小に取る。J の対象と C の hom を同じ
  大きさ        universe `v` に置くと、錐の集合 Cone(c, F) が C の hom と同じ `Type v` に
                落ち、Cone(−, F) を `Cᵒᵖ ⥤ Type v` の関手として `ULift` なしに書ける。
                Mathlib の対応物 `IsLimit.natIso` は一般の universe のために
                `uliftFunctor` を挟んでいるので、そこだけ形が違う
  この節の定義  定数関手・錐・錐の引き戻し μ·Δf・Cone(−, F)・錐の射・錐の圏は、組んでも
  の自前実装    義務が自動で閉じ、データにも選択の余地がないので `sorry` なしで書き切って
                渡す。いずれも Mathlib とデータの持ち方が一致するので、statement は
                Mathlib のもので述べ、自前実装は他から参照しない
  添字圏の      平行対の圏 • ⇉ • と余スパンの圏 • → • ← • は本の記述どおり帰納型で組む。
  自前実装      合成と圏の公理、および平行対・余スパンをこの圏からの関手と見る部分に義務が
                残るので演習。Mathlib の `WalkingCospan` は `WidePullbackShape WalkingPair`
                の特殊化で持ち方が違うが、statement は Mathlib の `parallelPair`・`cospan`
                で述べる
  定義3.1.2     錐そのものを組む演習はなく、定義の直後の説明（脚の族が錐を定める条件は
                三角形 (3.1.3) の可換性）を演習にする。cocone が Fᵒᵖ 上の錐であるという
                言い換えも同じ
  定義3.1.5     本は極限を「Cone(−, F) の表現」で定義する。Mathlib の `IsLimit` は
                定義3.1.6 側（lift・fac・uniq）の持ち方なので食い違う。本の形を
                `MyLimitRepr`（対象と自然同型 C(−, pt) ≅ Cone(−, F) の組）として自前で
                置く。構造は本の定義の写しなのでフィールドまで書いて渡し、演習になるのは
                「表現から極限錐が定まり、自然同型はその錐の前合成で与えられる」という
                本の直後の主張と、定義3.1.6 との同値
  定義3.1.6     「錐の圏の終対象」は `IsTerminal t` で述べ、Mathlib の `IsLimit t` との
                同値を橋渡しの演習にする。以後の statement は `IsLimit`・`IsColimit` で
                述べる。本が要素の圏 ∫Cone(−, F) と書く部分は、2.4 を経由せず錐の圏で
                直接扱う
  定義3.1.5 と  「命題2.4.8 を適用して」の一文を、`MyLimitRepr` から `IsLimit` を出す
  3.1.6 の同値  方向と、`IsLimit` から `MyLimitRepr` を出す方向の 2 本に割る。前者は自前
                定義を参照するが、Mathlib の対応物 `IsLimit.OfNatIso.limitCone` は表現を
                2.1 の `RepresentableBy`（hom の全単射の族）で受け取り、自然同型で受け
                取る形を持たないので許容する
  命題3.1.7     一意な同型を「同型の構成」「脚との可換性」「一意性」の 3 本に割る。
                Mathlib は構成と可換性を持ち、一意性そのものに対応する宣言はない
  定義3.1.9 〜  特別な形の極限は、本の記述に沿って「その形の錐は〜のデータに尽きる」と
  3.1.15、      「普遍性は〜」の 2 本ずつ置く。前者は錐（頂点を固定した自然変換）と
  3.1.23        データの全単射、後者は極限錐についての hom の全単射または一意存在。
                Mathlib は前者を `Fan.mk`・`Fork.ofι`・`PullbackCone.mk` のような片方向の
                構成としてしか持たない
  定義3.1.11    Mathlib は終対象を空図式の極限 `IsLimit (asEmptyCone X)` として定義して
                いるので、本の定義3.1.11 は Mathlib の定義そのもの。演習は定義1.6.14 の
                形（各対象からの射が一意）との橋渡し
  演習3.1.iii   本は「同型」と言うが、Mathlib は圏の同値 `≌` で持つのでそれに合わせる
  演習3.1.vi    引き戻しの四角形を Mathlib の `IsPullback`（可換性と極限性の組）で述べる。
                cone で述べると 3 つの四角形それぞれに `PullbackCone.mk` が要る
  演習3.1.vii   問題の主役である錐（F(X) を頂点とし、X からの一意な射の像を脚とする）を
                組むのを `myConeOfDiagramInitial` で演習にし、極限錐であることの statement
                は Mathlib の `coneOfDiagramInitial` で述べる
  演習3.1.ix    本は零対象を仮定する。Mathlib の対応物は零射を仮定し、余積の包含
                `Sigma.ι` について述べる
  本にない      次は本に対応する概念がなく、Mathlib の道具として statement に使う。
  Mathlib の    `Fan`・`Cofan`・`Fork`・`Cofork`・`PullbackCone`・`PushoutCocone`（特定の
  道具          形の図式上の錐の略記と、その脚の名前）、`Discrete.functor`（対象の族を
                離散圏上の図式と見る）、`Functor.empty`・`asEmptyCone`・`asEmptyCocone`
                （空図式とその上の錐）、`Cone.whisker`（添字の付け替え。演習3.1.xii）、
                `CostructuredArrow`・`StructuredArrow`（一点圏からの関手とのコンマ圏。
                演習3.1.iii）、`Cat.Hom`・`Functor.toCatHom`（`Cat` の射は関手を包む
                構造。演習3.1.x）

statement を置かない節末問題:
  3.1.i    poset での極限・余極限を特徴づける問題で、答えの形（下限・上限）が statement に
           出る
  3.1.ii   命題3.1.7 と statement が同じ。Lean では証明法の違いを分けて出題できない
  3.1.vii  後半（後続順序数で添字づけられた図式の余極限を記述する）は答えの形が出る。
           前半のみ置く
  3.1.viii 例3.1.19 の引き戻しについての問題で、Ab の射 n : ℤ → ℤ を組むところから
           になり形式化が不自然。後半は説明問題
  3.1.ix   後半（他の文脈への拡張）は説明問題。前半のみ置く
  3.1.x    後半（添字づけられた圏の族の積を定義する）は、成分ごとの定義を書くだけで
           義務が自動で閉じ、演習にならない。前半のみ置く
  3.1.xi   余積を記述する問題で、答えの形が出る

本文中の例（例3.1.10・3.1.12・3.1.14・3.1.18・3.1.19・3.1.22・3.1.24・3.1.25・3.1.26）と、
定義3.1.2 の直後の (ℤ, ≤) 添字の例、定義3.1.15 の末尾のファイバー (3.1.17) の命名は載せない。
定義3.1.21（逆極限）と定義3.1.23 の列余極限は形に名前を与えるだけなので宣言を置かず、
定義3.1.21 にある錐の記述（(ω + 𝟙)ᵒᵖ 型図式への延長）も、関手の制限の一致を等式で書く
ことになり形式化が不自然なので載せない。注意3.1.8 に対応する Mathlib の圏は `WithInitial`・
`WithTerminal`。注意3.1.27 に対応する Mathlib の宣言は `Limits.Sigma.desc`・`Limits.Pi.lift`
と、直和の行列表示 `Limits.biproduct.matrix`。

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Limits/Cones.lean`（`Cone`・`Cocone`・`Functor.cones`・
    `Cone.extend`・`Cone.whisker`・`coconeEquivalenceOpConeOp`）
  - `Mathlib/CategoryTheory/Limits/IsLimit.lean`（`IsLimit`・`IsColimit`・`IsLimit.natIso`・
    `IsLimit.OfNatIso.limitCone`・`IsLimit.conePointUniqueUpToIso`・`IsLimit.hom_ext`・
    `IsLimit.whiskerEquivalence`）
  - `Mathlib/CategoryTheory/Limits/ConeCategory.lean`（`Cone.isLimitEquivIsTerminal`・
    `Cone.equivCostructuredArrow`）
  - `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean`（`IsTerminal`・
    `isTerminalEquivUnique`・`limitOfDiagramInitial`）
  - `Mathlib/CategoryTheory/Limits/Shapes/Products.lean`（`Fan`・`Cofan`・`Fan.IsLimit.lift`）
  - `Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean`（`WalkingParallelPair`・
    `parallelPair`・`Fork`・`Cofork`・`Fork.IsLimit.existsUnique`・`mono_of_isLimit_fork`）
  - `Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean`（`PullbackCone`・
    `PushoutCocone`）、`Pullback/Mono.lean`、`Pullback/IsPullback/Basic.lean`
  - `Mathlib/CategoryTheory/Limits/Shapes/WidePullbacks.lean`（`WalkingCospan`・`cospan`）
  - `Mathlib/CategoryTheory/Limits/Shapes/ZeroMorphisms.lean`（`isSplitMono_sigma_ι`）
  - `Mathlib/CategoryTheory/Monoidal/Cartesian/Cat.lean`（`Cat.prodCone`）
-/

open CategoryTheory Opposite Limits

universe v u

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定数図式関手 Δ : C → C^J は、対象 c を定数関手 Δc に、射 f を定数自然変換 Δf に送る。

#check @CategoryTheory.Functor.const

def myConst : C ⥤ J ⥤ C where
  obj X :=
    { obj := fun _ => X
      map := fun _ => 𝟙 X }
  map {X Y} f := { app := fun _ => f }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
頂点 c を持つ F 上の錐とは自然変換 Δc ⇒ F で、その成分が脚である。射の族 (λ_j : c → Fj)_j が
F 上の錐を定めるための必要十分条件は、J の各射 f : j → k について三角形 (3.1.3) が可換な
ことである。双対に、頂点 c を持つ F 下の錐とは自然変換 F ⇒ Δc で、族 (λ_j : Fj → c)_j が
F 下の錐を定める条件は裏返した三角形の可換性である。F 下の錐は Fᵒᵖ 上の錐にほかならない。

構成: 錐と下の錐を組む。錐の脚が三角形を可換にすることと、三角形を可換にする族から錐を
      組めることを、上の錐と下の錐それぞれについて示し、下の錐と Fᵒᵖ 上の錐の全単射を
      組む。
-/

#check @CategoryTheory.Limits.Cone

structure MyCone (F : J ⥤ C) where
  pt : C
  π : (Functor.const J).obj pt ⟶ F

#check @CategoryTheory.Limits.Cocone

structure MyCocone (F : J ⥤ C) where
  pt : C
  ι : F ⟶ (Functor.const J).obj pt

#check @CategoryTheory.Limits.Cone.w

theorem def_3_1_2_w {F : J ⥤ C} (t : Cone F) {j k : J} (f : j ⟶ k) :
    t.π.app j ≫ F.map f = t.π.app k := sorry

def def_3_1_2_ofLegs {F : J ⥤ C} (c : C) (lam : ∀ j, c ⟶ F.obj j)
    (w : ∀ {j k : J} (f : j ⟶ k), lam j ≫ F.map f = lam k) : Cone F where
  pt := c
  π :=
    { app := lam
      naturality := sorry }

#check @CategoryTheory.Limits.Cocone.w

theorem def_3_1_2_cocone_w {F : J ⥤ C} (t : Cocone F) {j k : J} (f : j ⟶ k) :
    F.map f ≫ t.ι.app k = t.ι.app j := sorry

def def_3_1_2_cocone_ofLegs {F : J ⥤ C} (c : C) (lam : ∀ j, F.obj j ⟶ c)
    (w : ∀ {j k : J} (f : j ⟶ k), F.map f ≫ lam k = lam j) : Cocone F where
  pt := c
  ι :=
    { app := lam
      naturality := sorry }

#check @CategoryTheory.Limits.coconeEquivalenceOpConeOp

def def_3_1_2_cocone_equiv_cone_op (F : J ⥤ C) : Cocone F ≃ Cone F.op := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.5（極限と余極限 I）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
関手 Cone(−, F) = Hom(Δ(−), F) : Cᵒᵖ → Set は、c を頂点 c の F 上の錐の集合に送り、射 f を
錐 μ を μ·Δf に変える関数に送る。F の極限とはこの関手の表現である。米田の補題により、
極限は対象 lim F と、自然同型 C(−, lim F) ≅ Cone(−, F) を定める普遍的な錐（極限錐）の組から
なる。双対に、余極限とは Cone(F, −) = Hom(F, Δ(−)) の表現で、対象 colim F と自然同型
C(colim F, −) ≅ Cone(F, −) を定める余極限錐の組からなる。

構成: 関手 Cone(−, F) と Cone(F, −)、錐の引き戻し μ·Δf を組み、表現を定義する。表現から
      極限錐を取り出し、表現の与える自然同型が、その錐の引き戻しに一致することを示す。
      余極限側も同様。
-/

#check @CategoryTheory.Functor.cones

def myCones (F : J ⥤ C) : Cᵒᵖ ⥤ Type v := (Functor.const J).op ⋙ yoneda.obj F

#check @CategoryTheory.Functor.cocones

def myCocones (F : J ⥤ C) : C ⥤ Type v := Functor.const J ⋙ coyoneda.obj (op F)

#check @CategoryTheory.Limits.Cone.extend

def myConeExtend {F : J ⥤ C} (c : Cone F) {X : C} (f : X ⟶ c.pt) : Cone F where
  pt := X
  π := (Functor.const J).map f ≫ c.π

#check @CategoryTheory.Limits.Cocone.extend

def myCoconeExtend {F : J ⥤ C} (c : Cocone F) {X : C} (f : c.pt ⟶ X) : Cocone F where
  pt := X
  ι := c.ι ≫ (Functor.const J).map f

structure MyLimitRepr (F : J ⥤ C) where
  pt : C
  iso : yoneda.obj pt ≅ F.cones

#check @CategoryTheory.Limits.IsLimit.OfNatIso.limitCone

def myLimitConeOfRepr {F : J ⥤ C} (L : MyLimitRepr F) : Cone F where
  pt := L.pt
  π := sorry

#check @CategoryTheory.Limits.IsLimit.OfNatIso.cone_fac

theorem def_3_1_5_iso_app {F : J ⥤ C} (L : MyLimitRepr F) {c : C} (g : c ⟶ L.pt) :
    L.iso.hom.app (op c) g = ((myLimitConeOfRepr L).extend g).π := sorry

structure MyColimitRepr (F : J ⥤ C) where
  pt : C
  iso : coyoneda.obj (op pt) ≅ F.cocones

#check @CategoryTheory.Limits.IsColimit.OfNatIso.colimitCocone

def myColimitCoconeOfRepr {F : J ⥤ C} (L : MyColimitRepr F) : Cocone F where
  pt := L.pt
  ι := sorry

#check @CategoryTheory.Limits.IsColimit.OfNatIso.cocone_fac

theorem def_3_1_5_dual_iso_app {F : J ⥤ C} (L : MyColimitRepr F) {c : C} (g : L.pt ⟶ c) :
    L.iso.hom.app c g = ((myColimitCoconeOfRepr L).extend g).ι := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.6（極限と余極限 II）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
F 上の錐の圏は、錐を対象、頂点の射 f : c → d で各脚が μ_j·f = λ_j と分解するものを射とする
圏である。極限とはこの圏の終対象であり、この定義は定義3.1.5 と同値である。双対に、
余極限とは F 下の錐の圏の始対象である。

構成: 錐の射と錐の圏を組む。錐の圏の終対象であることと Mathlib の `IsLimit` の同値、
      Cone(−, F) の表現から `IsLimit` を出すこと、`IsLimit` から Cone(−, F) の表現を
      出すことを示す。余極限側も同様。
-/

#check @CategoryTheory.Limits.ConeMorphism

structure MyConeMorphism {F : J ⥤ C} (A B : Cone F) where
  hom : A.pt ⟶ B.pt
  w (j : J) : hom ≫ B.π.app j = A.π.app j := by cat_disch

attribute [reassoc (attr := simp)] MyConeMorphism.w

#check @CategoryTheory.Limits.Cone.category

@[instance_reducible]
def myConeCategory (F : J ⥤ C) : Category (Cone F) where
  Hom A B := MyConeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

#print CategoryTheory.Limits.IsLimit
#check @CategoryTheory.Limits.Cone.isLimitEquivIsTerminal

def def_3_1_6 {F : J ⥤ C} (t : Cone F) : IsTerminal t ≃ IsLimit t := sorry

def def_3_1_6_of_repr {F : J ⥤ C} (L : MyLimitRepr F) : IsLimit (myLimitConeOfRepr L) := sorry

#check @CategoryTheory.Limits.IsLimit.natIso

def def_3_1_5_of_isLimit {F : J ⥤ C} {t : Cone F} (h : IsLimit t) : MyLimitRepr F where
  pt := t.pt
  iso := sorry

#print CategoryTheory.Limits.IsColimit
#check @CategoryTheory.Limits.Cocone.isColimitEquivIsInitial

def def_3_1_6_dual {F : J ⥤ C} (t : Cocone F) : IsInitial t ≃ IsColimit t := sorry

def def_3_1_6_dual_of_repr {F : J ⥤ C} (L : MyColimitRepr F) :
    IsColimit (myColimitCoconeOfRepr L) := sorry

#check @CategoryTheory.Limits.IsColimit.natIso

def def_3_1_5_dual_of_isColimit {F : J ⥤ C} {t : Cocone F} (h : IsColimit t) :
    MyColimitRepr F where
  pt := t.pt
  iso := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.1.7（極限の本質的一意性）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
共通の図式上の二つの極限錐の頂点の間には、脚と可換な同型がただ一つ存在する。極限錐を
自己同型で引き戻したものも極限錐だが、指定された極限錐と可換な自己同型は恒等射だけである。

構成: 同型を構成し、それが脚と可換なことと、脚と可換な同型がそれに限ることを示す。
      さらに極限錐を同型で引き戻したものが極限錐であることと、極限錐と可換な自己同型が
      恒等射であることを示す。
-/

#check @CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso

def prop_3_1_7_iso {F : J ⥤ C} {s t : Cone F} (hs : IsLimit s) (ht : IsLimit t) :
    s.pt ≅ t.pt := sorry

#check @CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp

theorem prop_3_1_7_hom_comp {F : J ⥤ C} {s t : Cone F} (hs : IsLimit s) (ht : IsLimit t)
    (j : J) : (prop_3_1_7_iso hs ht).hom ≫ t.π.app j = s.π.app j := sorry

theorem prop_3_1_7_unique {F : J ⥤ C} {s t : Cone F} (hs : IsLimit s) (ht : IsLimit t)
    (φ : s.pt ≅ t.pt) (w : ∀ j, φ.hom ≫ t.π.app j = s.π.app j) :
    φ = prop_3_1_7_iso hs ht := sorry

#check @CategoryTheory.Limits.IsLimit.extendIso

def prop_3_1_7_extend {F : J ⥤ C} {t : Cone F} (ht : IsLimit t) {X : C} (f : X ≅ t.pt) :
    IsLimit (t.extend f.hom) := sorry

theorem prop_3_1_7_aut {F : J ⥤ C} {t : Cone F} (ht : IsLimit t) (φ : t.pt ≅ t.pt)
    (w : ∀ j, φ.hom ≫ t.π.app j = t.π.app j) : φ = Iso.refl t.pt := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.9（積）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
積とは離散圏で添字づけられた図式の極限である。この図式上の錐は、添字づけられた射の族
そのもので、それ以上の制約を持たない。積の普遍性は、射影との合成が全単射
C(c, ∏ Fj) ≅ ∏ C(c, Fk) を定めることである。

構成: 頂点 c の錐と射の族の全単射を組み、極限錐について、射影との合成が全単射である
      ことを示す。
-/

#check @CategoryTheory.Discrete.functor
#check @CategoryTheory.Discrete.natTrans

def def_3_1_9_cone_equiv {β : Type v} (f : β → C) (c : C) :
    ((Functor.const (Discrete β)).obj c ⟶ Discrete.functor f) ≃ ∀ b, c ⟶ f b := sorry

#check @CategoryTheory.Limits.Fan
#check @CategoryTheory.Limits.Fan.proj
#check @CategoryTheory.Limits.Fan.IsLimit.lift

def def_3_1_9_univ {β : Type v} {f : β → C} {t : Fan f} (ht : IsLimit t) (c : C) :
    (c ⟶ t.pt) ≃ ∀ b, c ⟶ f b where
  toFun g b := g ≫ t.proj b
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.11（終対象）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
終対象は添字圏が空である積の特別な場合である。空図式上の錐の圏は C 自身と同型であり、
空図式の極限とは定義1.6.14 の意味での終対象にほかならない。

構成: 空図式上の錐の圏と C の同値を組み、空図式上の錐が極限錐であることと、各対象からの
      射が一意であることの同値を示す。
-/

#check @CategoryTheory.Functor.empty

def def_3_1_11_cones (C : Type u) [Category.{v} C] : Cone (Functor.empty.{0} C) ≌ C := sorry

#check @CategoryTheory.Limits.asEmptyCone
#print CategoryTheory.Limits.IsTerminal
#check @CategoryTheory.Limits.isTerminalEquivUnique

def def_3_1_11 (X : C) : IsTerminal X ≃ ∀ Y : C, Unique (Y ⟶ X) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.13（等化子）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
等化子とは、対象 2 つと平行な非恒等射 2 本を持つ平行対の圏 • ⇉ • で添字づけられた図式の
極限である。この形の図式は平行な射の対 f, g : A ⇉ B にすぎない。平行対上の錐は、fa = ga を
満たす一本の射 a : C → A で代表される。等化子 h : E → A の普遍性は、fa = ga を満たす任意の
a が h を通してただ一通りに分解することである。

構成: 平行対の圏と、平行対をそこからの関手と見る図式を組む。頂点 C の錐と、fa = ga を
      満たす射 a の全単射を組み、極限錐について分解の一意存在を示す。
-/

#check @CategoryTheory.Limits.WalkingParallelPair

inductive MyWalkingParallelPair : Type
  | zero
  | one

#check @CategoryTheory.Limits.WalkingParallelPairHom

inductive MyWalkingParallelPairHom : MyWalkingParallelPair → MyWalkingParallelPair → Type
  | left : MyWalkingParallelPairHom .zero .one
  | right : MyWalkingParallelPairHom .zero .one
  | id (X : MyWalkingParallelPair) : MyWalkingParallelPairHom X X

#check @CategoryTheory.Limits.walkingParallelPairHomCategory

instance myWalkingParallelPairCategory : SmallCategory MyWalkingParallelPair where
  Hom := MyWalkingParallelPairHom
  id := MyWalkingParallelPairHom.id
  comp := sorry
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

#check @CategoryTheory.Limits.parallelPair

def myParallelPair {X Y : C} (f g : X ⟶ Y) : MyWalkingParallelPair ⥤ C where
  obj x := match x with
    | .zero => X
    | .one => Y
  map := sorry
  map_id := sorry
  map_comp := sorry

#check @CategoryTheory.Limits.Fork.ofι

def def_3_1_13_cone_equiv {X Y : C} (f g : X ⟶ Y) (c : C) :
    ((Functor.const WalkingParallelPair).obj c ⟶ parallelPair f g) ≃
      {a : c ⟶ X // a ≫ f = a ≫ g} := sorry

#check @CategoryTheory.Limits.Fork
#check @CategoryTheory.Limits.Fork.ι
#check @CategoryTheory.Limits.Fork.IsLimit.existsUnique

theorem def_3_1_13_univ {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t) {W : C}
    (a : W ⟶ X) (w : a ≫ f = a ≫ g) : ∃! k : W ⟶ t.pt, k ≫ t.ι = a := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.15（引き戻し）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
引き戻しとは、共通の余域を持つ非恒等射 2 本からなる poset 圏 • → • ← • で添字づけられた
図式（余スパン）の極限である。余スパン B → A ← C 上の錐のデータは、可換な四角形を定める
射の対 B ← D → C に尽きる。引き戻しの普遍性は、任意の可換な四角形の脚が引き戻し錐の頂点を
通してただ一通りに分解することである。

構成: 余スパンの圏と、射の対 f, g をそこからの関手と見る図式を組む。頂点 D の錐と、可換な
      四角形を定める射の対の全単射を組み、極限錐について分解の一意存在を示す。
-/

#check @CategoryTheory.Limits.WalkingCospan

inductive MyWalkingCospan : Type
  | left
  | right
  | one

inductive MyWalkingCospanHom : MyWalkingCospan → MyWalkingCospan → Type
  | inl : MyWalkingCospanHom .left .one
  | inr : MyWalkingCospanHom .right .one
  | id (X : MyWalkingCospan) : MyWalkingCospanHom X X

instance myWalkingCospanCategory : SmallCategory MyWalkingCospan where
  Hom := MyWalkingCospanHom
  id := MyWalkingCospanHom.id
  comp := sorry
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

#check @CategoryTheory.Limits.cospan

def myCospan {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : MyWalkingCospan ⥤ C where
  obj x := match x with
    | .left => X
    | .right => Y
    | .one => Z
  map := sorry
  map_id := sorry
  map_comp := sorry

#check @CategoryTheory.Limits.PullbackCone.mk

def def_3_1_15_cone_equiv {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (d : C) :
    ((Functor.const WalkingCospan).obj d ⟶ cospan f g) ≃
      {p : (d ⟶ X) × (d ⟶ Y) // p.1 ≫ f = p.2 ≫ g} := sorry

#check @CategoryTheory.Limits.PullbackCone
#check @CategoryTheory.Limits.PullbackCone.fst
#check @CategoryTheory.Limits.PullbackCone.snd
#check @CategoryTheory.Limits.PullbackCone.IsLimit.lift

theorem def_3_1_15_univ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : PullbackCone f g}
    (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    ∃! l : W ⟶ t.pt, l ≫ t.fst = h ∧ l ≫ t.snd = k := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.1.23（余積・始対象・余等化子・押し出し）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
定義3.1.9・3.1.11・3.1.13・3.1.15 の双対。余積の普遍性は包含との合成が全単射
C(∐ Aj, X) ≅ ∏ C(Ak, X) を定めること、始対象は空図式の余極限、余等化子 h : B → C は
hf = hg を満たす普遍的な射、押し出しは f と g の下の普遍的な可換四角形である。

構成: 余積の包含との合成が全単射であること、空図式上の下の錐が余極限錐であることと各対象
      への射が一意であることの同値、余等化子と押し出しについて分解の一意存在を示す。
-/

#check @CategoryTheory.Limits.Cofan
#check @CategoryTheory.Limits.Cofan.inj
#check @CategoryTheory.Limits.Cofan.IsColimit.desc

def def_3_1_23_coproduct_univ {β : Type v} {f : β → C} {t : Cofan f} (ht : IsColimit t)
    (X : C) : (t.pt ⟶ X) ≃ ∀ b, f b ⟶ X where
  toFun g b := t.inj b ≫ g
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

#check @CategoryTheory.Limits.asEmptyCocone
#print CategoryTheory.Limits.IsInitial
#check @CategoryTheory.Limits.isInitialEquivUnique

def def_3_1_23_initial (X : C) : IsInitial X ≃ ∀ Y : C, Unique (X ⟶ Y) := sorry

#check @CategoryTheory.Limits.Cofork
#check @CategoryTheory.Limits.Cofork.π
#check @CategoryTheory.Limits.Cofork.IsColimit.existsUnique

theorem def_3_1_23_coequalizer_univ {X Y : C} {f g : X ⟶ Y} {t : Cofork f g}
    (ht : IsColimit t) {W : C} (h : Y ⟶ W) (w : f ≫ h = g ≫ h) :
    ∃! k : t.pt ⟶ W, t.π ≫ k = h := sorry

#check @CategoryTheory.Limits.span
#check @CategoryTheory.Limits.PushoutCocone
#check @CategoryTheory.Limits.PushoutCocone.inl
#check @CategoryTheory.Limits.PushoutCocone.inr
#check @CategoryTheory.Limits.PushoutCocone.IsColimit.desc

theorem def_3_1_23_pushout_univ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {t : PushoutCocone f g}
    (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) :
    ∃! l : t.pt ⟶ W, t.inl ≫ l = h ∧ t.inr ≫ l = k := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.1.28
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
極限対象への平行な射の対が等しいための必要十分条件は、極限錐の脚との合成が等しいことで
ある。双対に、余極限対象からの平行な射の対が等しいための必要十分条件は、余極限錐の脚との
合成が等しいことである。
-/

#check @CategoryTheory.Limits.IsLimit.hom_ext

theorem lemma_3_1_28 {F : J ⥤ C} {t : Cone F} (ht : IsLimit t) {X : C} (f g : X ⟶ t.pt) :
    f = g ↔ ∀ j, f ≫ t.π.app j = g ≫ t.π.app j where
  mp H := by subst H; simp
  mpr H := by
    apply ht.hom_ext; assumption



#check @CategoryTheory.Limits.IsColimit.hom_ext

theorem lemma_3_1_28_dual {F : J ⥤ C} {t : Cocone F} (ht : IsColimit t) {X : C}
    (f g : t.pt ⟶ X) : f = g ↔ ∀ j, t.ι.app j ≫ f = t.ι.app j ≫ g := sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
F 上の錐の圏は、定数関手 Δ : C → C^J と F : 𝟙 → C^J のコンマ圏 Δ ↓ F と同値である。
双対に、F 下の錐の圏はコンマ圏 F ↓ Δ と同値である。
-/

#check @CategoryTheory.CostructuredArrow
#check @CategoryTheory.Limits.Cone.equivCostructuredArrow

def ex_3_1_iii (F : J ⥤ C) : Cone F ≌ CostructuredArrow (Functor.const J) F := sorry

#check @CategoryTheory.StructuredArrow
#check @CategoryTheory.Limits.Cocone.equivStructuredArrow

def ex_3_1_iii_dual (F : J ⥤ C) : Cocone F ≌ StructuredArrow F (Functor.const J) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 等化子図式の h : E → A はモノ射である。

#check @CategoryTheory.Limits.mono_of_isLimit_fork

theorem ex_3_1_iv {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t) : Mono t.ι where
  right_cancellation {Z} h k H := by
    apply ht.hom_ext
    intro j
    cases j with
    | zero => exact H
    | one => simp only [parallelPair_obj_one, Fork.app_one_eq_ι_comp_left]; grind


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.v
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 引き戻しの四角形で f : B → A がモノ射ならば、その向かいの辺 k : P → C もモノ射である。

#check @CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono

theorem ex_3_1_v {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] --{t : PullbackCone f g} (ht : IsLimit t)
    [Mono f] : Mono (pullback.snd f g) where
  right_cancellation {A} h k H := by
    bapply pullback.hom_ext _ H
    apply Mono.right_cancellation (f := f)
    rw [Category.assoc, pullback.condition]
    rw [Category.assoc, pullback.condition]
    rw [<- Category.assoc, H, Category.assoc]




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 右の四角形が引き戻しである可換な長方形について、左の四角形が引き戻しであることと
-- 長方形全体が引き戻しであることは同値である。

#print CategoryTheory.CommSq
#print CategoryTheory.IsPullback
#check @CategoryTheory.IsPullback.paste_horiz_iff

theorem ex_3_1_vi {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} {a₁ : X₁ ⟶ X₂} {a₂ : X₂ ⟶ X₃} {b₁ : X₁ ⟶ Y₁}
    {b₂ : X₂ ⟶ Y₂} {b₃ : X₃ ⟶ Y₃} {c₁ : Y₁ ⟶ Y₂} {c₂ : Y₂ ⟶ Y₃} (w : a₁ ≫ b₂ = b₁ ≫ c₁)
    (hr : IsPullback a₂ b₂ b₃ c₂) :
    IsPullback a₁ b₁ b₂ c₁ ↔ IsPullback (a₁ ≫ a₂) b₁ b₃ (c₁ ≫ c₂) where
  mp H := by
    apply IsPullback.mk'
    · rw [Category.assoc, hr.w, <- Category.assoc, H.w, Category.assoc]
    · intro Z h k E1 E2
      apply H.hom_ext _ E2
      apply hr.hom_ext<;> simp only [Category.assoc]
      · exact E1
      · rw [w, <- Category.assoc, E2, Category.assoc]
    · intro Z h k E
      rw [<- Category.assoc] at E
      have Hl1 :=  hr.lift_fst _ _ E
      have Hl2 := hr.lift_snd _ _ E
      set l := hr.lift _ _ E
      use H.lift l k Hl2
      rw [<- Category.assoc, H.lift_fst _ _ Hl2, Hl1, H.lift_snd _ _ Hl2]
      simp
  mpr H := by
    apply IsPullback.mk' w
    · intro T h k Ha Hb
      apply H.hom_ext _ Hb
      rw [<- Category.assoc, Ha]; simp
    · intro T a b E
      have E' : (a ≫ a₂) ≫ b₃ = b ≫ c₁ ≫ c₂ := by
        rw [Category.assoc, hr.w, <- Category.assoc, E]; simp
      use H.lift (a ≫ a₂) b E'
      rw [H.lift_snd _ _ E']; simp only [and_true]
      apply hr.hom_ext
      · rw [Category.assoc, H.lift_fst _ _ E']
      · rw [Category.assoc, w, <- Category.assoc,  H.lift_snd _ _ E', E]


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.vii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
J が始対象 X を持つならば、J で添字づけられた任意の関手の極限は、その関手の X での値である。

構成: F(X) を頂点とする錐を組み、それが極限錐であることを示す。
-/

#check @CategoryTheory.Limits.coneOfDiagramInitial

def myConeOfDiagramInitial {X : J} (tX : IsInitial X) (F : J ⥤ C) : Cone F where
  pt := F.obj X
  π := {
    app j := F.map (tX.to j)
    naturality {i j} f := by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      rw [<- F.map_comp]
      congr
      apply tX.hom_ext
  }


#check @CategoryTheory.Limits.limitOfDiagramInitial

def ex_3_1_vii {X : J} (tX : IsInitial X) (F : J ⥤ C) : IsLimit (coneOfDiagramInitial tX F) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.ix
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 零対象を持つ圏では、余積錐の脚は分裂モノ射である。

#check @CategoryTheory.Limits.isSplitMono_sigma_ι
#check Limits.coprod
#check Limits.HasCoproduct
#check

theorem ex_3_1_ix [DecidableEq C] (z : C) (Hz : IsZero z) {β : Type v} {f : β → C} [HasCoproduct f] (b : β) --{t : Cofan f} (ht : IsColimit t)
    -- (b : β) : IsSplitMono (t.inj b) := sorry
    : IsSplitMono (Sigma.ι f b)
:= sorry




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.x
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義1.3.12 の圏の積は、射影関手を脚として、圏の圏における積である。

#print CategoryTheory.Cat.Hom
#check @CategoryTheory.Functor.toCatHom
#check @CategoryTheory.Cat.isLimitProdCone

def ex_3_1_x (A B : Cat.{v, u}) :
    IsLimit (BinaryFan.mk (P := Cat.of (A × B)) (CategoryTheory.Prod.fst A B).toCatHom
      (CategoryTheory.Prod.snd A B).toCatHom) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.1.xii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
E : I ≃ J が小圏の間の同値なら、F 上の J 型の錐の圏は FE 上の I 型の錐の圏と同値であり、
F の極限錐は E で添字を付け替えると FE の極限錐になり、その逆も成り立つ。

構成: 錐の圏の同値を組み、極限錐の付け替えが極限錐であることと、付け替えが極限錐なら
      元も極限錐であることを示す。
-/

#check @CategoryTheory.Limits.Cone.whisker
#check @CategoryTheory.Limits.Cone.whiskeringEquivalence

def ex_3_1_xii_cones {I : Type v} [SmallCategory I] (E : I ≌ J) (F : J ⥤ C) :
    Cone F ≌ Cone (E.functor ⋙ F) := sorry

#check @CategoryTheory.Limits.IsLimit.whiskerEquivalence

def ex_3_1_xii_isLimit {I : Type v} [SmallCategory I] (E : I ≌ J) {F : J ⥤ C} {t : Cone F}
    (ht : IsLimit t) : IsLimit (t.whisker E.functor) := sorry

#check @CategoryTheory.Limits.IsLimit.ofWhiskerEquivalence

def ex_3_1_xii_isLimit_of {I : Type v} [SmallCategory I] (E : I ≌ J) {F : J ⥤ C} {t : Cone F}
    (ht : IsLimit (t.whisker E.functor)) : IsLimit t := sorry
