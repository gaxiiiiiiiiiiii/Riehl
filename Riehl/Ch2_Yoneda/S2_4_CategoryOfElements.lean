import Mathlib.CategoryTheory.Limits.Elements
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Order.Defs.Unbundled
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# 2.4 要素の圏

節の数学的な内容は同名の HTML にある。このファイルは本の主張を出現順に並べたもので、主張と
定理群の構成は各セクションの冒頭に、形式化の判断は下の表に、Mathlib の対応物は各
statement の直前の `#check` にある。

形式化の判断:
  Set 値関手   hom 集合と同じ universe に値を取る関手として書く。本が圏に課す locally
               small の仮定が、この universe の一致にあたる
  定義2.4.1    圏として組むところに、恒等射と合成が要素の条件を保つという証明義務がある
               （F の関手性を使う）。data を書いて義務だけ `sorry` にした形で置く
  射影 Π       義務は自動で閉じるが、共変・反変のどちらでも C へ共変に落ちるという定義
               2.4.2 の規約がこの型に現れるので、両方に演習として置く
  定義2.4.2    Mathlib の `Functor.Elements` は共変関手にしか定義されない。本の反変版 ∫F に
               あたるのは `F.Elementsᵒᵖ`、その射影は `(π F).leftOp` で、以降の statement は
               この形で述べる。反変側の `#check` が指す Mathlib の宣言は、いずれも本の ∫F の
               反対圏についてのものになる
  持ち方の一致 Mathlib の `Functor.Elements` は対象が `Σ c, F.obj c`、射が
               `{f // F.map f x = y}` で本の定義2.4.1 と一致するので、statement は Mathlib の
               ものを使う。組むこと自体は上記のとおり演習に残す
  同型と同値   本は「圏の同型」と述べるが、Mathlib の対応物（`structuredArrowEquivalence`・
               `costructuredArrowYonedaEquivalence`）は `≌` なので `≌` で述べる。命題2.4.14 と
               演習2.4.viii の「C 上で」だけは、射影との両立を関手の等式で述べる
  補題2.4.7    射影との両立は、Mathlib の `...FunctorProj` が Mathlib の同値について述べるのと
               同じ形で、この演習の `lemma_2_4_7` について述べる
  命題2.4.8    本は共変・反変の両方を述べるが、反変側は演習2.4.iv が双対性で導くよう指示して
               いるので、そちらに置く
  可縮亜群     本が 1.6 の地の文で与える定義。「終圏と同値」と「空でなく、どの hom 集合も
               ちょうど1元」の2つの言い方のうち、後者を定義に採る。Mathlib に対応物なし
               （`Quiver.IsThin` は「高々1本」の部分だけ）
  補題1.6.16   命題2.4.9 が引く 1.6 の補題。節としては対象範囲の外だが、2.4.9 を本の形で
               述べるのに要るので、2.4.9 の直前に演習として置く。Mathlib に対応物なし
  命題2.4.9    本の主張のまま「表現たちが張る充満部分圏は空か可縮亜群」を1本で述べる。
               「表現である」は命題2.4.8 と同じ語彙で書き、始対象には言い換えない。充満部分圏
               は `ObjectProperty.FullSubcategory` で取る
  定数関手     どんな圏も定数関手の要素の圏として現れるという地の文の主張。Mathlib に対応物
               なし
  持ち上げ     c の持ち上げ全体と、射が f の持ち上げであることは、本がこの節で導入する語。
               自前実装を演習として置き、以降の主張は Mathlib の `Functor.Fiber`・
               `Functor.IsHomLift` で述べる
  定義2.4.13   本が「ただ一つ存在する」と述べるので、持ち上げの対象と射をフィールドで持ち、
               一意性を別のフィールドに置く。データを持つので `Prop` ではない。一意性は
               「余域（右では域）と射の対が一致する」という Σ 型上の等式で述べる。対象の
               等式と射の等式を分けて書くと、後者が要素の圏の hom の中で eqToHom を運ぶ形に
               なり、`Functor.Elements` が `Σ` 上の `def` であるために書き換えが通らない。
               Mathlib に対応物なし（Grothendieck ファイブレーションはあるが離散版はない）
               ので `#check` も置かない
  命題2.4.14   充満忠実性は演習2.4.viii に委ねられているので、ここには射影が離散左（右）
               ファイブレーションであることと、逆向きの構成を置く。
               `myFunctorOfLeftFibration` は構成そのものが中身なので丸ごと `sorry`。
               この構成に対応する Mathlib の宣言がないため、続く2本はこの自前定義を参照する
  演習2.4.i    Mathlib は反変版の `costructuredArrowYonedaEquivalence` だけを持ち、共変関手に
               ついての形に対応物なし
  演習2.4.ii   本文が「similar result」としか言わない反変版は、本の ∫F = `F.Elementsᵒᵖ` に
               合わせて `(StructuredArrow PUnit F)ᵒᵖ` との同値で述べる
  演習2.4.vi   前順序の集合への対応（obj）は書いて渡し、引き戻し（map）と関手性を残す。
               Mathlib に対応物なし
  演習2.4.viii Mathlib は ∫(−) を `Functor.elementsFunctor : (C ⥤ Type w) ⥤ Cat` として持つが
               充満忠実性の宣言はなく、そこから出る同型の判定にも対応物がない。CAT/C への
               関手としての充満忠実性を「C 上の関手 K ごとに ∫α = K となる α がただ一つ」と
               いう形で述べる。この ∫α にあたるのが最初の `ex_2_4_viii_map` で、続く2本は
               それを参照する
  対応物なし   Mathlib に対応物がなく `#check` を置かない宣言は、可縮亜群の定義、補題1.6.16 の
               2本、命題2.4.9 の2本、定数関手の2本、定義2.4.13 のファイブレーション2本、
               命題2.4.14 の5本、
               演習2.4.i、演習2.4.vi、`ex_2_4_viii_iso_iff`、演習2.4.ix の2本

statement を置かない節末問題:
  2.4.iii  c/C の始対象と C/c の終対象を特徴づける問題で、条件の形そのものが答えになる
  2.4.v    説明問題。シェルピンスキー空間と普遍要素を statement に書くと、どの意味で普遍かの
           答えがそのまま出る
  2.4.vi   後半（要素の圏の記述と表現可能性の判定）。記述と可否がそのまま答えになる
  2.4.vii  twisted arrow category の対象と射を記述する問題で、記述が答え。Mathlib にも
           対応物なし

本文中の例（例2.4.3・2.4.4・2.4.5・2.4.6・2.4.10・2.4.11・2.4.12）は載せない。節の締めに置かれた
問い（C(A,−) × C(B,−) が表現可能であるとはどういうことか）も、主張ではなく問いなので置かない。

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Elements.lean`（`Functor.Elements`・`Functor.elementsMk`・
    `categoryOfElements`・`CategoryOfElements.π`・`map`・`map_π`・
    `structuredArrowEquivalence`・`costructuredArrowYonedaEquivalence`・
    `Functor.elementsFunctor`）
  - `Mathlib/CategoryTheory/Limits/Elements.lean`（`Functor.Elements.isInitialOfCorepresentableBy`・
    `corepresentableByOfIsInitial`・`hasInitial_iff_isCorepresentable`・その反変版）
  - `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean`（`IsInitial`・`IsTerminal`・
    `IsInitial.hom_ext`・`IsInitial.uniqueUpToIso`）
  - `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean`（`ObjectProperty`・
    `FullSubcategory`）
  - `Mathlib/CategoryTheory/Comma/Basic.lean`（`Comma`・`CommaMorphism`）
  - `Mathlib/CategoryTheory/Comma/StructuredArrow/Basic.lean`（`StructuredArrow`・
    `CostructuredArrow`・`CostructuredArrow.proj`）
  - `Mathlib/CategoryTheory/Yoneda.lean`（`yoneda`・`coyoneda`・`RepresentableBy`・
    `CorepresentableBy`）
  - `Mathlib/CategoryTheory/FiberedCategory/Fiber.lean`（`Functor.Fiber`）
  - `Mathlib/CategoryTheory/FiberedCategory/HomLift.lean`（`Functor.IsHomLift`）
  - `Mathlib/Order/Defs/Unbundled.lean`（`IsPreorder`）
-/

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

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

-- 定義2.1.4 の表現。Mathlib は自然同型ではなく hom の全単射の族と合成との両立で持つ
structure RepresentableBy (F : Cᵒᵖ ⥤ Type v₁) (Y : C) where
  homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X)
  homEquiv_comp {X X' : C} (g : X ⟶ X') (f : X' ⟶ Y) :
    homEquiv (g ≫ f) = F.map g.op (homEquiv f)

-- その共変版。自然同型 C(X,−) ≅ F にあたる
structure CorepresentableBy (F : C ⥤ Type v₁) (X : C) where
  homEquiv {Y : C} : (X ⟶ Y) ≃ F.obj Y
  homEquiv_comp {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    homEquiv (f ≫ g) = F.map g (homEquiv f)

-- 定義2.1.4(ii) の表現可能性。表現のデータが存在すること
class IsRepresentable (F : Cᵒᵖ ⥤ Type v₁) : Prop where
  has_representation : ∃ Y : C, Nonempty (RepresentableBy F Y)

-- その共変版
class IsCorepresentable (F : C ⥤ Type v₁) : Prop where
  has_corepresentation : ∃ X : C, Nonempty (CorepresentableBy F X)

-- 定義1.6.14 の始対象。Mathlib は空図式の余極限として持ち、`IsInitial.to` で射を取り出す
abbrev IsInitial (X : C) := Limits.IsColimit (Limits.asEmptyCocone X)

-- 同じく終対象
abbrev IsTerminal (X : C) := Limits.IsLimit (Limits.asEmptyCone X)

-- 始対象の存在。Mathlib は空図式の余極限の存在として持つ
abbrev HasInitial (C : Type u₁) [Category.{v₁} C] :=
  Limits.HasColimitsOfShape (Discrete.{0} PEmpty) C

-- 終対象の存在
abbrev HasTerminal (C : Type u₁) [Category.{v₁} C] :=
  Limits.HasLimitsOfShape (Discrete.{0} PEmpty) C

-- 演習1.3.vi のコンマ圏。対象は3つ組 (a, b, f : La ⟶ Rb)
structure Comma {A B T : Type*} [Category* A] [Category* B] [Category* T]
    (L : A ⥤ T) (R : B ⥤ T) where
  left : A
  right : B
  hom : L.obj left ⟶ R.obj right

-- コンマ圏の射。両側の射の組であって、四角形を可換にするもの
structure CommaMorphism {A B T : Type*} [Category* A] [Category* B] [Category* T]
    {L : A ⥤ T} {R : B ⥤ T} (X Y : Comma L R) where
  left : X.left ⟶ Y.left
  right : X.right ⟶ Y.right
  w : L.map left ≫ Y.hom = X.hom ≫ R.map right

-- ∗ ↓ F にあたるコンマ圏。左を終圏からの関手に取り、対象 S を1つ選ぶ
abbrev StructuredArrow {C D : Type*} [Category* C] [Category* D] (S : D) (T : C ⥤ D) :=
  Comma (Functor.fromPUnit.{0} S) T

-- よ ↓ F にあたるコンマ圏。右を終圏からの関手に取り、対象 T を1つ選ぶ
abbrev CostructuredArrow {C D : Type*} [Category* C] [Category* D] (S : C ⥤ D) (T : D) :=
  Comma S (Functor.fromPUnit.{0} T)

end Recap

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義2.4.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
共変関手 F : C ⥤ Set の要素の圏 ∫F は、対象を F の要素 (c, x)、(c,x) から (c',x') への射を
Ff(x) = x' を満たす f : c ⟶ c' とする圏であり、C への忘却関手 Π をもつ。

構成: 要素の型に圏構造を与え、忘却関手 Π を構成する。
-/

#check @CategoryTheory.Functor.Elements

structure Elm

def myElements (F : C ⥤ Type v₁) := Σ c : C, F.obj c

#check @CategoryTheory.categoryOfElements

instance myCategoryOfElements (F : C ⥤ Type v₁) : Category.{v₁} (myElements F) where
  Hom p q := { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := {
    val := 𝟙 p.1
    property := by simp
  }
  comp {X Y Z} f g := {
    val := f.val ≫ g.val
    property := by rw [F.map_comp, comp_apply, f.prop, g.prop]
  }
  id_comp {X Y} f := by ext; dsimp only; rw [Category.id_comp]
  comp_id {X Y} f := by ext; simp
  assoc {W X Y Z} f g h := by ext; simp

#check @CategoryTheory.CategoryOfElements.π

def myπ (F : C ⥤ Type v₁) : myElements F ⥤ C where
  obj c := c.fst
  map {x y} f := f.val


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義2.4.2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
反変関手 F : Cᵒᵖ ⥤ Set の要素の圏 ∫F は、(c,x) から (c',x') への射を Ff(x') = x を満たす
f : c ⟶ c' とする圏である。忘却関手 Π : ∫F ⥤ C はこの向きでも共変になる。

構成: 反変版の要素の型に圏構造を与え、忘却関手 Π を構成する。
-/

#check @CategoryTheory.Functor.Elements

def myElementsContra (F : Cᵒᵖ ⥤ Type v₁) := Σ c : C, F.obj (op c)

#check @CategoryTheory.categoryOfElements

instance myCategoryOfElementsContra (F : Cᵒᵖ ⥤ Type v₁) :
    Category.{v₁} (myElementsContra F) where
  Hom p q := { f : p.1 ⟶ q.1 // (F.map f.op) q.2 = p.2 }
  id p := ⟨𝟙 p.1, sorry⟩
  comp f g := ⟨f.val ≫ g.val, sorry⟩
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

#check @CategoryTheory.CategoryOfElements.π

def myπContra (F : Cᵒᵖ ⥤ Type v₁) : myElementsContra F ⥤ C := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題2.4.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
反変関手 F の要素の圏は、米田埋め込み よ と対象 F : 1 ⥤ Set^(Cᵒᵖ) に関するコンマ圏 よ↓F と
同型であり、この同型は C への射影と両立する。

構成: 両者の同値を構成し、それが射影と両立することを示す。
-/

#check @CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence

namespace Lemma_2_4_7

-- 順方向の対象成分: 要素 c に対応する自然変換 よ(c) ⟶ F
@[simps]
def hom (F : Cᵒᵖ ⥤ Type v₁) (c : F.Elementsᵒᵖ) :
    yoneda.obj c.unop.fst.unop ⟶ F where
  app x := by
    apply TypeCat.ofHom
    intro g
    exact ConcreteCategory.hom (F.map g.op) c.unop.snd
  naturality {X Y} f := by
    ext g; simp

-- 順方向 (∫F)ᵒᵖ ⥤ よ↓F
@[simps]
def functor (F : Cᵒᵖ ⥤ Type v₁) :
    F.Elementsᵒᵖ ⥤ CostructuredArrow yoneda F where
  obj c := CostructuredArrow.mk (hom F c)
  map {X Y} f := {
    left := f.unop.val.unop
    right := 𝟙 _
  }
  map_comp {X Y Z} f g := by ext; dsimp
  map_id X := by ext; simp

-- 逆方向の射成分が ∫F の射になるための条件
theorem inverse_map_property (F : Cᵒᵖ ⥤ Type v₁)
    {X Y : CostructuredArrow yoneda F} (f : X ⟶ Y) :
    F.map (op f.left) (Y.hom.app (op Y.left) (𝟙 Y.left)) = X.hom.app (op X.left) (𝟙 X.left) := by
  simp only [yoneda_obj_obj]
  have Hf := f.w
  conv at Hf => arg 2; simp
  have E := CategoryTheory.congr_app Hf (op X.left)
  have E' := ConcreteCategory.congr_hom E (𝟙 X.left)
  rw [<- E']
  rw [<- comp_apply, <- Y.hom.naturality, comp_apply]
  rw [NatTrans.comp_app, comp_apply]
  simp

-- 逆方向 よ↓F ⥤ (∫F)ᵒᵖ
@[simps]
def inverse (F : Cᵒᵖ ⥤ Type v₁) :
    CostructuredArrow yoneda F ⥤ F.Elementsᵒᵖ where
  obj X := ⟨{
    fst := op X.left
    snd := X.hom.app (op X.left) (𝟙 _)
  }⟩
  map {X Y} f := ⟨{
    val := op f.left
    property := inverse_map_property F f
  }⟩
  map_comp {X Y Z} f g := Eq.symm (eq_of_comp_right_eq fun {Z_1} ↦ congrFun rfl)
  map_id X := Eq.symm (eq_of_comp_right_eq fun {Z} ↦ congrFun rfl)

-- 単位射の成分が ∫F の射になるための条件
theorem unitApp_property (F : Cᵒᵖ ⥤ Type v₁) (c : F.Elementsᵒᵖ) :
    F.map (𝟙 c.unop.fst) ((functor F ⋙ inverse F).obj c).unop.snd
      = c.unop.snd := by
  dsimp [functor, inverse, hom]
  rw [<- comp_apply, <- F.map_comp]
  rw [Category.id_comp, F.map_id]
  simp

-- 単位射の成分
def unitApp (F : Cᵒᵖ ⥤ Type v₁) (c : F.Elementsᵒᵖ) :
    (𝟭 F.Elementsᵒᵖ).obj c ⟶ (functor F ⋙ inverse F).obj c :=
  ⟨{
    val := 𝟙 c.unop.fst
    property := unitApp_property F c
  }⟩

-- 単位同型 𝟭 ≅ functor ⋙ inverse
def unitIso (F : Cᵒᵖ ⥤ Type v₁) :
    𝟭 F.Elementsᵒᵖ ≅ functor F ⋙ inverse F where
  hom := {
    app c := unitApp F c
    naturality {X Y} f := by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        inverse_map, yoneda_obj_obj, functor_map_left]
      apply Quiver.Hom.unop_inj
      simp only [unop_comp, unitApp]
      apply CategoryOfElements.ext
      erw [CategoryOfElements.comp_val, CategoryOfElements.comp_val]
      simp only [Functor.comp_obj, Functor.id_obj, Quiver.Hom.unop_op']
      erw [Category.id_comp, Category.comp_id]
      rfl
  }
  inv := {
    app c := ⟨{
      val := 𝟙 _
      property := by rfl
    }⟩
    naturality {X Y} f := by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      change 𝟙 (unop Y).fst ≫ f.unop.val = f.unop.val ≫ 𝟙 (unop X).fst
      simp
  }

  hom_inv_id := by
    ext x
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

  inv_hom_id := by
    ext x
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp


-- 余単位同型 inverse ⋙ functor ≅ 𝟭
def counitIso (F : Cᵒᵖ ⥤ Type v₁) :
    inverse F ⋙ functor F ≅ 𝟭 (CostructuredArrow yoneda F) where
  hom := {
    app f := {
      left := 𝟙 f.left
      right := 𝟙 _
      w := by
        ext x (g :  unop x ⟶ f.left)
        simp only [Functor.id_obj, Functor.const_obj_obj, inverse, yoneda_obj_obj, functor,
          CostructuredArrow.mk_right, Functor.comp_obj, CostructuredArrow.mk_left, Functor.map_id,
          Category.id_comp, TypeCat.Fun.toFun_apply, CostructuredArrow.mk_hom_eq_self,
          Discrete.functor_map_id, Category.comp_id, hom_app, op_unop, TypeCat.hom_ofHom,
          TypeCat.Fun.coe_mk]
        rw [<- comp_apply]
        rw [<- f.hom.naturality g.op]
        simp
    }
    naturality {X Y} f:= by
      simp only [functor, CostructuredArrow.mk_right, Functor.comp_obj, Functor.id_obj,
        Functor.comp_map, inverse_map, yoneda_obj_obj, Functor.id_map, CostructuredArrow.hom_eq_iff,
        CostructuredArrow.mk_left, CostructuredArrow.comp_left]
      change  f.left ≫ 𝟙 Y.left = 𝟙 X.left ≫ f.left
      simp

  }
  inv := {
    app f := {
      left := 𝟙 _
      right := 𝟙 _
      w := by
        ext c (g : unop c ⟶ f.left)
        simp only [inverse, yoneda_obj_obj, functor, hom, op_unop, CostructuredArrow.mk_right,
          Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj, CostructuredArrow.mk_left,
          Functor.map_id, CostructuredArrow.mk_hom_eq_self, Category.id_comp, TypeCat.hom_ofHom,
          TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk, Discrete.functor_map_id, Category.comp_id]
        rw [<- comp_apply, <- f.hom.naturality g.op]
        simp
    }
    naturality {X Y} f:= by
      simp only [Functor.id_obj, functor, CostructuredArrow.mk_right, Functor.comp_obj,
        Functor.id_map, Functor.comp_map, inverse_map, yoneda_obj_obj, CostructuredArrow.hom_eq_iff,
        CostructuredArrow.mk_left, CostructuredArrow.comp_left]
      change f.left ≫ 𝟙 Y.left = 𝟙 X.left ≫ f.left
      simp

  }
  hom_inv_id := by
    ext f; simp [functor, inverse]
  inv_hom_id := by
    ext f; simp [functor, inverse]


-- 三角等式: functor の像の上で単位と余単位が打ち消し合う
theorem functor_unitIso_comp (F : Cᵒᵖ ⥤ Type v₁) (c : F.Elementsᵒᵖ) :
    (functor F).map ((unitIso F).hom.app c) ≫ (counitIso F).hom.app ((functor F).obj c)
      = 𝟙 ((functor F).obj c) := by
  ext;
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp


end Lemma_2_4_7

def lemma_2_4_7 (F : Cᵒᵖ ⥤ Type v₁) : F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F where
  functor := Lemma_2_4_7.functor F
  inverse := Lemma_2_4_7.inverse F
  unitIso := Lemma_2_4_7.unitIso F
  counitIso := Lemma_2_4_7.counitIso F
  functor_unitIso_comp := Lemma_2_4_7.functor_unitIso_comp F

-- あくまでもイメージだが
-- {F c | c : C} ≅ {⟨Hom(_, c) ⟶ F | c : C}
def lemma_2_4_7' (F : Cᵒᵖ ⥤ Type v₁) :
    F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F where
  functor := {
    obj x := CostructuredArrow.mk (yonedaEquiv.symm x.unop.snd)
    map {X Y} f := {
      left := f.unop.val.unop
      right := 𝟙 _
      w := by
        simp only [op_unop, CostructuredArrow.mk_left, CostructuredArrow.mk_right,
          Functor.const_obj_obj, CostructuredArrow.mk_hom_eq_self, Discrete.functor_map_id,
          Category.comp_id]
        apply yonedaEquiv.injective
        simp [yonedaEquiv]
    }
  }
  inverse := {
    obj f := ⟨{
      fst := op f.left
      snd := yonedaEquiv f.hom
    }⟩
    map {X Y} f:= by
      apply op; simp only
      use f.left.op
      simp only
      rw [yonedaEquiv_naturality Y.hom f.left]
      erw [f.w]; simp
  }
  unitIso := {
    hom := {
      app x := op ⟨𝟙 x.unop.fst, by simp⟩
      naturality {X Y} f := by
        apply Quiver.Hom.unop_inj
        apply CategoryOfElements.ext
        change 𝟙 (unop Y).fst ≫ f.unop.val = f.unop.val ≫ 𝟙 (unop X).fst
        simp
    }
    inv := {
      app x := op ⟨𝟙 x.unop.fst, by simp⟩
      naturality {X Y} f := by
        apply Quiver.Hom.unop_inj
        apply CategoryOfElements.ext
        change 𝟙 (unop Y).fst ≫ f.unop.val = f.unop.val ≫ 𝟙 (unop X).fst
        simp
    }
    hom_inv_id := by
      ext x
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      change 𝟙 (unop x).fst ≫ 𝟙 (unop x).fst = 𝟙 (unop x).fst
      simp
    inv_hom_id := by
      ext x
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      change 𝟙 (unop x).fst ≫ 𝟙 (unop x).fst = 𝟙 (unop x).fst
      simp
  }
  counitIso := {
    hom := {
      app Y := CostructuredArrow.homMk (𝟙 Y.left) (by simp)
      naturality {X Y} f := by ext; simp
    }
    inv := {
      app Y := CostructuredArrow.homMk (𝟙 Y.left) (by simp)
      naturality {X Y} f := by ext; simp
    }
    hom_inv_id := by ext; simp
    inv_hom_id := by ext; simp
  }








#check @CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalenceFunctorProj

def lemma_2_4_7_proj (F : Cᵒᵖ ⥤ Type v₁) :
    (lemma_2_4_7 F).functor ⋙ CostructuredArrow.proj yoneda F
      ≅ (CategoryOfElements.π F).leftOp := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題2.4.8
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
共変関手 F と要素 x ∈ Fc について、x が普遍要素であることと (c,x) が ∫F の始対象であること
は同値である。したがって F が表現可能であることと、∫F が始対象をもつことは同値である。

構成: 表現から始対象を作り、始対象から表現を作り、表現可能性と始対象の存在の同値を示す。
-/

#check @CategoryTheory.Functor.Elements.isInitialOfCorepresentableBy

def prop_2_4_8_isInitial {F : C ⥤ Type v₁} {X : C} (h : F.CorepresentableBy X) :
    Limits.IsInitial (F.elementsMk X (h.homEquiv (𝟙 X))) := by
  apply  Limits.IsInitial.ofUniqueHom ?_ ?_
  · intro Y
    use h.homEquiv.symm Y.snd
    simp only
    rw [<- h.homEquiv_comp (h.homEquiv.symm Y.snd) (𝟙 X)]
    simp
  · intro Y m
    ext; simp only
    conv => arg 2; arg 2; rw [<- m.prop]
    rw [<- h.homEquiv_comp m.val (𝟙 X)]
    simp

#check @CategoryTheory.Functor.Elements.corepresentableByOfIsInitial

def prop_2_4_8_corepresentableBy {F : C ⥤ Type v₁} {E : F.Elements}
    (h : Limits.IsInitial E) : F.CorepresentableBy E.1 where
  homEquiv {x} := {
    toFun f := F.map f E.snd
    invFun Fx := (h.to (F.elementsMk x Fx)).val
    left_inv := by
      intro f; simp only
      set l := (h.to (F.elementsMk x ((ConcreteCategory.hom (F.map f)) E.snd)))
      set r : E ⟶ F.elementsMk x ((ConcreteCategory.hom (F.map f)) E.snd) := ⟨f, by simp⟩
      have : l = r := by apply Limits.IsInitial.hom_ext h
      rw [this]
    right_inv := by
      intro Fx; simp only
      exact (h.to (F.elementsMk x Fx)).prop
  }
  homEquiv_comp {x y} g f := by simp


#check @CategoryTheory.Functor.Elements.hasInitial_iff_isCorepresentable

theorem prop_2_4_8_iff (F : C ⥤ Type v₁) :
    Limits.HasInitial F.Elements ↔ F.IsCorepresentable := by
      constructor<;> intro H
      · constructor
        let init := (Limits.initial F.Elements)
        use init.fst
        refine ⟨{
          homEquiv {x} := {
            toFun f :=  F.map f init.snd
            invFun Fx := (Limits.initial.to (F.elementsMk x Fx)).val
            left_inv := by
              intro f; simp only
              let X : F.Elements := ⟨x, F.map f init.snd⟩
              let f' : init ⟶ X := {
                val := f
                property := by simp [X]
              }
              have : (Limits.initial.to (F.elementsMk x ((ConcreteCategory.hom (F.map f)) init.snd))) = f' := by apply Limits.initial.hom_ext
              rw [this]
            right_inv := by
              intro Fx; simp only
              have := (Limits.initial.to (F.elementsMk x Fx)).prop
              simp only at this
              rw [this]
          }
          homEquiv_comp {X Y} g f := by
            simp only [Equiv.coe_fn_mk, Functor.map_comp, comp_apply]
        }⟩
      · rcases H with ⟨X, ⟨H⟩⟩
        let FX := H.homEquiv (𝟙 X)
        let x := F.elementsMk X FX
        apply @Limits.hasInitial_of_unique F.Elements _ x ?_ ?_
        · intro y; constructor
          use H.homEquiv.symm y.snd
          simp only [x, FX]
          rw [<- H.homEquiv_comp (H.homEquiv.symm y.snd) (𝟙 X)]
          simp
        · intro y; constructor
          intro ⟨f, Hf⟩ ⟨g, Hg⟩
          simp only [x, FX] at Hf Hg
          have Ef := H.homEquiv_comp f (𝟙 X)
          have Eg := H.homEquiv_comp g (𝟙 X)
          simp only [Category.id_comp] at Ef Eg
          ext; simp only
          rw [<- H.homEquiv.left_inv f]
          conv => arg 1; arg 2; simp only [Equiv.toFun_as_coe]
          rw [Ef, Hf, <- Hg, <- Eg]
          simp


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 可縮亜群（1.6）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
命題2.4.9 が使う可縮亜群を、1.6 から持ってくる。本は「終圏と同値な圏」を定義とし、その展開と
して「空でなく、どの hom 集合もちょうど1元」を挙げる。ここでは後者を定義に採る。

構成: 可縮亜群を定義する。
-/

class MyContractibleGroupoid (D : Type u₂) [Category.{v₂} D] : Prop where
  nonempty : Nonempty D
  hom_nonempty (x y : D) : Nonempty (x ⟶ y)
  hom_ext {x y : D} (f g : x ⟶ y) : f = g

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題1.6.16
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏の終対象たちが張る充満部分圏は、空であるか可縮亜群である。特に、任意の2つの終対象は一意的に
同型である。

構成: 終対象であるという性質で充満部分圏を取り、それが空か可縮亜群かを示す。
-/

def myTerminals (D : Type u₂) [Category.{v₂} D] : ObjectProperty D :=
  fun X => Nonempty (Limits.IsTerminal X)

theorem lemma_1_6_16 (D : Type u₂) [Category.{v₂} D] :
    IsEmpty (myTerminals D).FullSubcategory ∨
      MyContractibleGroupoid (myTerminals D).FullSubcategory := by
  rcases isEmpty_or_nonempty (myTerminals D).FullSubcategory with H | H
  · left; exact H
  · right; use H
    · intro ⟨x, ⟨Hx⟩⟩ ⟨y, ⟨Hy⟩⟩
      constructor; constructor; simp only
      exact  Hy.from x
    · intro ⟨x, ⟨Hx⟩⟩ ⟨y, ⟨Hy⟩⟩ ⟨f⟩ ⟨g⟩
      simp only at f g
      ext; simp only
      apply Hy.hom_ext






-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題2.4.9
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
F の表現たちが ∫F に張る充満部分圏は、空であるか可縮亜群である。

構成: 表現であるという性質で充満部分圏を取り、それが空か可縮亜群かを示す。
-/

-- ∫F の対象 (c, x) についての性質を、「𝟙 c を x に送る自然同型 Hom(c, −) ≅ F が存在する」で定義する
def myRepresentations (F : C ⥤ Type v₁) : ObjectProperty F.Elements :=
  fun E => ∃ h : F.CorepresentableBy E.fst, h.homEquiv (𝟙 E.fst) = E.snd

theorem prop_2_4_9 (F : C ⥤ Type v₁) :
    IsEmpty (myRepresentations F).FullSubcategory ∨
      MyContractibleGroupoid (myRepresentations F).FullSubcategory := by
    rcases isEmpty_or_nonempty (myRepresentations F).FullSubcategory with H | H
    · left; exact H
    · right
      rcases H with ⟨c⟩
      constructor
      · exact ⟨c⟩
      · intro ⟨x, Hx, Ex⟩ ⟨y, Hy, Ey⟩
        constructor; constructor; simp only
        refine {
          val := Hx.homEquiv.symm (Hy.homEquiv.toFun (𝟙 y.fst))
          property := by
            simp only [Equiv.toFun_as_coe]
            rw [Ey, <- Ex]
            rw [<- Hx.homEquiv_comp (Hx.homEquiv.symm y.snd) (𝟙 x.fst)]
            simp
        }
      · intro ⟨x, Hx, Ex⟩ ⟨y, Hy, Ey⟩ ⟨f, Hf⟩ ⟨g, Hg⟩
        ext; simp only at f g Hf Hg ⊢
        have H1 := Hx.homEquiv_comp f (𝟙 x.fst)
        have H2 := Hx.homEquiv_comp g (𝟙 x.fst)
        rw [Ex, Hf, Category.id_comp] at H1
        rw [Ex, Hg, Category.id_comp] at H2
        rw [<- Hx.homEquiv.left_inv f]
        conv => arg 1; arg 2; simp; rw [H1]
        rw [<- Hx.homEquiv.left_inv g]
        conv => arg 2; arg 2; simp ; rw [H2]




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定数関手の要素の圏
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
どんな圏 E も、一点集合を値とする定数関手 Δ∗ : E ⥤ Set の要素の圏として現れ、Δ∗ の表現は
E の始対象を定める。

構成: 要素の圏と E の同値を構成し、Δ∗ の表現が始対象を定めることを示す。
-/


def constElementsEquiv (E : Type u₂) [Category.{v₂} E] :
    ((Functor.const E).obj (PUnit : Type v₂)).Elements ≌ E where
  functor := {
    obj x := x.fst
    map {x y} f := f.val
    map_id x := by simp
    map_comp {x y z} f g := by simp
  }
  inverse := {
    obj x := {
      fst := x
      snd := PUnit.unit
    }
    map {x y} f := ⟨f, by simp⟩
  }
  unitIso := {
    hom := {
      app x := by
        use 𝟙 x.fst
        exact PUnit.eq_punit x.snd
      naturality {x y} f := by
        apply CategoryOfElements.ext
        simp only [CategoryOfElements.comp_val]
        simp
    }
    inv := {
      app x := 𝟙 x
      naturality {x y} f := by
        change f ≫ 𝟙 y = 𝟙 x ≫ f
        simp
    }
    hom_inv_id := by
      ext x
      change 𝟙 x.fst ≫ 𝟙 x.fst = 𝟙 x.fst
      simp
    inv_hom_id := by
      ext x
      change _ ≫ _ = 𝟙 _
      simp
  }
  counitIso := {
    hom := {
      app x := 𝟙 x
      naturality := by simp
    }
    inv := {
      app x := 𝟙 x
      naturality := by simp
    }
    hom_inv_id := by ext; simp
    inv_hom_id := by ext; simp
  }




def isInitialOfConstCorepresentableBy {E : Type u₂} [Category.{v₂} E] {X : E}
    (h : ((Functor.const E).obj (PUnit : Type v₂)).CorepresentableBy X) :
    Limits.IsInitial X := by
  -- have := h.homEquiv (𝟙 X)
  apply Limits.IsInitial.ofUniqueHom ?_ ?_
  · intro Y
    exact h.homEquiv.symm.toFun PUnit.unit
  · intro Y m
    simp only [Functor.const_obj_obj, Equiv.toFun_as_coe]
    rw [ Equiv.eq_symm_apply]


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義2.4.13
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
関手 Π : E ⥤ C が離散左ファイブレーションであるとは、C の射 f と、その域の持ち上げ e に
対して、e を域とし f を持ち上げる E の射がただ一つ存在することをいう。離散右ファイブレー
ションは、余域の持ち上げ e' に対して同じことをいう。c の持ち上げとは Πe = c となる対象 e、
f の持ち上げとは Π が f に送る E の射のことである。

構成: c の持ち上げ全体と、射が f の持ち上げであることを定義し、そのうえで離散左ファイブレー
      ションと離散右ファイブレーションをそれぞれ定義する。
-/

#check @CategoryTheory.Functor.Fiber

def MyFiber {E : Type u₂} [Category.{v₂} E] (P : E ⥤ C) (c : C) :=
  {e : E // P.obj e = c}

#check @CategoryTheory.Functor.IsHomLift

inductive MyIsHomLift {E : Type u₂} [Category.{v₂} E] (P : E ⥤ C) :
    ∀ {c c' : C} {e e' : E}, (c ⟶ c') → (e ⟶ e') → Prop
  | map {e e' : E} (g : e ⟶ e') : MyIsHomLift P (P.map g) g

class LeftFibration {E : Type u₂} [Category.{v₂} E] (P : E ⥤ C) where
  liftObj {e : E} {c : C} (f : P.obj e ⟶ c) : P.Fiber c
  liftMap {e : E} {c : C} (f : P.obj e ⟶ c) : e ⟶ (liftObj f).val
  homLift {e : E} {c : C} (f : P.obj e ⟶ c) : P.IsHomLift f (liftMap f)
  uniq {e : E} {c : C} (f : P.obj e ⟶ c) {e' : E} (g : e ⟶ e') :
    P.IsHomLift f g → (⟨e', g⟩ : Σ x : E, e ⟶ x) = ⟨(liftObj f).val, liftMap f⟩

class RightFibration {E : Type u₂} [Category.{v₂} E] (P : E ⥤ C) where
  liftObj {e' : E} {c : C} (f : c ⟶ P.obj e') : P.Fiber c
  liftMap {e' : E} {c : C} (f : c ⟶ P.obj e') : (liftObj f).val ⟶ e'
  homLift {e' : E} {c : C} (f : c ⟶ P.obj e') : P.IsHomLift f (liftMap f)
  uniq {e' : E} {c : C} (f : c ⟶ P.obj e') {e : E} (g : e ⟶ e') :
    P.IsHomLift f g → (⟨e, g⟩ : Σ x : E, x ⟶ e') = ⟨(liftObj f).val, liftMap f⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題2.4.14
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
要素の圏の構成は Set^C から CAT/C への充満忠実関手を定め、その本質的像は離散左ファイブ
レーションのなす充満部分圏である。反変な C-添字関手の場合は離散右ファイブレーションになる。

構成: 要素の圏からの射影が離散左（右）ファイブレーションであることを示し、逆に離散左ファイブ
      レーションから関手を構成して、もとの圏がその要素の圏と C 上で同値になることを示す。
-/

#print CategoryOfElements.π
instance prop_2_4_14_π_lf (F : C ⥤ Type v₁) :
    LeftFibration (CategoryOfElements.π F) where
  liftObj {e c} (f : e.fst ⟶ c) := ⟨⟨c, F.map f e.snd⟩, by simp [CategoryOfElements.π]⟩
  liftMap {e c} (f : e.fst ⟶ c) := ⟨f, by simp⟩
  homLift {e c} (f : e.fst ⟶ c) := by

    set g : e ⟶ (⟨c, (ConcreteCategory.hom (F.map f)) e.snd⟩ : F.Elements) := ⟨f, rfl⟩
    exact Functor.IsHomLift.map g
  uniq {e c} (f : (CategoryOfElements.π F).obj e ⟶ c) {e'} g Hg := by
    have := Hg
    have hcod : (CategoryOfElements.π F).obj e' = c := IsHomLift.codomain_eq _ f g
    obtain ⟨c₂, x₂⟩ := e'
    have hcod' : c₂ = c := hcod
    subst hcod'
    have hg2 : (CategoryOfElements.π F).IsHomLift
        (show (CategoryOfElements.π F).obj e ⟶
          (CategoryOfElements.π F).obj (⟨c₂, x₂⟩ : F.Elements) from f) g := Hg
    have hfac0 : f = (CategoryOfElements.π F).map g := IsHomLift.eq_of_isHomLift _ f g
    have hfac : Subtype.val g = f := hfac0.symm
    have hprop : (ConcreteCategory.hom (F.map (Subtype.val g))) e.snd = x₂ := g.property
    rw [hfac] at hprop
    congr 1
    · exact Functor.Elements.ext _ _ rfl (by simpa using hprop.symm)
    · rw [Subtype.heq_iff_coe_eq fun k => by rw [hprop]]
      exact hfac

instance prop_2_4_14_π_rf (F : Cᵒᵖ ⥤ Type v₁) :
    RightFibration (CategoryOfElements.π F).leftOp := sorry

def myFunctorOfLeftFibration {E : Type u₂} [Category.{v₂} E] (P : E ⥤ C)
    [LeftFibration P] : C ⥤ Type u₂ := sorry

def prop_2_4_14_equiv {E : Type u₂} [Category.{v₂} E] (P : E ⥤ C)
    [LeftFibration P] : E ≌ (myFunctorOfLeftFibration P).Elements := sorry

theorem prop_2_4_14_over {E : Type u₂} [Category.{v₂} E] (P : E ⥤ C)
    [LeftFibration P] :
    (prop_2_4_14_equiv P).functor ⋙ CategoryOfElements.π _ = P := sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.4.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
共変関手 F : C ⥤ Set の要素の圏と、米田埋め込み よ : Cᵒᵖ ⥤ Set^C と対象 F に関するコンマ圏
よ↓F との間の、反変な同型を定義する。
-/

def ex_2_4_i (F : C ⥤ Type v₁) : F.Elementsᵒᵖ ≌ CostructuredArrow coyoneda F := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.4.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
F : C ⥤ Set の要素の圏は、一点集合 ∗ : 1 ⥤ Set と F に関するコンマ圏 ∗↓F と同型である。
反変関手についても同様の主張が成り立つ。

構成: 共変版と反変版をそれぞれ同値として述べる。
-/

#check @CategoryTheory.CategoryOfElements.structuredArrowEquivalence

def ex_2_4_ii (F : C ⥤ Type v₁) : F.Elements ≌ StructuredArrow PUnit F := sorry

#check @CategoryTheory.CategoryOfElements.structuredArrowEquivalence

def ex_2_4_ii_contra (F : Cᵒᵖ ⥤ Type v₁) :
    F.Elementsᵒᵖ ≌ (StructuredArrow PUnit F)ᵒᵖ := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.4.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
双対性により、反変関手 F と要素 x ∈ Fc について、x が普遍要素であることと (c,x) が ∫F の
終対象であることは同値であり、F が表現可能であることと ∫F が終対象をもつことは同値である。

構成: 命題2.4.8 の3本を反変側で述べる。
-/

#check @CategoryTheory.Functor.Elements.isInitialOfRepresentableBy

def ex_2_4_iv_isTerminal {F : Cᵒᵖ ⥤ Type v₁} {X : C} (h : F.RepresentableBy X) :
    Limits.IsTerminal (op (F.elementsMk (op X) (h.homEquiv (𝟙 X)))) := sorry

#check @CategoryTheory.Functor.Elements.representableByOfIsInitial

def ex_2_4_iv_representableBy {F : Cᵒᵖ ⥤ Type v₁} {E : F.Elements}
    (h : Limits.IsTerminal (op E)) : F.RepresentableBy E.1.unop := sorry

#check @CategoryTheory.Functor.Elements.hasInitial_iff_isRepresentable

theorem ex_2_4_iv_iff (F : Cᵒᵖ ⥤ Type v₁) :
    Limits.HasTerminal F.Elementsᵒᵖ ↔ F.IsRepresentable := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.4.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 集合を、その上の前順序全体の集合に送る反変関手 F : Setᵒᵖ ⥤ Set を定義する。

def ex_2_4_vi : (Type u)ᵒᵖ ⥤ Type u where
  obj A := { r : unop A → unop A → Prop // IsPreorder (unop A) r }
  map f := sorry
  map_id := sorry
  map_comp := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.4.viii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
要素の圏の構成は、充満忠実関手 ∫(−) : Set^C ⥤ CAT/C の対象への作用を与える。したがって
F, G : C ⥤ Set が自然同型であることと、∫F と ∫G が C 上で同型であることは同値である。

構成: 自然変換から要素の圏の間の関手を作り、それが C 上の関手であることを示し、C 上の関手が
      すべてこの形にただ一通りに書けることを示して、自然同型と C 上の同型の同値を結論する。
-/

#check @CategoryTheory.CategoryOfElements.map

def ex_2_4_viii_map {F G : C ⥤ Type v₁} (α : F ⟶ G) : F.Elements ⥤ G.Elements := sorry

#check @CategoryTheory.CategoryOfElements.map_π

theorem ex_2_4_viii_map_π {F G : C ⥤ Type v₁} (α : F ⟶ G) :
    ex_2_4_viii_map α ⋙ CategoryOfElements.π G = CategoryOfElements.π F := sorry

#check @CategoryTheory.Functor.elementsFunctor

theorem ex_2_4_viii_fullyFaithful {F G : C ⥤ Type v₁} (K : F.Elements ⥤ G.Elements)
    (hK : K ⋙ CategoryOfElements.π G = CategoryOfElements.π F) :
    ∃! α : F ⟶ G, ex_2_4_viii_map α = K := sorry

theorem ex_2_4_viii_iso_iff (F G : C ⥤ Type v₁) :
    Nonempty (F ≅ G) ↔ ∃ (K : F.Elements ⥤ G.Elements) (L : G.Elements ⥤ F.Elements),
      K ⋙ L = 𝟭 _ ∧ L ⋙ K = 𝟭 _ ∧ K ⋙ CategoryOfElements.π G = CategoryOfElements.π F :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習2.4.ix
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
離散左ファイブレーションと離散右ファイブレーションのファイバーは離散圏である。すなわち、
Π が恒等射に送る射は、両端の対象が等しく、その等式から来る射に限る。

構成: 左と右のそれぞれについて述べる。
-/

theorem ex_2_4_ix_left {E : Type u₂} [Category.{v₂} E] {P : E ⥤ C} [LeftFibration P]
    {c : C} {e e' : E} (g : e ⟶ e') (hg : P.IsHomLift (𝟙 c) g) :
    ∃ p : e = e', g = eqToHom p := sorry

theorem ex_2_4_ix_right {E : Type u₂} [Category.{v₂} E] {P : E ⥤ C} [RightFibration P]
    {c : C} {e e' : E} (g : e ⟶ e') (hg : P.IsHomLift (𝟙 c) g) :
    ∃ p : e = e', g = eqToHom p := sorry
