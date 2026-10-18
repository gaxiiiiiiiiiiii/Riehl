import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Topology.Category.TopCat.Basic

/-!
# 3.4 極限と余極限の保存・反映・創出

節の数学的な内容は同名の HTML にある。このファイルは本の主張を出現順に並べたもので、主張と
定理群の構成は各セクションの冒頭に、形式化の判断は下の表に、Mathlib の対応物は各
statement の直前の `#check`・`#print` にある。

形式化の判断:
  添字圏の      節をまたぐ取り決めどおり、J は `Type v` の小圏、C と D は `Category.{v}` に
  大きさ        取る。命題3.4.9 の A も `Type v` の小圏に取り、関手圏 A ⥤ C の hom が
                `Type v` に落ちるようにする
  錐の像と      錐の像 Fλ と comparison map κ は本節の本文が記述するので自前で組む。Fλ は
  comparison    data を書き、脚の自然性を演習にする。κ は「F で写した極限錐を FK の極限錐から
  map           分解する射」を作ること自体が中身なので丸ごと演習。どちらも Mathlib の
                `Functor.mapCone`・`limit.post` と定義が一致するので、以降の statement は
                Mathlib の名前で書く。余極限側の錐の像 `myMapCocone` も、演習3.4.i と
                演習3.4.vi の statement が `Functor.mapCocone` を使うので組む。錐の像が錐の
                射も写して関手 Cone K ⥤ Cone (K ⋙ F) をなすことは本にないが、錐の同型を F で
                写すのに要るので `myConeFunctoriality` として組む（Mathlib の
                `Cone.functoriality`）。対象の部分は `Functor.mapCone`、射の頂点成分は F で
                写した射として書いて渡し、錐の射の条件と関手則を演習にする
  定義3.4.1    保存・反映は Mathlib の `PreservesLimit`・`ReflectsLimit` とフィールド単位
                で同じなので、写しを書いて渡し、statement は Mathlib で書く。創出は Mathlib
                の定義と形が違う。本は「FK が極限を持てば K も持ち、そのとき錐が極限錐であることと像が
                極限錐であることが同値」という命題で、Mathlib の `CreatesLimit` は極限錐の
                持ち上げと同型 `LiftableCone` を data として持つ。本の形を `MyCreatesLimit`
                として置き、`Nonempty (CreatesLimit K F)` との同値を演習にする。
                同値の証明では同型を介して極限錐を移すので、本にない補題「極限錐と同型な錐は
                極限錐」を `myIsLimitOfIso` として直前に置く（Mathlib の
                `IsLimit.ofIsoLimit`）。創出の statement は Mathlib の `CreatesLimit` を返す `def` で書く。余極限の
                保存 `MyPreservesColimit` は演習3.4.i と演習3.4.vi で使うので写しを置く。
                定義の直後の段落が述べる
                「ある形の図式すべてについて保存する」と「同型を反映する」も、Mathlib の
                `PreservesLimitsOfShape`・`PreservesColimitsOfShape`・
                `Functor.ReflectsIsomorphisms` とフィールド単位で同じ写しを置き、statement は
                Mathlib で書く
  余極限の半分  補題3.4.5・3.4.6、命題3.4.9、演習3.4.v の「極限と余極限」は、極限の半分
                だけ置く。余極限の半分は同じ主張・同じ証明の双対である。命題3.4.8 の連結な
                余極限と演習3.4.i・3.4.ii の余極限は双対ではない主張なので置く
  定義3.4.7     厳密な創出は、錐の等式 `F.mapCone c = d` で「持ち上げ」を述べる。本の
                「邪悪な」厳密化は、同型ではなく等式で持ち上げを述べることにあたる。Mathlib
                に対応物なし。形は Mathlib の `LiftsToLimit`・`CreatesLimit` に合わせ、
                持ち上げの中身を `MyStrictLift`（`validLift` を `≅` から `=` に替え、
                `unique` を足したもの）に束ね、`MyStrictlyCreatesLimit` はそれを返す
                `lifts` 1 本とする。Mathlib と同じく Prop ではなくデータなので、これを
                結論とする主張は `theorem` でなく `noncomputable def` になる。命題3.4.8
                の余極限側のために双対 `MyStrictlyCreatesColimit` も置く
  連結な圏      本の定義（空でなく、任意の二対象が射の有限のジグザグで結ばれる）を
                `MyIsConnected` として置く。ジグザグは一歩の関係 `myZag` の反射推移閉包
                `Relation.ReflTransGen` で書く。Mathlib の `IsConnected` は「任意の離散圏への
                関手が定関手と同型」の形で定義されているので、同値 `myIsConnected_iff` を演習
                に置き、statement は `IsConnected` で書く
  命題3.4.8     c/C（演習1.1.iii）は Mathlib の `Under c`、忘却関手は `Under.forget c`。
                `Under c` はコンマ圏 `Comma (Functor.fromPUnit c) (𝟭 C)` で、本の c/C に空の
                `left` 成分が付いた形。本の c/C とは形が違うので、使う直前に `#print` で定義を見せる。
                忘却関手は `myUnderForget` として組み直す演習を置くが、statement は
                `Under.forget c` で書く。証明で使う Π の上の錐 `Under.forgetCone` と錐の
                引き戻し `Cone.whisker` も `myUnderForgetCone`・`myConeWhisker` として組む
                演習を置く。strict な創出の 2 本と、「したがって c/C は極限・連結な余極限を
                持つ」の 2 本に割る
  命題3.4.9     ob A ↪ A を `myObIncl`（`Discrete A ⥤ A`）、忘却関手 ev を `myEv`（`myObIncl`
                との前合成）として組む。どちらも義務が自動で閉じるので書き切って渡す。
                Mathlib に ev の名前の付いた対応物はない（`Functor.whiskeringLeft` の特殊化）
                ので、statement は `myEv` を参照する。主張は strict な創出と (i)・(ii) の
                3 本に割る
  演習3.4.i     (i) の κ の型は本が与えるので書く。(ii) は (i) で組んだ κ について述べる
  演習3.4.ii    要素の圏 ∫F（定義2.4.1）とその射影は既知の定義として Mathlib の
                `Functor.Elements`・`Functor.Elements.π` を使う
  演習3.4.iv    Set∗ を ∗/Set、すなわち `Under (PUnit : Type v)`、Top∗ を
                `Under (TopCat.of PUnit)` で取る。余積を保存しないことを、二項余積の形
                `Discrete WalkingPair` の余極限を保存しないこととして述べる
  演習3.4.v     「積の圏が極限を持つのは各成分が持つとき、かつそのときに限る」は、成分の圏が
                一つでも空だと成り立たない（積の圏が空になり、左辺が空虚に真になる）。
                各成分が空でないことを仮定に加える。(ii) の錐は頂点を書いて渡し、脚と
                極限錐であることを演習にする。圏の積 ∏ C_i とその射影は既知の定義として
                Mathlib の `∀ i, Cs i`・`Pi.eval` を使う
  演習3.4.vi    レトラクトの条件 rs = id_B は `s ≫ r = 𝟙 B`、冪等射 sr は `r ≫ s`。
                等化子図式・余等化子図式の条件式を別の宣言に割る
  本にない      次は本に対応する概念がなく、Mathlib の道具として statement に使う。
  Mathlib の    `LimitCone`（錐と極限錐である証拠の組。演習3.4.v）、`Relation.ReflTransGen`
  道具          （関係の反射推移閉包。連結な圏）、`TopCat.of`（演習3.4.iv）

statement を置かない節末問題:
  3.4.iv   後半（連結性の仮定が必要な理由を説明する）は説明問題。前半のみ置く
  3.4.vi   (ii) は冪等射 1 本で生成される圏の図式の極限・余極限を問う。この添字圏は Mathlib
           になく、自前で組むと節の主題から外れる。(iii) は (i) の等化子・余等化子の部分
           だけ置く

載せない例と Remark:
  注意3.4.2（上の階と下の階の比喩）、例3.4.10（各点的でない極限）、命題3.4.9 の後の注意
  （C が極限を持たないとき命題3.4.9 は何も言わない）、脚注12〜14 は載せない。定義3.4.4
  （被覆と層）も載せない。この節の論理展開では極限の保存が重要な仮定になる例として置かれて
  いて、後の主張から参照されない。形式化には開集合の poset と二つずつの共通部分がなす添字圏
  を組む必要があり、節の主題から外れる。

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Limits/Cones.lean`（`Functor.mapCone`・`Functor.mapCocone`）
  - `Mathlib/CategoryTheory/Limits/HasLimits.lean`（`limit.post`・`colimit.post`）
  - `Mathlib/CategoryTheory/Limits/Preserves/Basic.lean`（`PreservesLimit`・
    `ReflectsLimit`・`fullyFaithful_reflectsLimits`）
  - `Mathlib/CategoryTheory/Limits/Preserves/Limits.lean`（`preservesLimit_of_isIso_post`）
  - `Mathlib/CategoryTheory/Limits/Creates.lean`（`CreatesLimit`・`LiftableCone`・
    `createsLimitOfReflectsIso`）
  - `Mathlib/CategoryTheory/Adjunction/Limits.lean`（`Adjunction.isEquivalencePreservesLimits`・
    `Functor.reflectsLimits_of_isEquivalence`）
  - `Mathlib/CategoryTheory/IsConnected.lean`（`IsConnected`・`zigzag_isConnected`）
  - `Mathlib/CategoryTheory/Limits/Comma.lean`（`StructuredArrow.createsLimitsOfShape`）
  - `Mathlib/CategoryTheory/Limits/Constructions/Over/Connected.lean`
    （`Under.createsColimitsOfShapeForgetOfIsConnected`）
  - `Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean`
    （`functorCategoryHasLimitsOfShape`・`evaluation_preservesLimitsOfShape`）
-/

open CategoryTheory Limits

universe w v u u'

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v} D]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 錐の像と comparison map（定義3.4.1 の前）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の関手 F : C → D と図式 K : J → C について、F は K 上の錐 λ : Δc ⇒ K を、whiskering に
よって FK 上の錐 Fλ : ΔFc ⇒ FK に送る。Fλ の脚は Fλ_j である。K と FK の極限がともに存在する
とき、極限錐の像 ΔF(lim K) ⇒ FK を FK の極限錐から分解する comparison map κ : F lim K → lim FK
がある。余極限についても双対的に余錐の像がある。
-/

#print Functor.mapCone
def myMapCone (F : C ⥤ D) {K : J ⥤ C} (c : Cone K) : Cone (K ⋙ F) where
  pt := F.obj c.pt
  π := {
    app j := (Functor.whiskerRight c.π F).app j
    naturality := by
      intro i j f
      rw [<- ((Functor.whiskerRight c.π F)).naturality f]
      simp
  }

-- 錐の像は錐の射も写し、錐の圏の間の関手 Cone K ⥤ Cone (K ⋙ F) をなす。本にない構成で、
-- 錐の同型を F で写すのに使う。

#check Cone.functoriality

def myConeFunctoriality (K : J ⥤ C) (F : C ⥤ D) : Cone K ⥤ Cone (K ⋙ F) where
  obj c := F.mapCone c
  map {X Y} f := {
    hom := F.map f.hom
    w j := by simp
  }
  map_id X := by ext; simp
  map_comp {X Y Z} f g := by ext; simp

#check Functor.mapCocone

def myMapCocone (F : C ⥤ D) {K : J ⥤ C} (c : Cocone K) : Cocone (K ⋙ F) where
  pt := F.obj c.pt
  ι := {
    app j := F.map (c.ι.app j)
    naturality := sorry
  }

#check limit.post

noncomputable def myLimitPost (K : J ⥤ C) (F : C ⥤ D) [HasLimit K] [HasLimit (K ⋙ F)] :
    F.obj (limit K) ⟶ limit (K ⋙ F) := limit.lift _ (F.mapCone (limit.cone K))




-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.4.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
図式 K : J → C について、関手 F : C → D が K の極限を保存するとは、K 上の任意の極限錐の像が
FK 上の極限錐になること。反映するとは、像が FK の極限錐になる K 上の錐がすべて極限錐である
こと。創出するとは、FK が極限を持てば K も極限を持ち、そのとき K 上の錐が極限錐であることと
その像が極限錐であることが同値になること。余極限についても双対的に定める。図式のクラス
（たとえば特定の形の図式すべて）について極限を保存する・反映する・創出するとは、そのクラスに
属する各図式についてそうすることをいう。同じ言葉は同型についても使い、F が同型を反映する
とは、F で写して同型になる射がすべて同型であることをいう。

構成: 保存・反映・創出をそれぞれ組み、極限錐と同型な錐が極限錐であることを示してから、
      創出が Mathlib の `CreatesLimit` と同値であることを示す。余極限の保存、ある形の図式
      すべてについての保存、同型の反映を組む。
-/


#print PreservesLimit

-- FはKの極限を保存する
class MyPreservesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves : ∀ {c : Cone K}, IsLimit c → Nonempty (IsLimit (F.mapCone c))

#print ReflectsLimit

class MyReflectsLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  reflects : ∀ {c : Cone K}, IsLimit (F.mapCone c) → Nonempty (IsLimit c)

class MyCreatesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  creates : HasLimit (K ⋙ F) →
    HasLimit K ∧ ∀ c : Cone K, Nonempty (IsLimit c) ↔ Nonempty (IsLimit (F.mapCone c))

-- 極限錐と同型な錐は極限錐である。創出の二つの定義の同値で使う。

#check IsLimit.ofIsoLimit

def myIsLimitOfIso {K : J ⥤ C} {c d : Cone K} (Hc : IsLimit c) (σ : c ≅ d) : IsLimit d where
  lift s := Hc.lift s ≫ σ.hom.hom
  fac s j := by
    rw [Category.assoc, σ.hom.w, Hc.fac]
  uniq s m w := by
    rw [<- Hc.uniq s (m ≫ σ.inv.hom)]
    · simp
    · intro j; rw [Category.assoc, σ.inv.w, w]







#print CreatesLimit
#print LiftableCone

theorem def_3_4_1_creates (K : J ⥤ C) (F : C ⥤ D) :
    MyCreatesLimit K F ↔ Nonempty (CreatesLimit K F) where
  mp H := ⟨{
    reflects {c} HFc := ⟨(((H.creates ⟨_, HFc⟩).2 c).mpr ⟨HFc⟩).some⟩
    lifts c Hc := {
      liftedCone := (H.creates ⟨c, Hc⟩).1.exists_limit.some.cone
      validLift := by
        have Hs := (H.creates ⟨c, Hc⟩).1.exists_limit.some.isLimit
        set s := (H.creates ⟨c, Hc⟩).1.exists_limit.some.cone
        have HFs := (((H.creates ⟨c, Hc⟩).2 s).mp ⟨Hs⟩).some
        refine {
          hom := {
            hom := Hc.lift (F.mapCone s)
            w j :=  Hc.fac (F.mapCone s) j
          }
          inv := {
            hom := HFs.lift c
            w j := HFs.fac c j
          }
          hom_inv_id := by
            ext; simp only [Functor.mapCone_pt, Cone.category_comp_hom, Cone.category_id_hom]
            apply HFs.hom_ext
            intro j; dsimp only [Functor.comp_obj, Functor.mapCone_pt]
            rw [Category.assoc, HFs.fac, Hc.fac]; simp
          inv_hom_id := by
            ext; simp only [Cone.category_comp_hom, Functor.mapCone_pt, Cone.category_id_hom]
            apply Hc.hom_ext; intro j
            dsimp only [Functor.comp_obj]
            rw [Category.assoc, Hc.fac, HFs.fac]; simp
        }
    }
  }⟩
  mpr H := {
    creates HKF := by
      have H1 := H.some.toReflectsLimit
      have H2 := H.some.lifts
      have H3 := H2 (limit.cone (K ⋙ F)) (limit.isLimit (K ⋙ F))
      rcases H3 with ⟨s, σ⟩
      have HFs := (limit.isLimit (K ⋙ F)).ofIsoLimit σ.symm
      have Hs := (H1.reflects HFs).some
      use ⟨s, Hs⟩
      intro c
      constructor<;> intro ⟨H'⟩<;> constructor;swap
      · exact (H1.reflects H').some
      · let τ :=  Hs.uniqueUpToIso H'
        have τ' := (Cone.functoriality K F).mapIso τ
        have : F.mapCone c ≅limit.cone (K ⋙ F) := τ'.symm.trans σ
        exact (limit.isLimit (K ⋙ F)).ofIsoLimit this.symm
  }







#print PreservesColimit

class MyPreservesColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves : ∀ {c : Cocone K}, IsColimit c → Nonempty (IsColimit (F.mapCocone c))

#print PreservesLimitsOfShape

class MyPreservesLimitsOfShape (J : Type v) [SmallCategory J] (F : C ⥤ D) : Prop where
  preservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F

#print PreservesColimitsOfShape

class MyPreservesColimitsOfShape (J : Type v) [SmallCategory J] (F : C ⥤ D) : Prop where
  preservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F

#print Functor.ReflectsIsomorphisms

class MyReflectsIsomorphisms (F : C ⥤ D) : Prop where
  reflects : ∀ {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)], IsIso f

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.4.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- C と D が J 型の極限を持つとき、関手 F : C → D と図式 K : J → C について、F が K の極限を
-- 保存するのは、comparison map κ : F(lim K) → lim FK が同型であるとき、かつそのときに限る。

#check preservesLimit_of_isIso_post
#print HasLimitsOfShape

theorem lemma_3_4_3 [HasLimitsOfShape J C] [HasLimitsOfShape J D] (F : C ⥤ D) (K : J ⥤ C) :
    PreservesLimit K F ↔ IsIso (limit.post K F) where
  mp H := by
    have Hs := limit.isLimit K
    have Ht := (H.preserves Hs).some
    set t := F.mapCone (limit.cone K)
    set s := limit.cone K
    use Ht.lift (limit.cone (K ⋙ F))
    constructor
    · apply Ht.hom_ext
      intro j
      rw [Category.assoc, Ht.fac]
      rw [limit.cone_π, limit.post_π]
      simp [t]
    · apply limit.hom_ext
      intro j; simp only [Functor.comp_obj, Category.assoc, limit.post_π, Category.id_comp]
      have E := Ht.fac (limit.cone (K ⋙ F)) j
      simp only [t] at E
      rw [Functor.mapCone_π_app, limit.cone_π, limit.cone_π] at E
      rw [E]
  mpr H := {
    preserves {s} Hs := ⟨{
      lift t := limit.lift _ t ≫ inv (limit.post K F) ≫ F.map (Hs.lift (limit.cone K))
      fac t j := by
        simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app, Category.assoc]
        rw [<- F.map_comp, Hs.fac, limit.cone_π]
        rw [<- limit.lift_π (F := K ⋙ F) t]
        congr
        rw [<- Category.id_comp (limit.π (K ⋙ F) j), <- H.inv_hom_id, Category.assoc]
        conv => arg 2; arg 2; simp only [limit.post]; rw [limit.lift_π]
        simp only [Functor.mapCone_π_app, limit.cone_π]
      uniq c m w := by
        simp only [Functor.mapCone_pt, Functor.comp_obj, Functor.mapCone_π_app] at m w
        let f : limit.cone K ⟶ s := {
          hom := (Hs.lift (limit.cone K))
          w := by intro j; simp
        }
        have Hf : IsIso f := IsLimit.hom_isIso (limit.isLimit K) Hs f
        have Hf' : IsIso f.hom := (Cone.forget K).map_isIso f
        have Hf'' :=  F.map_isIso f.hom
        simp [f] at Hf''
        rw [<- Category.assoc, <- Hf''.comp_inv_eq, H.eq_comp_inv]
        apply limit.hom_ext; intro j
        simp only [Functor.comp_obj, Category.assoc, limit.post_π, limit.lift_π]
        rw [<- w j]
        congr
        rw [Hf''.inv_comp_eq, <- F.map_comp, Hs.fac]
        simp
    }⟩
  }


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.4.5
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 充満忠実な関手 F : C → D は、任意の図式 K : J → C について、K の極限を反映する。余極限に
-- ついても同様。

#check fullyFaithful_reflectsLimits

theorem lemma_3_4_5 (F : C ⥤ D) [F.Full] [F.Faithful] (K : J ⥤ C) :
    ReflectsLimit K F where
  reflects {c} Hc := ⟨{
    lift s := F.preimage (Hc.lift (F.mapCone s))
    fac s j := by
      apply F.map_injective
      rw [F.map_comp, F.map_preimage]
      exact Hc.fac (F.mapCone s) j
    uniq s m w := by
      apply F.map_injective
      rw [F.map_preimage]
      apply Hc.uniq (F.mapCone s) (F.map m)
      intro j; simp only [Functor.mapCone_pt, Functor.comp_obj, Functor.mapCone_π_app]
      rw [<- F.map_comp, w]
  }⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 錐の圏の同値
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 圏同値 F : C → D と図式 K : J → C について、F は錐の圏の同値 Cone K ≃ Cone FK を誘導する。

#check Cone.functorialityEquivalence
#check Functor.mapConeInv

#print CategoryTheory.Equivalence

noncomputable def coneEquivalence (F : C ⥤ D) [F.IsEquivalence] (K : J ⥤ C) :
    Cone K ≌ Cone (K ⋙ F) where
  functor := {
    obj s := F.mapCone s
    map {s t} f := {
      hom := F.map f.hom
      w j := by simp
    }
    map_id s := by ext; simp
    map_comp {s t u} f g := by ext; simp
  }



  inverse := {
    obj s := by
      let f := F.objObjPreimageIso s.pt
      let t := s.extend f.hom
      refine {
        pt := F.objPreimage s.pt
        π := {
          app j := F.preimage (t.π.app j)
          naturality {i j} h := by
            apply F.map_injective
            rw [F.map_comp, F.map_preimage, F.map_comp, F.map_preimage]
            rw [<- K.comp_map, <- t.π.naturality h]
            simp
        }
      }
    map {s t} f := {
      hom := F.preimage ((F.objObjPreimageIso s.pt).hom ≫ f.hom ≫ (F.objObjPreimageIso t.pt).inv)
      w j := by
        simp only [Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt, Cone.extend_π,
          NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app]
        apply F.map_injective
        rw [F.map_comp, F.map_preimage, F.map_preimage, F.map_preimage]
        simp
    }
    map_id s := by ext; simp
    map_comp f g := by
      ext; simp only [Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt, Cone.extend_π,
        NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app, Cone.category_comp_hom,
        Category.assoc]
      apply F.map_injective; simp
  }

  unitIso := {
    hom := {
      app s := {
        hom := by
          simp only [Functor.id_obj, Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt,
            Cone.extend_π, NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app,
            Functor.mapCone_pt, Functor.mapCone_π_app, Functor.preimage_comp, Functor.preimage_map]
          exact F.preimage (F.objObjPreimageIso (F.obj s.pt)).inv
        w j := by
          simp only [Functor.id_obj, Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt,
            Cone.extend_π, NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app,
            Functor.mapCone_pt, Functor.mapCone_π_app, eq_mpr_eq_cast, cast_eq,
            Functor.preimage_comp, Functor.preimage_map]
          apply F.map_injective
          rw [F.map_comp, F.map_comp, F.map_preimage, F.map_preimage]
          rw [<- Category.assoc, Iso.inv_hom_id, Category.id_comp]
      }
      naturality {s t} f:= by
        ext
        dsimp only [Functor.id_obj, Functor.comp_obj, Functor.const_obj_obj, Lean.Elab.WF.paramLet,
          Cone.extend_pt, Cone.extend_π, NatTrans.comp_app, Functor.const_map_app,
          Functor.mapCone_pt, Functor.mapCone_π_app, Functor.id_map, eq_mpr_eq_cast, cast_eq,
          Cone.category_comp_hom, Functor.comp_map]
        rw [F.preimage_comp, F.preimage_comp, F.preimage_map]
        rw [<- Category.assoc, <- F.preimage_comp, Iso.inv_hom_id]
        rw [F.preimage_id, Category.id_comp]
    }
    inv := {
      app s := {
        hom := by
          simp only [Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt, Cone.extend_π,
            NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app, Functor.mapCone_pt,
            Functor.mapCone_π_app, Functor.preimage_comp, Functor.preimage_map, Functor.id_obj]
          exact (F.preimage (F.objObjPreimageIso (F.obj s.pt)).hom)
        w i := by simp
      }
      naturality {X Y} f:= by
        ext
        dsimp only [Functor.comp_obj, Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt,
          Cone.extend_π, NatTrans.comp_app, Functor.const_map_app, Functor.mapCone_pt,
          Functor.mapCone_π_app, Functor.id_obj, Functor.comp_map, eq_mpr_eq_cast, cast_eq,
          Cone.category_comp_hom, Functor.id_map]
        rw [F.preimage_comp, F.preimage_comp, F.preimage_map]
        rw [Category.assoc, Category.assoc, <- F.preimage_comp]
        rw [Iso.inv_hom_id, F.preimage_id, Category.comp_id]
    }
    hom_inv_id := by
      apply NatTrans.ext; ext s
      simp only [Functor.id_obj, Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt,
        Cone.extend_π, NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app,
        Functor.mapCone_pt, Functor.mapCone_π_app, eq_mpr_eq_cast, cast_eq, Cone.category_comp_hom,
        NatTrans.id_app, Cone.category_id_hom]
      rw [<- F.preimage_comp]; simp
    inv_hom_id := by
      apply NatTrans.ext; ext s
      simp only [Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt, Cone.extend_π,
        NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app, Functor.mapCone_pt,
        Functor.mapCone_π_app, Functor.id_obj, eq_mpr_eq_cast, cast_eq, Cone.category_comp_hom,
        NatTrans.id_app, Cone.category_id_hom]
      rw [<- F.preimage_comp]; simp
  }

  counitIso := {
    hom := {
      app s := {
        hom := by
          simp only [Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt, Cone.extend_π,
            NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app, Functor.mapCone_pt,
            Functor.id_obj]
          exact (F.objObjPreimageIso (s.pt)).hom
        w := by simp
      }
      naturality {s t} f := by ext; simp
    }
    inv := {
      app s := by
        simp only [Functor.id_obj, Functor.const_obj_obj, Lean.Elab.WF.paramLet, Cone.extend_pt,
          Cone.extend_π, NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app]
        refine {
          hom := by
            simp only [Functor.mapCone_pt]
            exact (F.objObjPreimageIso (s.pt)).inv
        }
      naturality {s t} f:= by
        ext; simp only [Functor.id_obj, Functor.const_obj_obj, Lean.Elab.WF.paramLet,
          Cone.extend_pt, Cone.extend_π, NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app,
          Functor.mapCone_pt, Functor.id_map, id_eq, Cone.category_comp_hom, Functor.comp_map,
          Functor.map_preimage, Iso.inv_hom_id_assoc]
    }
    hom_inv_id := by ext s; simp
    inv_hom_id := by ext s; simp
  }
  functor_unitIso_comp s := by
    -- Lean.Elab.WF.paramLet
    ext; simp only [Functor.mapCone_pt, Functor.const_obj_obj, Lean.Elab.WF.paramLet,
      Cone.extend_pt, Cone.extend_π, NatTrans.comp_app, Functor.comp_obj, Functor.const_map_app,
      Functor.mapCone_π_app, Functor.id_obj, eq_mpr_eq_cast, cast_eq, Functor.map_preimage, id_eq,
      Cone.category_comp_hom, Iso.inv_hom_id, Cone.category_id_hom]


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.4.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 圏同値 F : C → D は、任意の図式 K : J → C について、K の極限を保存し、反映し、創出する。
-- 余極限についても同様。

#check Adjunction.isEquivalencePreservesLimits

-- Functor.mapConeInv
theorem lemma_3_4_6_preserves (F : C ⥤ D) [F.IsEquivalence] (K : J ⥤ C) :
    PreservesLimit K F where
  preserves {c} Hc := ⟨{
    lift μ := by
      simp only [Functor.mapCone_pt]
      let f := F.objObjPreimageIso μ.pt
      let ν := F.mapConeInv μ
      exact f.inv ≫ F.map (Hc.lift ν)
    fac s i := by
      simp only [Functor.comp_obj, Functor.mapCone_pt, id_eq, Functor.mapCone_π_app, Category.assoc]
      erw [<- F.map_comp, Hc.fac]
      conv => arg 1; arg 2; change (F.mapCone (F.mapConeInv s)).π.app i
      rw [<- (K.mapConeMapConeInv F s).hom.w i]
      conv => arg 1; arg 2; arg 1; change (F.objObjPreimageIso s.pt).hom
      erw [Iso.inv_hom_id_assoc]
    uniq s m w := by
      simp only [Functor.mapCone_pt, id_eq]
      let m' : (F.mapConeInv s).pt ⟶ c.pt := F.preimage ((F.objObjPreimageIso s.pt).hom ≫ m)
      rw [<- Hc.uniq (F.mapConeInv s) m']<;> simp only [m']<;> clear m'
      · erw [F.map_preimage, Iso.inv_hom_id_assoc]
      · intro i
        apply F.map_injective
        erw [F.map_comp, F.map_preimage]
        erw [Category.assoc, w i]
        conv => arg 2; change (F.mapCone (F.mapConeInv s)).π.app i
        rw [<- (K.mapConeMapConeInv F s).hom.w i]
        rfl
  }⟩

#check Functor.reflectsLimits_of_isEquivalence

theorem lemma_3_4_6_reflects (F : C ⥤ D) [F.IsEquivalence] (K : J ⥤ C) :
  ReflectsLimit K F := (fullyFaithful_reflectsLimits F).reflectsLimitsOfShape.reflectsLimit

#check Functor.createsLimitsOfIsEquivalence
#print CreatesLimit
noncomputable instance lemma_3_4_6_creates (F : C ⥤ D) [F.IsEquivalence] (K : J ⥤ C) :
    CreatesLimit K F where
  lifts c _ := {
    liftedCone := F.mapConeInv c
    validLift := K.mapConeMapConeInv F c
  }





-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 定義3.4.7
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 関手 F : C → D が図式 K の極限を厳密に創出するとは、FK 上の任意の極限錐について、その錐の
-- K 上の錐への持ち上げがただ一つ存在し、しかもその持ち上げが C の極限錐であることをいう。
-- 余極限についても双対的に定める。

#print LiftsToLimit

structure MyStrictLift (K : J ⥤ C) (F : C ⥤ D) (d : Cone (K ⋙ F)) where
  liftedCone : Cone K
  validLift : F.mapCone liftedCone = d
  unique : ∀ c : Cone K, F.mapCone c = d → c = liftedCone
  makesLimit : IsLimit liftedCone

class MyStrictlyCreatesLimit (K : J ⥤ C) (F : C ⥤ D) where
  lifts : ∀ d : Cone (K ⋙ F), IsLimit d → MyStrictLift K F d

structure MyStrictColift (K : J ⥤ C) (F : C ⥤ D) (d : Cocone (K ⋙ F)) where
  liftedCocone : Cocone K
  validLift : F.mapCocone liftedCocone = d
  unique : ∀ c : Cocone K, F.mapCocone c = d → c = liftedCocone
  makesColimit : IsColimit liftedCocone

class MyStrictlyCreatesColimit (K : J ⥤ C) (F : C ⥤ D) where
  lifts : ∀ d : Cocone (K ⋙ F), IsColimit d → MyStrictColift K F d

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 連結な圏（定義3.4.7 の後）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 圏 J が連結であるとは、J が空でなく、任意の二つの対象が射の有限のジグザグで結ばれること。
-- 図式が連結であるとは、その添字圏が連結であること。

#print Relation.ReflTransGen

def myZag (j k : J) : Prop := Nonempty (j ⟶ k) ∨ Nonempty (k ⟶ j)
class MyIsConnected (J : Type v) [SmallCategory J] : Prop where
  nonempty : Nonempty J
  zigzag : ∀ j k : J, Relation.ReflTransGen myZag j k

#print IsConnected
#print IsPreconnected

theorem myIsConnected_iff : MyIsConnected J ↔ IsConnected J where
mp H := by
  rcases H with ⟨HJ, H⟩
  refine {
    is_nonempty := HJ
    toIsPreconnected := {
      iso_constant {X} F i := ⟨by
        apply NatIso.ofComponents ?_ ?_
        · intro j; simp only [Functor.const_obj_obj]
          have E : F.obj i = F.obj j := by {
            induction H i j with
            | refl  => rfl
            | @tail  a b H' H IH =>
              rw [IH]
              rcases H with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩<;>ext
              · exact Discrete.eq_of_hom (F.map f)
              · exact (Discrete.eq_of_hom (F.map f)).symm
          }
          rw [E]
        · intro _ _ _
          exact Subsingleton.elim _ _
      ⟩
    }
  }
mpr H := {
  nonempty := H.is_nonempty
  zigzag := by
    let F : J ⥤ Discrete  (Quot (Relation.ReflTransGen myZag)) := {
      obj j := ⟨Quot.mk (Relation.ReflTransGen myZag) j⟩
      map {i j} f := {
        eq := by
          simp only
          apply Quot.sound
          apply Relation.ReflTransGen.tail; swap
          · left; exact ⟨f⟩
          · constructor
      }
    }
    intro i j
    let σ := (H.iso_constant F i).some.hom.app j
    simp only [Functor.const_obj_obj, F] at σ
    rcases σ with ⟨E⟩; simp only at E
    rw [Quot.eq] at E
    have hz : Std.Symm (@myZag J _) := ⟨fun _ _ h => h.symm⟩
    have hs : Std.Symm (Relation.ReflTransGen (@myZag J _)) := Relation.ReflTransGen.stdSymm
    induction E with
    | rel _ _ h => exact hs.symm _ _ h
    | refl _ => exact Relation.ReflTransGen.refl
    | symm _ _ _ ih => exact hs.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
}



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.4.8
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の対象 c ∈ C について、忘却関手 Π : c/C → C は、任意の図式に対して極限を厳密に創出し、
連結な図式に対して余極限を厳密に創出する。したがって、任意の添字圏 J について、C が J 型の
極限を持てば c/C も持ち、J が連結で C が J 型の余極限を持てば c/C も持つ。
-/

#print Under
#print StructuredArrow
#print Comma
#print CommaMorphism
#print Under.forget

-- 忘却関手 Π : c/C → C を自分で組む。射 f : c → x をその終域 x に送る。
def myUnderForget (c : C) : Under c ⥤ C where
  obj f := f.right
  map {x y} f := f.right
  map_id x := by simp
  map_comp {x y z} f g := by simp

#check Under.forgetCone

-- 頂点 c、脚が各対象 f : c → x の f 自身である、Π の上の錐。
def myUnderForgetCone (c : C) : Cone (Under.forget c) where
  pt := c
  π := {
    app i := i.hom
    naturality {f g} F:= by simp
  }

#check Cone.whisker

-- 錐 s : Cone K を関手 E : J' → J で引き戻した錐。
def myConeWhisker {J' : Type v} [SmallCategory J'] {K : J ⥤ C} (E : J' ⥤ J) (s : Cone K) :
    Cone (E ⋙ K) where
  pt := s.pt
  π := Functor.whiskerLeft E s.π



#check StructuredArrow.createsLimitsOfShape

noncomputable instance prop_3_4_8_limits (c : C) (K : J ⥤ Under c) :
    MyStrictlyCreatesLimit K (Under.forget c) where
  lifts d H := {
    liftedCone := {
      pt := {
        left := ⟨PUnit.unit⟩
        right := d.pt
        hom := H.lift ((Under.forgetCone c).whisker K)
      }
      π := {
        app i := {
          left := 𝟙 _
          right := d.π.app i
          w := by
            simp only [Functor.const_obj_obj, Functor.id_obj, Discrete.functor_map_id,
              Category.id_comp]
            erw [Functor.id_map, H.fac]; simp
        }
        naturality {i j} f:= by
          ext; simp only [Functor.const_obj_obj, Functor.const_obj_map]
          erw [Under.comp_right, Under.comp_right]; simp only [Under.id_right, Category.id_comp]
          simp only [Under.Hom.right]
          erw [<- d.π.naturality f]
          simp only [Functor.const_obj_obj, Functor.comp_obj, Under.forget_obj,
            Functor.const_obj_map]
          erw [Category.id_comp]
      }



    }
    validLift := by
      simp only [Functor.const_obj_obj]
      rw [Cone.mk.injEq]; constructor
      simp only [Functor.mapCone_pt, Under.forget_obj]
      apply heq_of_eq; ext j; simp only [Functor.mapCone_pt, Under.forget_obj,
        Functor.const_obj_obj, Functor.comp_obj, Functor.mapCone_π_app]
      erw [Under.forget_map]
    unique s w := by
      rcases s with ⟨f, σ⟩
      simp only [Functor.const_obj_obj, Cone.mk.injEq]
      have E : f = { left := { as := PUnit.unit }, right := d.pt, hom := H.lift (Cone.whisker K (Under.forgetCone c)) } := by {
        subst d; simp only [Functor.mapCone_pt, Under.forget_obj]
        erw [Comma.mk.injEq]; simp only [Under.under_left, Functor.const_obj_obj, Functor.id_obj,
          true_and]
        rw [<- H.uniq ((Cone.whisker K (Under.forgetCone c))) f.hom]
        intro j; simp only [Cone.whisker_pt, Functor.comp_obj, Under.forget_obj, Functor.mapCone_pt,
          Functor.mapCone_π_app, Under.forget_map, Cone.whisker_π, Functor.whiskerLeft_app,
          Under.forgetCone_π_app]
        exact  f.w (σ.app j)
      }
      use E
      subst E; simp only [heq_eq_eq]
      ext j; simp only [Functor.const_obj_obj]
      simp only [Under.Hom.right]
      have E := congr_arg_heq (fun d => d.π) w
      simp only [Functor.mapCone, Cone.functoriality, Under.forget_obj, Under.forget_map,
        heq_eq_eq] at E
      rw [<- E]
    makesLimit := {
      lift s := {
        left := 𝟙 _
        right := H.lift ((Under.forget c).mapCone s)
        w := by
          simp only [Functor.const_obj_obj, Functor.id_obj, Discrete.functor_map_id]
          erw [Category.id_comp, Functor.id_map]
          apply H.hom_ext
          intro j; simp only [Cone.whisker_pt, Functor.comp_obj, Under.forget_obj]
          erw [Category.assoc, H.fac, H.fac]
          simp only [Cone.whisker_pt, Cone.whisker_π, Functor.whiskerLeft_app,
            Under.forgetCone_π_app, Functor.mapCone_pt, Under.forget_obj, Functor.mapCone_π_app,
            Under.forget_map]
          exact (s.pt.w (s.π.app j)).symm

      }
      fac s j := by
        ext
        erw [Under.comp_right]
        simp only [Functor.const_obj_obj, Under.Hom.right]
        erw [H.fac ((Under.forget c).mapCone s) j]
        rfl
      uniq s m w := by
        simp only [Functor.const_obj_obj] at m w
        ext; simp only [Under.Hom.right]
        apply H.uniq ((Under.forget c).mapCone s)
        intro j; simp only [Functor.mapCone_pt, Under.forget_obj, Functor.comp_obj,
          Functor.mapCone_π_app, Under.forget_map]
        erw [<- w j, Under.comp_right]
    }
  }

#check Comma.hasLimitsOfShape

#print HasLimitsOfShape
theorem prop_3_4_8_hasLimits (c : C) [HasLimitsOfShape J C] : HasLimitsOfShape J (Under c) where
  has_limit F := by
    have H := (prop_3_4_8_limits c F).lifts
    have HF := H (limit.cone (F ⋙ Under.forget c)) (limit.isLimit (F ⋙ Under.forget c))
    exact ⟨HF.liftedCone, HF.makesLimit⟩

#check Under.createsColimitsOfShapeForgetOfIsConnected

noncomputable instance prop_3_4_8_colimits [IsConnected J] (c : C) (K : J ⥤ Under c) :
    MyStrictlyCreatesColimit K (Under.forget c) where
  lifts d Hd := {
    liftedCocone := {
      pt := {
        left := ⟨PUnit.unit⟩
        right := d.pt
        hom := (K.obj (Classical.arbitrary J)).hom ≫ (d.ι.app ( Classical.arbitrary J))
      }
      ι := {
        app j := {
          left := 𝟙 _
          right := d.ι.app j
          w := by
            simp only [Functor.const_obj_obj, Functor.id_obj, Discrete.functor_map_id,
              Category.id_comp]
            change _ =  (K.obj j).hom ≫ d.ι.app j
            set i := (Classical.arbitrary J)
            have H := isPreconnected_zigzag i j
            induction H with
            | refl => rfl
            | @tail k l H Hkl IH =>
              rcases Hkl with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
              · erw [<- (K.map f).w, Category.assoc, IH]
                have E := d.ι.naturality f
                simp only [Functor.comp_obj, Under.forget_obj, Functor.const_obj_obj,
                  Functor.comp_map, Under.forget_map, Functor.const_obj_map] at E
                erw [E, Category.comp_id]
              · erw [IH, <- (K.map f).w]
                have E := d.ι.naturality f
                simp only [Functor.comp_obj, Under.forget_obj, Functor.const_obj_obj,
                  Functor.comp_map, Under.forget_map, Functor.const_obj_map] at E
                erw [Category.assoc, E, Category.comp_id]
        }
        naturality {i j} f := by
          simp only [Functor.const_obj_obj, Functor.id_obj, Functor.const_obj_map]
          ext
          erw [Under.comp_right, Under.comp_right]
          simp only [Under.Hom.right, Under.id_right]
          erw [Category.comp_id]
          have E := d.ι.naturality f
          simp only [Functor.comp_obj, Under.forget_obj, Functor.const_obj_obj, Functor.comp_map,
            Under.forget_map, Functor.const_obj_map] at E
          erw [E, Category.comp_id]
      }

    }
    validLift := by
      simp only [Functor.const_obj_obj, Functor.id_obj]
      rw [Cocone.mk.injEq]; constructor
      · simp
      · apply heq_of_eq; ext j
        simp only [Functor.comp_obj, Under.forget_obj, Functor.mapCocone_pt, Functor.const_obj_obj,
          Functor.mapCocone_ι_app]
        erw [Under.forget_map]
    unique s E := by
      rcases s with ⟨f, σ⟩
      have hf : f = {
          left := ⟨PUnit.unit⟩
          right := d.pt
          hom := (K.obj (Classical.arbitrary J)).hom ≫ d.ι.app (Classical.arbitrary J) } := by
        subst E
        have w := Under.w (σ.app (Classical.arbitrary J))
        dsimp at w ⊢
        rw [w]
        rfl
      simp only [Cocone.mk.injEq]
      subst hf
      simp only [heq_eq_eq, true_and]
      ext j
      simp only [Functor.const_obj_obj, Under.Hom.right]
      have E' := congr_arg_heq (fun d => d.ι) E
      simp only [Functor.mapCocone, Cocone.functoriality, Under.forget_obj, Under.forget_map,
        heq_eq_eq] at E'
      exact NatTrans.congr_app E' j
    makesColimit := {
      desc s := {
        left := 𝟙 _
        right := Hd.desc ((Under.forget c).mapCocone s)
        w := by
          simp only [Functor.const_obj_obj, Functor.id_obj, Discrete.functor_map_id,
            Category.id_comp]
          erw [Functor.id_map, Category.assoc, Hd.fac]
          dsimp only [Functor.mapCocone_pt, Under.forget_obj, Functor.mapCocone_ι_app,
            Under.forget_map]
          rw [(s.ι.app (Classical.arbitrary J)).w]
          simp
      }
      fac s i := by
        simp only [Functor.const_obj_obj, Functor.id_obj]
        ext; erw [Under.comp_right]
        simp only [Under.Hom.right]
        erw [Hd.fac]; simp
      uniq s m w := by
        simp only [Functor.const_obj_obj, Functor.id_obj] at m w ⊢
        ext; simp only [Under.Hom.right]
        rw [<- (Hd.uniq ((Under.forget c).mapCocone s) m.right)]
        simp only [Functor.comp_obj, Under.forget_obj, Functor.mapCocone_pt,
          Functor.mapCocone_ι_app, Under.forget_map]
        intro j
        have E := congr_arg Under.Hom.right (w j)
        erw [Under.comp_right] at E
        simp only [Under.Hom.right] at E
        rw [E]
    }
  }


#check Under.hasColimitsOfShape_of_isConnected

theorem prop_3_4_8_hasColimits [IsConnected J] (c : C) [HasColimitsOfShape J C] :
    HasColimitsOfShape J (Under c) where
  has_colimit F := by
    have H := prop_3_4_8_colimits c F
    have HF := H.lifts (colimit.cocone (F ⋙ Under.forget c)) (colimit.isColimit (F ⋙ Under.forget c))
    exact ⟨HF.liftedCocone, HF.makesColimit⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.4.9
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小圏 A について、忘却関手 ev : Cᴬ → C^{ob A} は、任意の図式に対して極限を厳密に創出する。
したがって、任意の添字圏 J について、C が J 型の極限を持てば、(i) Cᴬ も J 型の極限を持ち、
(ii) 各 a ∈ A について評価関手 ev_a : Cᴬ → C は J 型の極限を保存する。余極限についても同様。

構成: 小圏 A の対象を極大な離散部分圏 ob A ↪ A と見て、忘却関手 ev を組む。ev が極限を
      厳密に創出することを示し、そこから (i) と (ii) を示す。
-/

def myObIncl (A : Type v) [SmallCategory A] : Discrete A ⥤ A where
  obj a := a.as
  map f := eqToHom (Discrete.eq_of_hom f)

def myEv (A : Type v) [SmallCategory A] (C : Type u) [Category.{v} C] :
    (A ⥤ C) ⥤ (Discrete A ⥤ C) where
  obj G := myObIncl A ⋙ G
  map α := Functor.whiskerLeft (myObIncl A) α

noncomputable def prop_3_4_9 (A : Type v) [SmallCategory A] (K : J ⥤ (A ⥤ C)) :
    MyStrictlyCreatesLimit K (myEv A C) where
  lifts d Hd := {
    liftedCone := _
    validLift := _
    unique := _
    makesLimit := _
  }




#check functorCategoryHasLimitsOfShape

theorem prop_3_4_9_i (A : Type v) [SmallCategory A] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (A ⥤ C) := sorry

#check evaluation_preservesLimitsOfShape

theorem prop_3_4_9_ii (A : Type v) [SmallCategory A] [HasLimitsOfShape J C] (a : A) :
    PreservesLimitsOfShape J ((evaluation A C).obj a) := sorry

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
補題3.4.3 の双対。任意の図式 K : J → C と関手 F : C → D について、colim K と colim FK が
ともに存在するとき標準的な射 κ : colim FK → F colim K が定まり、F が K の余極限を保存するのは
この射が同型であるとき、かつそのときに限る。
-/

noncomputable def ex_3_4_i_i (K : J ⥤ C) (F : C ⥤ D) [HasColimit K] [HasColimit (K ⋙ F)] :
    colimit (K ⋙ F) ⟶ F.obj (colimit K) := sorry

#check preservesColimit_of_isIso_post

theorem ex_3_4_i_ii (K : J ⥤ C) (F : C ⥤ D) [HasColimit K] [HasColimit (K ⋙ F)] :
    PreservesColimit K F ↔ IsIso (ex_3_4_i_i K F) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の関手 F : C → Set について、射影関手 Π : ∫F → C は、(i) ΠK の極限が C に存在し F が
それを保存するような任意の図式 K : J → ∫F に対して K の極限を厳密に創出し、(ii) J が連結で
ΠK の余極限が C に存在するような任意の図式 K : J → ∫F に対して K の余極限を厳密に創出する。
-/

noncomputable def ex_3_4_ii_i (F : C ⥤ Type v) (K : J ⥤ F.Elements)
    [HasLimit (K ⋙ Functor.Elements.π F)] [PreservesLimit (K ⋙ Functor.Elements.π F) F] :
    MyStrictlyCreatesLimit K (Functor.Elements.π F) := sorry

noncomputable def ex_3_4_ii_ii [IsConnected J] (F : C ⥤ Type v) (K : J ⥤ F.Elements) :
    MyStrictlyCreatesColimit K (Functor.Elements.π F) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 関手 F : C → D と図式 K : J → C について、K の極限が C に存在して F がそれを保存し、F が
-- 同型を反映するならば、F は K の極限を創出する。

#check createsLimitOfReflectsIso

noncomputable def ex_3_4_iii (K : J ⥤ C) (F : C ⥤ D) [HasLimit K] [PreservesLimit K F]
    [F.ReflectsIsomorphisms] : CreatesLimit K F := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 忘却関手 U : Set∗ → Set と U : Top∗ → Top は余積を保存しない。これは命題3.4.8 の連結性の
-- 仮定が落とせないことを示す。

theorem ex_3_4_iv_set :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (Under.forget (PUnit.{v + 1} : Type v)) :=
  sorry

theorem ex_3_4_iv_top :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (Under.forget (TopCat.of PUnit.{v + 1})) :=
  sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.v
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏の積 ∏_{i∈I} C_i について、(i) 各射影関手 π_k : ∏ C_i → C_k は任意の図式に対して極限を
保存し、(ii) 射影関手は共同で極限を創出する。すなわち任意の図式 F : J → ∏ C_i について、
各成分 π_k F が極限を持てば、それらが F の極限の成分を定める。したがって、任意の添字圏 J に
ついて、積の圏が J 型の極限を持つのは各成分が持つとき、かつそのときに限る。
-/

section

variable {I : Type w} (Cs : I → Type u) [∀ i, Category.{v} (Cs i)]

theorem ex_3_4_v_i (k : I) : PreservesLimitsOfShape J (Pi.eval Cs k) := sorry

def ex_3_4_v_ii (F : J ⥤ ∀ i, Cs i) (c : ∀ k, LimitCone (F ⋙ Pi.eval Cs k)) : Cone F where
  pt := fun k => (c k).cone.pt
  π := sorry

def ex_3_4_v_ii_isLimit (F : J ⥤ ∀ i, Cs i) (c : ∀ k, LimitCone (F ⋙ Pi.eval Cs k)) :
    IsLimit (ex_3_4_v_ii Cs F c) := sorry

theorem ex_3_4_v_hasLimits [∀ i, Nonempty (Cs i)] :
    HasLimitsOfShape J (∀ i, Cs i) ↔ ∀ i, HasLimitsOfShape J (Cs i) := sorry

end

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
レトラクト B →s A →r B, rs = id_B が A 上の分裂冪等射 sr を定めるとき、(i) B →s A ⇉ A
（id_A と sr）は等化子図式、A ⇉ A →r B は余等化子図式であり、(ii) B は冪等射 sr が定める
図式の極限かつ余極限であり、(iii) これらの極限・余極限は任意の関手 G : C → D で保存される。
-/

section

variable {A B : C} (s : B ⟶ A) (r : A ⟶ B)

theorem ex_3_4_vi_i_fork_condition (h : s ≫ r = 𝟙 B) : s ≫ 𝟙 A = s ≫ r ≫ s := sorry

def ex_3_4_vi_i_equalizer (h : s ≫ r = 𝟙 B) :
    IsLimit (Fork.ofι s (ex_3_4_vi_i_fork_condition s r h)) := sorry

theorem ex_3_4_vi_i_cofork_condition (h : s ≫ r = 𝟙 B) : 𝟙 A ≫ r = (r ≫ s) ≫ r := sorry

def ex_3_4_vi_i_coequalizer (h : s ≫ r = 𝟙 B) :
    IsColimit (Cofork.ofπ r (ex_3_4_vi_i_cofork_condition s r h)) := sorry

theorem ex_3_4_vi_iii_equalizer (h : s ≫ r = 𝟙 B) (G : C ⥤ D) :
    PreservesLimit (parallelPair (𝟙 A) (r ≫ s)) G := sorry

theorem ex_3_4_vi_iii_coequalizer (h : s ≫ r = 𝟙 B) (G : C ⥤ D) :
    PreservesColimit (parallelPair (𝟙 A) (r ≫ s)) G := sorry

end
