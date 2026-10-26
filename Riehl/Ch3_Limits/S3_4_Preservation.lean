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
import Mathlib.CategoryTheory.Limits.Pi
import Mathlib.Topology.Category.TopCat.Basic
import Riehl.Topics.Embedding

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
                Mathlib の名前で書く。余極限側の錐の像 `mapCocone` も、演習3.4.i と
                演習3.4.vi の statement が `Functor.mapCocone` を使うので組む。錐の像が錐の
                射も写して関手 Cone K ⥤ Cone (K ⋙ F) をなすことは本にないが、錐の同型を F で
                写すのに要るので `coneFunctoriality` として組む（Mathlib の
                `Cone.functoriality`）。対象の部分は `Functor.mapCone`、射の頂点成分は F で
                写した射として書いて渡し、錐の射の条件と関手則を演習にする
  定義3.4.1    保存・反映は Mathlib の `PreservesLimit`・`ReflectsLimit` とフィールド単位
                で同じなので、写しを書いて渡し、statement は Mathlib で書く。創出は Mathlib
                の定義と形が違う。本は「FK が極限を持てば K も持ち、そのとき錐が極限錐であることと像が
                極限錐であることが同値」という命題で、Mathlib の `CreatesLimit` は極限錐の
                持ち上げと同型 `LiftableCone` を data として持つ。本の形を `CreatesLimit'`
                として置き、`Nonempty (CreatesLimit K F)` との同値を演習にする。
                同値の証明では同型を介して極限錐を移すので、本にない補題「極限錐と同型な錐は
                極限錐」を `isLimitOfIso` として直前に置く（Mathlib の
                `IsLimit.ofIsoLimit`）。創出の statement は Mathlib の `CreatesLimit` を返す `def` で書く。余極限の
                保存 `PreservesColimit'` は演習3.4.i と演習3.4.vi で使うので写しを置く。
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
                持ち上げの中身を `StrictLift`（`validLift` を `≅` から `=` に替え、
                `unique` を足したもの）に束ね、`StrictlyCreatesLimit` はそれを返す
                `lifts` 1 本とする。Mathlib と同じく Prop ではなくデータなので、これを
                結論とする主張は `theorem` でなく `noncomputable def` になる。命題3.4.8
                の余極限側のために双対 `StrictlyCreatesColimit` も置く
  連結な圏      本の定義（空でなく、任意の二対象が射の有限のジグザグで結ばれる）を
                `IsConnected'` として置く。ジグザグは一歩の関係 `Zag'` の反射推移閉包
                `Relation.ReflTransGen` で書く。Mathlib の `IsConnected` は「任意の離散圏への
                関手が定関手と同型」の形で定義されているので、同値 `isConnected'_iff` を演習
                に置き、statement は `IsConnected` で書く
  命題3.4.8     c/C（演習1.1.iii）は Mathlib の `Under c`、忘却関手は `Under.forget c`。
                `Under c` はコンマ圏 `Comma (Functor.fromPUnit c) (𝟭 C)` で、本の c/C に空の
                `left` 成分が付いた形。本の c/C とは形が違うので、使う直前に `#print` で定義を見せる。
                忘却関手は `underForget` として組み直す演習を置くが、statement は
                `Under.forget c` で書く。証明で使う Π の上の錐 `Under.forgetCone` と錐の
                引き戻し `Cone.whisker` も `underForgetCone`・`coneWhisker` として組む
                演習を置く。strict な創出の 2 本と、「したがって c/C は極限・連結な余極限を
                持つ」の 2 本に割る
  命題3.4.9     ob A ↪ A を `obIncl`（`Discrete A ⥤ A`。Mathlib の `Discrete.functor id` と
                `rfl` で一致）、忘却関手 ev を `ev`（`Discrete.functor id`
                との前合成）として組む。どちらも義務が自動で閉じるので書き切って渡す。
                Mathlib に ev の名前の付いた対応物はない（`Functor.whiskeringLeft` の特殊化）
                ので、statement は `ev` を参照する。創出は本の「厳密に創出する」でなく
                定義3.4.1 の創出（Mathlib の `CreatesLimit`）で述べる。落ちるのは持ち上げの
                等式での一意性で、本文の後の使用箇所（3.5.2 の注意、定理3.5.11、系4.5.15、
                系4.7.13）はどれも使わない。各点の極限錐は本と同じく演習3.4.v から取る。
                本が C^{ob A} ≅ ∏_{ob A} C で済ませている同一視は Mathlib の圏同値
                `piEquivalenceFunctorDiscrete` と、評価関手と `Pi.eval` の整合
                `piEquivalenceFunctorDiscreteCompEvaluationIso` で、どちらもこれまでの
                演習ファイルに出ていないので、同じ形で自前に組む演習を置く。同一視に沿って
                演習3.4.v を運ぶ補題 `discreteEvaluation_preservesLimitsOfShape` を置き、
                創出の証明はそれを使う。主張は創出と (i)・(ii) の 3 本に割る。
                Mathlib は同じ命題を ev なしで各点の評価関手 `(evaluation A C).obj a` の族に
                ついて述べる（`evaluationJointlyReflectsLimits`・`combineCones`・
                `evaluateCombinedCones`・`combinedIsLimit`）。本文の後の使用箇所はこの形で
                当たるので、別セクション「命題3.4.9（Mathlib の形）」として同じ形で自前に
                組む演習を置く
  演習3.4.i     (i) の κ の型は本が与えるので書く。(ii) は (i) で組んだ κ について述べる
  演習3.4.ii    要素の圏 ∫F（定義2.4.1）とその射影は既知の定義として Mathlib の
                `Functor.Elements`・`Functor.Elements.π` を使う。厳密な創出の 2 本に加えて、
                定義3.4.1 の創出 `CreatesLimit`・`CreatesColimit` で述べた 2 本も置く
                （`validLift` が錐の等式から同型になり、`Cone.ext` で示せる）
  演習3.4.iv    Set∗ を ∗/Set、すなわち `Under (PUnit : Type v)`、Top∗ を
                `Under (TopCat.of PUnit)` で取る。余積を保存しないことを、二項余積の形
                `Discrete WalkingPair` の余極限を保存しないこととして述べる
  演習3.4.v     「積の圏が極限を持つのは各成分が持つとき、かつそのときに限る」は、成分の圏が
                一つでも空だと成り立たない（積の圏が空になり、左辺が空虚に真になる）。
                各成分が空でないことを仮定に加える。(ii) の錐は頂点を書いて渡し、脚と
                極限錐であることを演習にする。(i) の証明が (ii) の錐の組み立てを使うので、
                (ii) の構成を (i) の前に置く。圏の積 ∏ C_i とその射影は既知の定義として
                Mathlib の `∀ i, Cs i`・`Pi.eval` を使う。添字の型は Mathlib の
                `Limits.Pi` の宇宙に合わせて `Type v` に限る（命題3.4.9 で使う添字は
                `A : Type v` なので足りる）
  演習3.4.vi    レトラクトの条件 rs = id_B は `s ≫ r = 𝟙 B`、冪等射 sr は `r ≫ s`。
                等化子図式・余等化子図式の条件式を別の宣言に割る
  本にない      次は本に対応する概念がなく、Mathlib の道具として statement に使う。
  Mathlib の    `Relation.ReflTransGen`（関係の反射推移閉包。連結な圏）、
  道具          `TopCat.of`（演習3.4.iv）

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

namespace Riehl

universe v u u'

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
def mapCone (F : C ⥤ D) {K : J ⥤ C} (c : Cone K) : Cone (K ⋙ F) where
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

def coneFunctoriality (K : J ⥤ C) (F : C ⥤ D) : Cone K ⥤ Cone (K ⋙ F) where
  obj c := F.mapCone c
  map {X Y} f := {
    hom := F.map f.hom
    w j := by simp
  }
  map_id X := by ext; simp
  map_comp {X Y Z} f g := by ext; simp

#check Functor.mapCocone

def mapCocone (F : C ⥤ D) {K : J ⥤ C} (c : Cocone K) : Cocone (K ⋙ F) where
  pt := F.obj c.pt
  ι := {
    app j := F.map (c.ι.app j)
    naturality := sorry
  }

#check limit.post

noncomputable def limitPost (K : J ⥤ C) (F : C ⥤ D) [HasLimit K] [HasLimit (K ⋙ F)] :
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
class PreservesLimit' (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves : ∀ {c : Cone K}, IsLimit c → Nonempty (IsLimit (F.mapCone c))

#print ReflectsLimit

class ReflectsLimit' (K : J ⥤ C) (F : C ⥤ D) : Prop where
  reflects : ∀ {c : Cone K}, IsLimit (F.mapCone c) → Nonempty (IsLimit c)

class CreatesLimit' (K : J ⥤ C) (F : C ⥤ D) : Prop where
  creates : HasLimit (K ⋙ F) →
    HasLimit K ∧ ∀ c : Cone K, Nonempty (IsLimit c) ↔ Nonempty (IsLimit (F.mapCone c))

-- 極限錐と同型な錐は極限錐である。創出の二つの定義の同値で使う。

#check IsLimit.ofIsoLimit

def isLimitOfIso {K : J ⥤ C} {c d : Cone K} (Hc : IsLimit c) (σ : c ≅ d) : IsLimit d where
  lift s := Hc.lift s ≫ σ.hom.hom
  fac s j := by
    rw [Category.assoc, σ.hom.w, Hc.fac]
  uniq s m w := by
    rw [<- Hc.uniq s (m ≫ σ.inv.hom)]
    · simp
    · intro j; rw [Category.assoc, σ.inv.w, w]







#print CreatesLimit
#print LiftableCone

theorem createsLimit'_iff (K : J ⥤ C) (F : C ⥤ D) :
    CreatesLimit' K F ↔ Nonempty (CreatesLimit K F) where
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

class PreservesColimit' (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves : ∀ {c : Cocone K}, IsColimit c → Nonempty (IsColimit (F.mapCocone c))

#print PreservesLimitsOfShape

class PreservesLimitsOfShape' (J : Type v) [SmallCategory J] (F : C ⥤ D) : Prop where
  preservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F

#print PreservesColimitsOfShape

class PreservesColimitsOfShape' (J : Type v) [SmallCategory J] (F : C ⥤ D) : Prop where
  preservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F

#print Functor.ReflectsIsomorphisms

class ReflectsIsomorphisms' (F : C ⥤ D) : Prop where
  reflects : ∀ {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)], IsIso f

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.4.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- C と D が J 型の極限を持つとき、関手 F : C → D と図式 K : J → C について、F が K の極限を
-- 保存するのは、comparison map κ : F(lim K) → lim FK が同型であるとき、かつそのときに限る。

#check preservesLimit_of_isIso_post
#print HasLimitsOfShape

theorem preservesLimit_iff_isIso_post [HasLimitsOfShape J C] [HasLimitsOfShape J D] (F : C ⥤ D)
    (K : J ⥤ C) : PreservesLimit K F ↔ IsIso (limit.post K F) where
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

theorem reflectsLimit_of_fullyFaithful (F : C ⥤ D) [F.Full] [F.Faithful] (K : J ⥤ C) :
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
theorem preservesLimit_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence] (K : J ⥤ C) :
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

theorem reflectsLimit_of_isEquivalence (F : C ⥤ D) [F.IsEquivalence] (K : J ⥤ C) :
  ReflectsLimit K F := (fullyFaithful_reflectsLimits F).reflectsLimitsOfShape.reflectsLimit

#check Functor.createsLimitsOfIsEquivalence
#print CreatesLimit
noncomputable instance createsLimitOfIsEquivalence (F : C ⥤ D) [F.IsEquivalence] (K : J ⥤ C) :
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

structure StrictLift (K : J ⥤ C) (F : C ⥤ D) (d : Cone (K ⋙ F)) where
  liftedCone : Cone K
  validLift : F.mapCone liftedCone = d
  unique : ∀ c : Cone K, F.mapCone c = d → c = liftedCone
  makesLimit : IsLimit liftedCone

class StrictlyCreatesLimit (K : J ⥤ C) (F : C ⥤ D) where
  lifts : ∀ d : Cone (K ⋙ F), IsLimit d → StrictLift K F d

structure StrictColift (K : J ⥤ C) (F : C ⥤ D) (d : Cocone (K ⋙ F)) where
  liftedCocone : Cocone K
  validLift : F.mapCocone liftedCocone = d
  unique : ∀ c : Cocone K, F.mapCocone c = d → c = liftedCocone
  makesColimit : IsColimit liftedCocone

class StrictlyCreatesColimit (K : J ⥤ C) (F : C ⥤ D) where
  lifts : ∀ d : Cocone (K ⋙ F), IsColimit d → StrictColift K F d

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 連結な圏（定義3.4.7 の後）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 圏 J が連結であるとは、J が空でなく、任意の二つの対象が射の有限のジグザグで結ばれること。
-- 図式が連結であるとは、その添字圏が連結であること。

#print Relation.ReflTransGen

def Zag' (j k : J) : Prop := Nonempty (j ⟶ k) ∨ Nonempty (k ⟶ j)
class IsConnected' (J : Type v) [SmallCategory J] : Prop where
  nonempty : Nonempty J
  zigzag : ∀ j k : J, Relation.ReflTransGen Zag' j k

#print IsConnected
#print IsPreconnected

theorem isConnected'_iff : IsConnected' J ↔ IsConnected J where
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
    let F : J ⥤ Discrete  (Quot (Relation.ReflTransGen Zag')) := {
      obj j := ⟨Quot.mk (Relation.ReflTransGen Zag') j⟩
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
    have hz : Std.Symm (@Zag' J _) := ⟨fun _ _ h => h.symm⟩
    have hs : Std.Symm (Relation.ReflTransGen (@Zag' J _)) := Relation.ReflTransGen.stdSymm
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
def underForget (c : C) : Under c ⥤ C where
  obj f := f.right
  map {x y} f := f.right
  map_id x := by simp
  map_comp {x y z} f g := by simp

#check Under.forgetCone

-- 頂点 c、脚が各対象 f : c → x の f 自身である、Π の上の錐。
def underForgetCone (c : C) : Cone (Under.forget c) where
  pt := c
  π := {
    app i := i.hom
    naturality {f g} F:= by simp
  }

#check Cone.whisker

-- 錐 s : Cone K を関手 E : J' → J で引き戻した錐。
def coneWhisker {J' : Type v} [SmallCategory J'] {K : J ⥤ C} (E : J' ⥤ J) (s : Cone K) :
    Cone (E ⋙ K) where
  pt := s.pt
  π := Functor.whiskerLeft E s.π



#check StructuredArrow.createsLimitsOfShape

noncomputable instance underForgetStrictlyCreatesLimit (c : C) (K : J ⥤ Under c) :
    StrictlyCreatesLimit K (Under.forget c) where
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
theorem under_hasLimitsOfShape (c : C) [HasLimitsOfShape J C] : HasLimitsOfShape J (Under c) where
  has_limit F := by
    have H := (underForgetStrictlyCreatesLimit c F).lifts
    have HF := H (limit.cone (F ⋙ Under.forget c)) (limit.isLimit (F ⋙ Under.forget c))
    exact ⟨HF.liftedCone, HF.makesLimit⟩

#check Under.createsColimitsOfShapeForgetOfIsConnected

noncomputable instance underForgetStrictlyCreatesColimit [IsConnected J] (c : C) (K : J ⥤ Under c) :
    StrictlyCreatesColimit K (Under.forget c) where
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

theorem under_hasColimitsOfShape_of_isConnected [IsConnected J] (c : C)
    [HasColimitsOfShape J C] : HasColimitsOfShape J (Under c) where
  has_colimit F := by
    have H := underForgetStrictlyCreatesColimit c F
    have HF := H.lifts (colimit.cocone (F ⋙ Under.forget c)) (colimit.isColimit (F ⋙ Under.forget c))
    exact ⟨HF.liftedCocone, HF.makesColimit⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.v
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
圏の積 ∏_{i∈I} C_i について、(i) 各射影関手 π_k : ∏ C_i → C_k は任意の図式に対して極限を
保存し、(ii) 射影関手は共同で極限を創出する。すなわち任意の図式 F : J → ∏ C_i について、
各成分 π_k F が極限を持てば、それらが F の極限の成分を定める。したがって、任意の添字圏 J に
ついて、積の圏が J 型の極限を持つのは各成分が持つとき、かつそのときに限る。

構成: (i) の証明は (ii) の錐の組み立てを使うので、(ii) の構成を先に置く。錐の組み立ては
      `piConeOfComponents` を自前で書き、以後は Mathlib の `pi.coneOfConeCompEval` を参照する。
      (i) では、積の極限錐 c の k 成分だけを錐 s に差し替えた錐の族 `coneUpdate` から積の錐を
      組み、`IsLimit.lift` の k 成分を lift にする。差し替えた成分が s に等しいことは命題的な
      等式なので、錐の等式から脚の等式を出す `Cone.π_app_of_eq` を添える。
-/

section

variable {I : Type v} {Cs : I → Type u} [∀ i, Category.{v} (Cs i)]
#check Pi.π
#check Pi.eval

#check pi.coneOfConeCompEval

def piConeOfComponents (F : J ⥤ ∀ i, Cs i) (c : ∀ k, Cone (F ⋙ Pi.eval Cs k)) : Cone F where
  pt k := (c k).pt
  π := {
    app j i := (c i).π.app j
    naturality {j j'} f := by
      ext i; simp only [Functor.const_obj_obj, Functor.const_obj_map]
      erw [Category.id_comp]
      change _ = (((c i).π.app j)) ≫ F.map f i
      have E := (c i).π.naturality f;
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map, Category.id_comp,
        Functor.comp_map, Pi.eval_map] at E
      rw [E]; rfl
  }

#check pi.coneOfConeEvalIsLimit

def isLimitPiConeOfComponents (F : J ⥤ ∀ i, Cs i) (c : ∀ k, Cone (F ⋙ Pi.eval Cs k))
    (h : ∀ k, IsLimit (c k)) : IsLimit (pi.coneOfConeCompEval c) where
  lift s i := (h i).lift ((Pi.eval Cs i).mapCone s)
  fac s j := by
    ext i; erw [Pi.comp_apply]
    erw [(h i).fac]
    rfl
  uniq s m w := by
    ext i
    rw [(h i).uniq ((Pi.eval Cs i).mapCone s) (m i)]
    intro j
    have E := congr_fun (w j) i
    simp only [pi.coneOfConeCompEval] at E
    erw [Pi.comp_apply] at E
    erw [E]; rfl




-- 積の錐 c の k 成分だけを s に差し替えた錐の族。
open Classical in
noncomputable def coneUpdate {K : J ⥤ ∀ i, Cs i} (c : Cone K) (k : I)
    (s : Cone (K ⋙ Pi.eval Cs k)) (i : I) : Cone (K ⋙ Pi.eval Cs i) :=
  if E : i = k then E ▸ s else (Pi.eval Cs i).mapCone c

theorem coneUpdate_self {K : J ⥤ ∀ i, Cs i} (c : Cone K) (k : I) (s : Cone (K ⋙ Pi.eval Cs k)) :
    coneUpdate c k s k = s := by simp [coneUpdate]

theorem coneUpdate_of_ne {K : J ⥤ ∀ i, Cs i} (c : Cone K) (k : I) (s : Cone (K ⋙ Pi.eval Cs k))
    {i : I} (E : i ≠ k) : coneUpdate c k s i = (Pi.eval Cs i).mapCone c := by
  simp only [coneUpdate, dite_eq_right_iff]; aesop


-- 錐の等式から脚の等式。
theorem Cone.π_app_of_eq {D : Type*} [Category D] {G : J ⥤ D} {c₁ c₂ : Cone G} (h : c₁ = c₂)
    (j : J) : c₁.π.app j = eqToHom (congrArg Cone.pt h) ≫ c₂.π.app j := by
  apply eq_of_heq
  rw [heq_eqToHom_comp_iff, h]


open Classical in
theorem piEval_preservesLimitsOfShape (k : I) : PreservesLimitsOfShape J (Pi.eval Cs k) where
  preservesLimit {K} := {
    preserves {c} Hc := ⟨{
      lift s :=
        eqToHom (show s.pt = (pi.coneOfConeCompEval (coneUpdate c k s)).pt k from
          (congrArg Cone.pt (coneUpdate_self c k s)).symm) ≫
        Hc.lift (pi.coneOfConeCompEval (coneUpdate c k s)) k
      fac s j := by
        simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app, Pi.eval_map]
        erw [Category.assoc]
        have E := Hc.fac (pi.coneOfConeCompEval (coneUpdate c k s)) j
        have := congr_fun E k
        simp only [Pi.comp_apply] at this
        erw [this]; simp only [pi.coneOfConeCompEval]
        rw [<- Cone.π_app_of_eq]
        rw [coneUpdate_self]
      uniq s m w := by
        -- simp at m
        let l : (pi.coneOfConeCompEval (coneUpdate c k s)).pt ⟶ c.pt := fun i =>
          if E : i = k then
            by subst E; exact eqToHom (congrArg Cone.pt (coneUpdate_self c i s)) ≫ m
          else
            eqToHom (congrArg Cone.pt (coneUpdate_of_ne c k s E))
        have E :=  Hc.uniq (pi.coneOfConeCompEval (coneUpdate c k s)) l
        rw [<- E]
        · simp only [Functor.mapCone_pt, Functor.comp_obj, Functor.mapCone_π_app, ↓reduceDIte, l]
          erw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        · intro j; ext i
          rw [Pi.comp_apply]
          simp only [l]
          simp only [pi.coneOfConeCompEval, Functor.mapCone_pt, Functor.comp_obj,
            Functor.mapCone_π_app]
          split_ifs with E
          · subst E; simp only
            erw [Category.assoc, w j]
            rw [Cone.π_app_of_eq (coneUpdate_self c i s) j]
            rfl
          · rw [Cone.π_app_of_eq (coneUpdate_of_ne c k s E) j]
            simp; rfl
    }⟩
  }


open Classical in
theorem pi_hasLimitsOfShape_iff [∀ i, Nonempty (Cs i)] :
    HasLimitsOfShape J (∀ i, Cs i) ↔ ∀ i, HasLimitsOfShape J (Cs i) where
  mp H k := {
    has_limit F := by
      let K : J ⥤ ((i : I) → Cs i) :=
        Functor.pi' (fun i => if E : i = k then E ▸ F else (Functor.const J).obj (Nonempty.some inferInstance))
      have ⟨⟨HK⟩⟩ := (H.has_limit K)
      have ⟨H⟩ :=  ((piEval_preservesLimitsOfShape (J := J) (Cs := Cs) k).preservesLimit (K := K)).preserves HK.2
      have E : (K ⋙ Pi.eval Cs k) = F := by simp [K]
      rw [<- E]
      apply HasLimit.mk ⟨_, H⟩
  }
  mpr H := {
    has_limit F := by
      let K : ∀ (i : I), J ⥤ Cs i := fun i => {
        obj j := F.obj j i
        map {j j'} f :=  F.map f i
        map_id j := by simp
        map_comp {a b c} f g := by simp
      }
      let c : ∀ (s : Cone F) i, Cone (K i) := fun s i => {
        pt := s.pt i
        π := {
          app j := s.π.app j i
          naturality {j j'} f := by
            have E := s.π.naturality f
            erw [Functor.const_obj_map, Category.id_comp] at E
            rw [E]; simp [K]
        }
      }
      apply HasLimit.mk {
        cone := {
          pt i := limit (K i)
          π := {
            app j i := limit.π (K i) j
            naturality {j j'} f:= by
              ext i; simp only [Functor.const_obj_obj, Functor.const_obj_map, Pi.comp_apply,
                Pi.id_apply, Category.id_comp]
              rw [<- limit.w (K i) f]
          }
        }
        isLimit := {
          lift s i := limit.lift (K i) (c s i)
          fac s j := by
            ext i; simp [c]
          uniq s m w := by
            ext i j; simp only [limit.lift_π, c]
            rw [<- w]; simp
        }
      }
  }


end

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.4.9
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小圏 A について、忘却関手 ev : Cᴬ → C^{ob A} は、任意の図式に対して極限を厳密に創出する。
したがって、任意の添字圏 J について、C が J 型の極限を持てば、(i) Cᴬ も J 型の極限を持ち、
(ii) 各 a ∈ A について評価関手 ev_a : Cᴬ → C は J 型の極限を保存する。余極限についても同様。

構成: 小圏 A の対象を極大な離散部分圏 ob A ↪ A と見て、忘却関手 ev を組む。創出は定義3.4.1
      の創出 `CreatesLimit` で述べる（厳密な創出からは持ち上げの等式での一意性が落ちる）。
      そこから (i) と (ii) を示す。
-/

#check Discrete.functor

def obIncl (A : Type v) [SmallCategory A] : Discrete A ⥤ A where
  obj a := a.as
  map f := eqToHom (Discrete.eq_of_hom f)

-- ob A ↪ A と書けるのは、この包含が埋め込み（忠実で対象に単射）だから（`Riehl.Topics.Embedding`）。
theorem discreteFunctorId_embedding (A : Type v) [SmallCategory A] :
    Embedding (Discrete.functor (id : A → A)) := by
  constructor; intro x y E
  simp only [Discrete.functor, Function.id_comp, Function.comp_apply, id_eq] at E
  ext; exact E

def ev (A : Type v) [SmallCategory A] (C : Type u) [Category.{v} C] :
    (A ⥤ C) ⥤ (Discrete A ⥤ C) where
  obj G := Discrete.functor id ⋙ G
  map α :=  Functor.whiskerLeft (Discrete.functor id) α

-- 本が C^{ob A} ≅ ∏_{ob A} C と書く同一視。`A → C` は `∀ _ : A, C`（演習3.4.v の積の圏）。
#check piEquivalenceFunctorDiscrete

def piEquivalenceFunctorDiscrete' (A : Type v) (C : Type u) [Category.{v} C] :
    (A → C) ≌ (Discrete A ⥤ C) where
  functor := {
    obj f := {
      obj a := f a.as
      map {a a'} g := eqToHom (congr_arg f g.eq)
      map_id a := by simp only [eqToHom_refl]
      map_comp {a b c} g h := by simp only [eqToHom_trans]
    }
    map {f g} F := {
      app a := F a.as
      naturality {a a'} h := by
        simp
        obtain ⟨a⟩ := a
        obtain ⟨a'⟩ := a'
        obtain ⟨rfl⟩ := h.eq
        simp
    }
    map_id f := by
      apply NatTrans.ext; ext; simp
    map_comp {f g h} F  G := by
      apply NatTrans.ext; ext; simp

  }
  inverse := {
    obj F a := F.obj ⟨a⟩
    map {F G} σ a := σ.app ⟨a⟩
    map_id F := by ext; simp
    map_comp {F G H} σ τ := by ext; simp
  }
  unitIso := {
    hom := {
      app f a := 𝟙 (f a)
      naturality {f g} F := by ext a; simp
    }
    inv := {
      app f a := 𝟙 (f a)
      naturality {f g} F := by ext; simp
    }
    hom_inv_id := by
      apply NatTrans.ext; ext; simp
    inv_hom_id := by
      apply NatTrans.ext; ext; simp
  }
  counitIso := {
    hom := {
      app F := {
        app i := 𝟙 (F.obj i)
        naturality {x y} f := by
          obtain ⟨x⟩ := x
          obtain ⟨y⟩ := y
          obtain ⟨⟨rfl⟩⟩ := f
          simp
      }
      naturality {G H} σ := by
        ext x; simp
    }
    inv := {
      app F := {
        app i := 𝟙 F.obj i
        naturality {x y} f := by
          obtain ⟨x⟩ := x
          obtain ⟨y⟩ := y
          obtain ⟨⟨rfl⟩⟩ := f
          simp
      }
      naturality {G H} σ := by
        ext x; simp
    }
    hom_inv_id := by
      ext F x; simp
    inv_hom_id := by
      ext F x; simp
  }
  functor_unitIso_comp f := by
    ext x; simp


-- この同一視のもとで、`Discrete A ⥤ C` の各点 a での評価関手は積の射影 `Pi.eval` に対応する。
#check piEquivalenceFunctorDiscreteCompEvaluationIso

def piEquivalenceFunctorDiscreteCompEvaluationIso' {A : Type v} (a : A) :
    (piEquivalenceFunctorDiscrete A C).functor ⋙ (evaluation (Discrete A) C).obj ⟨a⟩ ≅
    Pi.eval (fun _ : A => C) a where
  hom := {
    app f := 𝟙 (f a)
    naturality {f g} F:= by
      simp only [evaluation, Functor.comp_obj, Functor.comp_map,
        piEquivalenceFunctorDiscrete_functor_map, Discrete.natTrans_app, Pi.eval_map]
      erw [Category.comp_id, Category.id_comp]
  }
  inv := {
    app f := 𝟙 (f a)
    naturality {f g} F := by
      simp only [evaluation, Functor.comp_obj, Pi.eval_map, Functor.comp_map,
        piEquivalenceFunctorDiscrete_functor_map, Discrete.natTrans_app]
      erw [Category.comp_id, Category.id_comp]
  }
  hom_inv_id := by
    ext f
    simp only [piEquivalenceFunctorDiscrete, Functor.comp_obj, Functor.id_obj,
      Discrete.functor_obj_eq_as, Discrete.mk_as, evaluation_obj_obj, NatTrans.comp_app,
      NatTrans.id_app]
    erw [Category.comp_id]
  inv_hom_id := by
    ext f
    simp? [Pi.eval]
    erw [Category.comp_id]




-- C^{ob A} = `Discrete A ⥤ C` の各点への射影は極限を保存する。本が上の同一視と演習3.4.v で
-- 済ませている箇所。
theorem discreteEvaluation_preservesLimitsOfShape (A : Type v) [SmallCategory A] (a : A) :
    PreservesLimitsOfShape J ((evaluation (Discrete A) C).obj ⟨a⟩) where
  preservesLimit {K} := {
    preserves {c} Hc := by
      constructor
      have E : ((evaluation (Discrete A) C).obj { as := a }) =
        (piEquivalenceFunctorDiscrete A C).inverse ⋙  Pi.eval (fun _ : A => C) a := rfl
      rw [E]
      have Hc' := ((preservesLimit_of_isEquivalence (piEquivalenceFunctorDiscrete A C).inverse K).preserves Hc).some
      have Hc'':= ((piEval_preservesLimitsOfShape (Cs := fun _ : A => C) a).preservesLimit.preserves Hc').some
      apply Hc''.ofIsoLimit
      apply Functor.mapConeMapCone
  }

noncomputable instance evCreatesLimit (A : Type v) [SmallCategory A] (K : J ⥤ (A ⥤ C)) :
    CreatesLimit K (ev A C) where
  reflects {c} Hc := ⟨{
    lift s := {
      app a := (Hc.lift ((ev A C).mapCone s)).app ⟨a⟩
      naturality {a a'} f := by
        have H := ((discreteEvaluation_preservesLimitsOfShape A a').preservesLimit.preserves Hc).some
        apply H.hom_ext; intro j
        have Fa : (Hc.lift ((ev A C).mapCone s)).app ⟨a⟩ ≫ (c.π.app j).app a = (s.π.app j).app a :=
          NatTrans.congr_app (Hc.fac ((ev A C).mapCone s) j) ⟨a⟩
        have Fa' : (Hc.lift ((ev A C).mapCone s)).app ⟨a'⟩ ≫ (c.π.app j).app a' = (s.π.app j).app a' :=
          NatTrans.congr_app (Hc.fac ((ev A C).mapCone s) j) ⟨a'⟩
        have E : c.pt.map f ≫ (c.π.app j).app a' = (c.π.app j).app a ≫ (K.obj j).map f :=
          (c.π.app j).naturality f
        change (s.pt.map f ≫ (Hc.lift ((ev A C).mapCone s)).app ⟨a'⟩) ≫ (c.π.app j).app a' =
          ((Hc.lift ((ev A C).mapCone s)).app ⟨a⟩ ≫ c.pt.map f) ≫ (c.π.app j).app a'
        erw [Category.assoc, Fa', Category.assoc, E, ← Category.assoc, Fa]
        exact (s.π.app j).naturality f
    }
    fac s j := by
      ext a; simp only [Functor.mapCone_pt, NatTrans.comp_app]
      have E := (Hc.fac ((ev A C).mapCone s)) j
      have E' :=  NatTrans.congr_app E ⟨a⟩
      set σ := (Hc.lift ((ev A C).mapCone s))
      erw [NatTrans.comp_app] at E'
      simp [ev] at E'
      exact E'
    uniq s m w := by
      ext a; simp
      have E := (Hc.uniq ((ev A C).mapCone s)) (Functor.whiskerLeft (Discrete.functor id) m)
      rw [<- E]; simp
      intro j; ext a';
      simp only [ev, Functor.mapCone_pt, Functor.comp_obj, Discrete.functor_obj_eq_as, id_eq,
        Functor.mapCone_π_app, NatTrans.comp_app, Functor.whiskerLeft_app]
      rw [<- w j]; simp
  }⟩
  lifts c Hc := {
    liftedCone := by

    validLift := _
  }

#check functorCategoryHasLimitsOfShape

theorem functorCategory_hasLimitsOfShape (A : Type v) [SmallCategory A] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (A ⥤ C) := sorry

#check evaluation_preservesLimitsOfShape

theorem evaluationObj_preservesLimitsOfShape (A : Type v) [SmallCategory A]
    [HasLimitsOfShape J C] (a : A) : PreservesLimitsOfShape J ((evaluation A C).obj a) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.4.9（Mathlib の形）
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
小圏 A と図式 K : J → Cᴬ について、Cᴬ の錐が極限錐であるのは、各 a ∈ A での評価が C の極限錐で
あるときである。また各 a ∈ A で j ↦ (K j)(a) の極限錐を取ると、それらは Cᴬ の K 上の極限錐に
束ねられ、各 a での評価は元の極限錐に戻る。

構成: 上の命題3.4.9 を Mathlib が述べている形。忘却関手 ev を使わず、各点の評価関手
      `(evaluation A C).obj a` の族で述べ、反映と束ねの 2 つに分ける。
-/

#check evaluationJointlyReflectsLimits

def evaluationJointlyReflectsLimits' (A : Type v) [SmallCategory A] {K : J ⥤ A ⥤ C} (c : Cone K)
    (H : ∀ a : A, IsLimit (((evaluation A C).obj a).mapCone c)) : IsLimit c where
  lift s := {
    app a := (H a).lift (((evaluation A C).obj a).mapCone s)
    naturality {a a'} f := by
      apply (H a').hom_ext; intro j;
      simp only [Functor.comp_obj, evaluation_obj_obj,
        Functor.mapCone_pt, Functor.mapCone_π_app, evaluation_obj_map, Category.assoc,
        NatTrans.naturality]
      have Ha := (H a).fac (((evaluation A C).obj a).mapCone s) j
      have Ha' := (H a').fac (((evaluation A C).obj a').mapCone s) j
      simp only [Functor.mapCone_pt, evaluation_obj_obj, Functor.comp_obj, Functor.mapCone_π_app,
        evaluation_obj_map] at Ha Ha'
      rw [<- Category.assoc _ _ ((K.obj j).map f), Ha, Ha', <- (s.π.app j).naturality f]
      simp
  }


  fac s j := by
    ext a; simp only [NatTrans.comp_app]
    have E := (H a).fac (((evaluation A C).obj a).mapCone s) j
    simp only [Functor.mapCone_pt, evaluation_obj_obj, Functor.comp_obj, Functor.mapCone_π_app,
      evaluation_obj_map] at E
    exact E
  uniq s m w := by
    ext a; simp only
    apply (H a).hom_ext; intro j; simp only [Functor.comp_obj, evaluation_obj_obj,
      Functor.mapCone_pt, Functor.mapCone_π_app, evaluation_obj_map]
    have E := (H a).uniq (((evaluation A C).obj a).mapCone s) (m.app a)
    simp only [Functor.mapCone_pt, evaluation_obj_obj, Functor.comp_obj, Functor.mapCone_π_app,
      evaluation_obj_map] at E
    rw [E]
    intro j; rw [<- w j]; simp


-- 各点 a での図式 j ↦ (K j)(a) は `K.flip.obj a`（`Functor.flip` は引数の順を入れ替えた関手）。
#check Functor.flip
#check combineCones

def combineCones' (A : Type v) [SmallCategory A] (K : J ⥤ A ⥤ C)
    (c : ∀ a : A, LimitCone (K.flip.obj a)) : Cone K where
  pt := {
    obj a := (c a).cone.pt
    map {a a'} f := by
      let s := (Cone.postcompose (K.flip.map f)).obj (c a).cone
      exact ((c a').isLimit.lift s)
    map_id a := by
      apply (c a).isLimit.hom_ext
      intro j; dsimp only [Cone.postcompose_obj_pt, Functor.flip_obj_obj]
      rw [(c a).isLimit.fac]; simp
    map_comp {x y z} f g := by
      apply (c z).isLimit.hom_ext
      intro j; simp
  }
  π := {
    app j := {
      app a := (c a).cone.π.app j
      naturality {a a'} f := by
        dsimp only [Lean.Elab.WF.paramLet, Functor.const_obj_obj]
        have := (c a').isLimit.fac ((Cone.postcompose (K.flip.map f)).obj (c a).cone) j
        rw [this]; simp
    }
    naturality {j j'} f := by
      ext a; dsimp
      have := (c a).cone.π.naturality f
      simp only [Functor.const_obj_obj, Functor.flip_obj_obj, Functor.const_obj_map,
        Category.id_comp, Functor.flip_obj_map] at this
      rw [this]; simp
  }




#check evaluateCombinedCones

def evaluateCombinedCones' (A : Type v) [SmallCategory A] (K : J ⥤ A ⥤ C)
    (c : ∀ a : A, LimitCone (K.flip.obj a)) (a : A) :
    ((evaluation A C).obj a).mapCone (combineCones K c) ≅ (c a).cone where
  hom := {
    hom := 𝟙 _
    w j := by erw [Category.id_comp]; rfl
  }
  inv := {
    hom := 𝟙 _
    w j := by erw [Category.id_comp]; simp
  }
  hom_inv_id := by
    erw [Category.comp_id]; rfl
  inv_hom_id := by
    erw [Category.comp_id]; rfl



#check combinedIsLimit

def combinedIsLimit' (A : Type v) [SmallCategory A] (K : J ⥤ A ⥤ C)
    (c : ∀ a : A, LimitCone (K.flip.obj a)) : IsLimit (combineCones K c) := by
  apply evaluationJointlyReflectsLimits
  intro a
  apply (c a).isLimit.ofIsoLimit
  symm; apply evaluateCombinedCones






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

noncomputable def colimitComparison (K : J ⥤ C) (F : C ⥤ D) [HasColimit K] [HasColimit (K ⋙ F)] :
    colimit (K ⋙ F) ⟶ F.obj (colimit K) :=
  colimit.desc  (K ⋙ F) (F.mapCocone (colimit.cocone K))

#check preservesColimit_of_isIso_post

theorem preservesColimit_iff_isIso_colimitComparison (K : J ⥤ C) (F : C ⥤ D)
    [HasColimit K] [HasColimit (K ⋙ F)] :
    PreservesColimit K F ↔ IsIso (colimitComparison K F) where
  mp H := by
    constructor
    have HF := (H.preserves (colimit.isColimit K)).some
    use HF.desc (colimit.cocone (K ⋙ F))
    simp only [colimitComparison]; constructor
    · apply colimit.hom_ext; intro j
      rw [<- Category.assoc, colimit.ι_desc, HF.fac]
      simp
    · apply HF.hom_ext; intro j
      erw [Category.comp_id]
      rw [<- Category.assoc, HF.fac]
      erw [colimit.ι_desc]
  mpr H := by
    rcases H with ⟨inv, map_inv, inv_map⟩
    constructor; intro c Hc; constructor
    let σ := Hc.uniqueUpToIso (colimit.isColimit K)
    apply (colimit.isColimit (K ⋙ F)).ofIsoColimit
    refine {
      hom := {
        hom := colimitComparison K F ≫ F.map σ.inv.hom
        w j := by
          simp only [Functor.comp_obj, Functor.mapCocone_pt, colimit.cocone_x, colimit.cocone_ι,
            colimitComparison, IsColimit.uniqueUpToIso_inv, IsColimit.descCoconeMorphism_hom,
            colimit.isColimit_desc, colimit.ι_desc_assoc, Functor.mapCocone_ι_app, σ]
          rw [<- F.map_comp, colimit.ι_desc]
      }
      inv := {
        hom := F.map σ.hom.hom ≫ inv
        w j := by
          simp only [Functor.comp_obj, colimit.cocone_x, Functor.mapCocone_pt,
            Functor.mapCocone_ι_app, IsColimit.uniqueUpToIso_hom, IsColimit.descCoconeMorphism_hom,
            colimit.cocone_ι, σ]
          simp only [colimitComparison] at map_inv
          rw [<- F.map_comp_assoc, Hc.fac]
          have E :=  colimit.ι_desc (F.mapCocone (colimit.cocone K)) j
          dsimp only [Functor.comp_obj, Functor.mapCocone_pt, colimit.cocone_x,
            Functor.mapCocone_ι_app, colimit.cocone_ι] at E
          erw [<- E]
          rw [Category.assoc, map_inv]; simp
      }
      hom_inv_id := by
        ext; simp only [colimit.cocone_x, Functor.mapCocone_pt, Cocone.category_comp_hom,
          Category.assoc, Cocone.category_id_hom]
        rw [<- F.map_comp_assoc]
        have E := congr_arg (fun c => c.hom)  σ.inv_hom_id;
        dsimp only [Cocone.category_comp_hom, colimit.cocone_x, Cocone.category_id_hom] at E
        rw [E]; simp only [CategoryTheory.Functor.map_id, Category.id_comp]
        rw [map_inv]
      inv_hom_id := by
        ext; simp only [Functor.mapCocone_pt, colimit.cocone_x, Cocone.category_comp_hom,
          Category.assoc, Cocone.category_id_hom]
        rw [<- Category.assoc inv, inv_map]
        simp only [Category.id_comp]
        have E := congr_arg (fun c => c.hom)  σ.hom_inv_id;
        dsimp only [Cocone.category_comp_hom, colimit.cocone_x, Cocone.category_id_hom] at E
        rw [<- F.map_comp, E]; simp
    }


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
任意の関手 F : C → Set について、射影関手 Π : ∫F → C は、(i) ΠK の極限が C に存在し F が
それを保存するような任意の図式 K : J → ∫F に対して K の極限を厳密に創出し、(ii) J が連結で
ΠK の余極限が C に存在するような任意の図式 K : J → ∫F に対して K の余極限を厳密に創出する。
-/

noncomputable def elementsPiStrictlyCreatesLimit (F : C ⥤ Type v) (K : J ⥤ F.Elements)
    [HasLimit (K ⋙ Functor.Elements.π F)] [PreservesLimit (K ⋙ Functor.Elements.π F) F] :
    StrictlyCreatesLimit K (Functor.Elements.π F) where
  lifts s Hs := {
    liftedCone := by
      have HF := (PreservesLimit.preserves (F := F) Hs).some
      refine {
        pt := {
          obj := s.pt
          val := by
            let s : Cone ((K ⋙ Functor.Elements.π F) ⋙ F) := {
              pt := PUnit
              π := {
                app j := TypeCat.ofHom (fun _ => (K.obj j).val)
                naturality {j j'} f := by
                  ext x; simp
              }
            }
            exact HF.lift s PUnit.unit
        }
        π := {
          app j := {
            hom := s.π.app j
            map_val := by
              simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.Elements.π_obj,
                Functor.mapCone_pt, Lean.Elab.WF.paramLet]
              rw [<- comp_apply, <- F.mapCone_π_app, HF.fac]
              simp
          }
          naturality {j j'} f := by
            ext; simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.Elements.comp_hom]
            have E := s.π.naturality f
            dsimp only [Functor.const_obj_obj, Functor.comp_obj, Functor.Elements.π_obj,
              Functor.const_obj_map, Functor.comp_map, Functor.Elements.π_map] at E;
            rw [<- E]; simp

        }
      }

    validLift := rfl
    unique c Hc := by
      rw [Cone.mk.injEq]
      · sorry
      · sorry


    makesLimit := sorry
  }


noncomputable def elementsPiStrictlyCreatesColimit [IsConnected J] (F : C ⥤ Type v)
    (K : J ⥤ F.Elements) : StrictlyCreatesColimit K (Functor.Elements.π F) := sorry

/- 同じ主張を定義3.4.1 の創出 `CreatesLimit`・`CreatesColimit` で述べたもの。厳密な創出との差は、
   持ち上げの一意性 `unique` が落ち、`validLift` が錐の等式でなく同型になること。 -/

-- Mathlib は、C が J 型の極限をすべて持ち F がそれらをすべて保存する仮定のもとで、名前のない
-- instance `Functor.Elements.instCreatesLimitπ` として持つ（`Mathlib/CategoryTheory/Limits/
-- Elements.lean`。このファイルでは import しない）。
noncomputable def elementsPiCreatesLimit (F : C ⥤ Type v) (K : J ⥤ F.Elements)
    [HasLimit (K ⋙ Functor.Elements.π F)] [PreservesLimit (K ⋙ Functor.Elements.π F) F] :
    CreatesLimit K (Functor.Elements.π F) where
  reflects {c} Hc := ⟨{
    lift s := {
      hom := Hc.lift ((Functor.Elements.π F).mapCone s)
      map_val := by
        have HF := (PreservesLimit.preserves (F := F) Hc).some
        let σ := Types.isLimitEquivSections HF
        simp at σ
        apply σ.injective
        ext j
        rw [Types.isLimitEquivSections_apply]
        rw [Types.isLimitEquivSections_apply]
        simp only [Functor.mapCone_pt, Functor.Elements.π_obj, Functor.mapCone_π_app,
          Functor.comp_obj, Functor.Elements.π_map, Functor.const_obj_obj,
          Functor.Elements.Hom.map_val]
        rw [<- comp_apply, <- F.map_comp]
        have E := Hc.fac ((Functor.Elements.π F).mapCone s) j
        dsimp only [Functor.mapCone_pt, Functor.Elements.π_obj, Functor.comp_obj,
          Functor.mapCone_π_app, Functor.Elements.π_map] at E
        rw [E]
        exact (s.π.app j).map_val
    }


    fac s j := by
      ext; simp only [Functor.Elements.comp_hom]
      have E := Hc.fac ((Functor.Elements.π F).mapCone s) j
      simp only [Functor.mapCone_pt, Functor.Elements.π_obj, Functor.comp_obj,
        Functor.mapCone_π_app, Functor.Elements.π_map] at E
      rw [E]

    uniq s m w := by
      ext; simp only
      rw [Hc.uniq ((Functor.Elements.π F).mapCone s) m.hom]
      intro j; simp only [Functor.mapCone_pt, Functor.Elements.π_obj, Functor.comp_obj,
        Functor.mapCone_π_app, Functor.Elements.π_map]
      rw [<- w j]; simp
  }⟩
  lifts s Hs := {
    liftedCone := by
      have HF := (PreservesLimit.preserves (F := F) Hs).some
      refine {
        pt := {
          obj := s.pt
          val := by
            let s : Cone ((K ⋙ Functor.Elements.π F) ⋙ F) := {
              pt := PUnit
              π := {
                app j := TypeCat.ofHom (fun _ => (K.obj j).val)
                naturality {j j'} f := by
                  ext x; simp
              }
            }
            exact HF.lift s PUnit.unit
        }
        π := {
          app j := {
            hom := s.π.app j
            map_val := by
              simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.Elements.π_obj,
                Functor.mapCone_pt, Lean.Elab.WF.paramLet]
              rw [<- comp_apply, <- F.mapCone_π_app, HF.fac]
              simp
          }
          naturality {j j'} f := by
            ext; simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Functor.Elements.comp_hom]
            have E := s.π.naturality f
            dsimp only [Functor.const_obj_obj, Functor.comp_obj, Functor.Elements.π_obj,
              Functor.const_obj_map, Functor.comp_map, Functor.Elements.π_map] at E;
            rw [<- E]; simp

        }
      }


    validLift := {
      hom := {
        hom := 𝟙 _
        w j := by simp
      }

      inv := {
        hom := 𝟙 _
        w := by simp
      }
      hom_inv_id := by ext; simp
      inv_hom_id := by ext; simp
    }

  }

#check CreatesColimit

noncomputable instance elementsPiCreatesColimit [IsConnected J] (F : C ⥤ Type v) (K : J ⥤ F.Elements) :
    CreatesColimit K (Functor.Elements.π F) where
  reflects {c} Hc := ⟨{
    desc s := {
      hom := Hc.desc ((Functor.Elements.π F).mapCocone s)
      map_val := by
        let j : J :=  IsConnected.is_nonempty.some
        have E := (c.ι.app j).map_val
        dsimp at E
        rw [<- E, <- comp_apply, <- F.map_comp]; clear E
        have E := Hc.fac ((Functor.Elements.π F).mapCocone s) j
        dsimp at E; rw [E]; clear E
        have E := (s.ι.app j).map_val; dsimp at E
        exact E
    }
    fac s j := by
      ext; simp only [Functor.Elements.comp_hom]
      have E := Hc.fac ((Functor.Elements.π F).mapCocone s) j
      dsimp at E; exact E
    uniq s m w := by
      have E := Hc.uniq ((Functor.Elements.π F).mapCocone s) m.hom
      ext; rw [E]
      intro j; simp only [Functor.comp_obj, Functor.Elements.π_obj, Functor.mapCocone_pt,
        Functor.mapCocone_ι_app, Functor.Elements.π_map]
      rw [<- w j]; simp
  }⟩
  lifts c Hc := {
    liftedCocone := {
      pt := {
        obj := c.pt
        val := by
          let j : J := IsConnected.is_nonempty.some
          exact (F.map (c.ι.app j)).hom (K.obj j).val
      }
      ι := {
        app j := {
          hom := c.ι.app j
          map_val := by
            simp only [Functor.comp_obj, Functor.Elements.π_obj, Functor.const_obj_obj,
              Lean.Elab.WF.paramLet]
            set j' : J := IsConnected.is_nonempty.some
            let G := fun j => (ConcreteCategory.hom (F.map (c.ι.app j))) (K.obj j).val
            change G j = G j'
            apply constant_of_preserves_morphisms
            intro i i' f; simp only [G]
            rw [<- (K.map f).map_val, <- comp_apply, <- F.map_comp]
            have E := c.ι.naturality f; dsimp at E
            rw [E]; simp
        }
        naturality {j j'} f:= by
          ext; simp only [Functor.comp_obj, Functor.Elements.π_obj, Functor.const_obj_obj,
            Lean.Elab.WF.paramLet, Functor.Elements.comp_hom, Functor.const_obj_map,
            Category.comp_id]
          have := c.ι.naturality f; dsimp at this
          rw [this]; simp
      }
    }
    validLift := {
      hom := {
        hom := 𝟙 c.pt
        w := by simp
      }

      inv := {
        hom := 𝟙 c.pt
        w := by simp
      }
      hom_inv_id := by
        ext; simp
      inv_hom_id := by
        ext; simp
    }
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.iii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 関手 F : C → D と図式 K : J → C について、K の極限が C に存在して F がそれを保存し、F が
-- 同型を反映するならば、F は K の極限を創出する。

#check createsLimitOfReflectsIso

-- F で写した錐が極限錐なら、その錐から lim K への標準の射は同型。
theorem isIso_limitLift_of_isLimit_mapCone (K : J ⥤ C) (F : C ⥤ D) [HasLimit K]
    [PreservesLimit K F] [F.ReflectsIsomorphisms] {c : Cone K} (Hc : IsLimit (F.mapCone c)) :
    IsIso (limit.lift K c) := by
  have HFK := (PreservesLimit.preserves (F := F) (limit.isLimit K)).some
  let σ := Hc.conePointUniqueUpToIso HFK
  have E : F.map (limit.lift K c) = σ.hom := by
    apply HFK.hom_ext; intro j
    rw [IsLimit.conePointUniqueUpToIso_hom_comp]
    simp only [Functor.comp_obj, Functor.mapCone_pt, limit.cone_x, Functor.mapCone_π_app,
      limit.cone_π]
    rw [← F.map_comp, limit.lift_π]
  have Hf : IsIso (F.map (limit.lift K c)) := by
    rw [E]; exact σ.isIso_hom
  exact Functor.ReflectsIsomorphisms.reflects F (limit.lift K c)

noncomputable instance createsLimitOfPreservesOfReflectsIso (K : J ⥤ C) (F : C ⥤ D)
    [HasLimit K] [PreservesLimit K F] [F.ReflectsIsomorphisms] :
    CreatesLimit K F where
  reflects {c} Hc := ⟨{
    lift s := by
      have := isIso_limitLift_of_isLimit_mapCone K F Hc
      exact limit.lift K s ≫ inv (limit.lift K c)
    fac s j := by
      simp only [Category.assoc]
      let Hf := isIso_limitLift_of_isLimit_mapCone K F Hc
      rw [<- limit.lift_π s]
      rw [<- Category.id_comp (limit.π K j), <- Hf.inv_hom_id]
      rw [Category.assoc, limit.lift_π]

    uniq s m w := by
      dsimp
      let Hf := isIso_limitLift_of_isLimit_mapCone K F Hc
      rw [<- Category.comp_id m, <- Hf.hom_inv_id, <- Category.assoc]
      congr
      apply limit.hom_ext; intro j
      rw [Category.assoc, limit.lift_π, w j, limit.lift_π]
  }⟩
  lifts c Hc := {
    liftedCone := limit.cone K
    validLift := by
      have HFK := (PreservesLimit.preserves (F := F) (limit.isLimit K)).some
      exact HFK.uniqueUpToIso Hc
  }



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.iv
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 忘却関手 U : Set∗ → Set と U : Top∗ → Top は余積を保存しない。これは命題3.4.8 の連結性の
-- 仮定が落とせないことを示す。

theorem pointedSet_forget_not_preservesBinaryCoproducts :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (Under.forget (PUnit.{v + 1} : Type v)) :=
  sorry

theorem pointedTop_forget_not_preservesBinaryCoproducts :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (Under.forget (TopCat.of PUnit.{v + 1})) :=
  sorry



-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.4.vi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
レトラクト B →s A →r B, rs = id_B が A 上の分裂冪等射 sr を定めるとき、(i) B →s A ⇉ A
（id_A と sr）は等化子図式、A ⇉ A →r B は余等化子図式であり、(ii) B は冪等射 sr が定める
図式の極限かつ余極限であり、(iii) これらの極限・余極限は任意の関手 G : C → D で保存される。
-/

section

variable {A B : C} (s : B ⟶ A) (r : A ⟶ B) (h : s ≫ r = 𝟙 B)
include h

theorem splitIdempotent_fork_condition :
    s ≫ 𝟙 A = s ≫ r ≫ s := by
  rw [<- Category.assoc, h]; simp

def isLimitSplitIdempotentFork :
    IsLimit (Fork.ofι s (splitIdempotent_fork_condition s r h)) where
  lift (c : Fork (𝟙 A) (r ≫ s)) := c.ι ≫ r
  fac (c : Fork _ _ ) i := by
    rcases i
    · simp only [parallelPair_obj_zero, Fork.ofι_pt, Fork.ofι_π_app, Category.assoc,
      Fork.app_zero_eq_ι]
      rw [<- c.condition]; simp
    · simp only [parallelPair_obj_one, Fork.ofι_pt, Fork.ofι_π_app, Functor.const_obj_obj,
      Category.comp_id, Category.assoc, Fork.app_one_eq_ι_comp_left]
      rw [<- c.condition]; simp
  uniq (c : Fork _ _ ) m w := by
    have H0 := w WalkingParallelPair.zero
    simp only [parallelPair_obj_zero, Fork.ofι_pt, Fork.ofι_π_app, Fork.app_zero_eq_ι] at H0
    rw [<- H0, Category.assoc, h]; simp




theorem splitIdempotent_cofork_condition : 𝟙 A ≫ r = (r ≫ s) ≫ r := sorry

def isColimitSplitIdempotentCofork :
    IsColimit (Cofork.ofπ r (splitIdempotent_cofork_condition s r h)) := sorry

theorem preservesLimit_splitIdempotent (G : C ⥤ D) :
    PreservesLimit (parallelPair (𝟙 A) (r ≫ s)) G where
  preserves {c : Fork _ _} Hc := ⟨{
    lift t :=
      t.π.app WalkingParallelPair.zero ≫ G.map (r ≫ Hc.lift ((Fork.ofι s (splitIdempotent_fork_condition s r h))))
    fac t i := by
      simp only [Functor.comp_obj, Functor.mapCone_pt, parallelPair_obj_zero, Functor.map_comp,
        Functor.mapCone_π_app, Category.assoc]
      rcases i
      · simp only [parallelPair_obj_zero, Fork.app_zero_eq_ι]
        rw [<- G.map_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι]
        have Er := t.π.naturality WalkingParallelPairHom.right
        have El := t.π.naturality WalkingParallelPairHom.left
        simp only [Functor.const_obj_obj, Functor.comp_obj, parallelPair_obj_one,
          Functor.const_obj_map, Category.id_comp, parallelPair_obj_zero, Functor.comp_map,
          parallelPair_map_right, Functor.map_comp, parallelPair_map_left,
          CategoryTheory.Functor.map_id, Category.comp_id] at Er El
        exact Er.symm.trans El
      · simp only [parallelPair_obj_one, Fork.app_one_eq_ι_comp_left, Category.comp_id]
        rw [<- G.map_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι]
        have Er := t.π.naturality WalkingParallelPairHom.right
        simp at Er
        exact Er.symm
    uniq t m w := by
      simp only [Functor.mapCone_pt, Functor.comp_obj, parallelPair_obj_zero, Functor.map_comp]
      have w0 := w WalkingParallelPair.zero
      simp only [Functor.comp_obj, parallelPair_obj_zero, Functor.mapCone_pt, Functor.mapCone_π_app,
        Fork.app_zero_eq_ι] at w0
      rw [<- w0]; simp only [Category.assoc]
      nth_rw 1 [<- Category.comp_id m]
      congr 1; simp only [Functor.mapCone_pt]
      rw [<- G.map_id, <- G.map_comp, <- G.map_comp]
      congr
      apply Hc.hom_ext
      intro i; rcases i
      · simp only [parallelPair_obj_zero, Fork.app_zero_eq_ι, Category.id_comp, Category.assoc,
        Fork.IsLimit.lift_ι, Fork.ι_ofι]
        rw [<- c.condition]; simp
      · simp only [parallelPair_obj_one, Fork.app_one_eq_ι_comp_left, Category.comp_id,
          Category.id_comp, Category.assoc, Fork.IsLimit.lift_ι, Fork.ι_ofι]
        rw [<- c.condition]; simp

  }⟩

theorem preservesColimit_splitIdempotent (G : C ⥤ D) :
    PreservesColimit (parallelPair (𝟙 A) (r ≫ s)) G := sorry

end

end Riehl
