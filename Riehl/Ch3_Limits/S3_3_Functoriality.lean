import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# 3.3 極限と余極限の関手性

節の数学的な内容は同名の HTML にある。このファイルは本の主張を出現順に並べたもので、主張と
定理群の構成は各セクションの冒頭に、形式化の判断は下の表に、Mathlib の対応物と包装は各
statement の直前の `#check`・`#print` にある。

形式化の判断:
  添字圏の      節をまたぐ取り決めどおり、J は `Type v` の小圏、C は `Category.{v}` に取る
  大きさ
  命題3.3.1     本節が定める極限関手を自前で組む（`myLim`）。各図式への極限の選択は
                `HasLimitsOfShape` の instance が持つ `limit` で取り、本が証明の中で作る錐
                α·ε も本にあるので自前で組む（`myPostcompose`）。`obj` は選んだ極限の頂点で
                本の定義の写しなので書いて渡し、`map`（α·ε を分解する射 lim α を作ること）と
                関手則を演習にする。`map` の定義の性質（lim α が α·ε を分解すること）は
                別の宣言に割る。組んだ関手は Mathlib の `lim` と定義的に一致するので、
                橋渡しの宣言は置かず、以降の statement は `lim` で書く
  命題3.3.1 の  宣言を置かない。「すべての図式に極限があると仮定しなくてよい」という内容は、
  一般形        `limMap` が図式ごとに `HasLimit` を instance 引数で取る形にあたる。本が
                「極限が存在する図式全体が張る充満部分圏」に逃げるのは、関手 Cᴶ → C の形に
                押し込むために定義域を制限する必要があるからで、関手にまとめなければ仮定は
                自然に緩む。`HasLimit` は instance 解決に載せる Prop の class なので、充満
                部分圏の対象のフィールドに証明を持たせると解決から外れ、配管だけが増える。
                Mathlib もこの部分圏を作らない
  系3.3.3       誘導される射を `IsLimit.map`・`IsColimit.map` で述べ、それが同型であることを
                主張する。極限と余極限で宣言を分ける。この 2 つは本の lim α・colim α で、
                命題3.3.1 の構成を、選んだ極限ではなく任意の極限錐について述べたもの（系3.3.3
                の直前の段落が本でこれを述べている）。命題3.3.1 で組んだ関手の `map` と中身が
                同じなので、ここでは Mathlib の名前を使う
  補題3.3.6     二項積は `HasBinaryProducts` の選んだ積 `X ⨯ Y` で取る。同型の構成、射影
                との可換性、一意性、自然性の 4 本に割る。「射影と可換」は X・Y・Z への
                3 本の等式の組で述べる。自然性は X, Y, Z の射についての可換四角形で述べ、
                関手 C × C × C → C の間の自然同型としては組まない。Mathlib の
                `prod.associator` は逆向き (X × Y) × Z ≅ X × (Y × Z) なので、本の向きの
                同型は `(prod.associator X Y Z).symm` にあたる。自然性・五角形の対応物も
                逆向きで述べられている。自然性の statement には f × g を `prod.map` で書く。
                f × g を本が導入するのは演習3.3.i なので、読者が自前で組むより先に Mathlib の
                名前を使うことになる
  演習3.3.i     積の双関手 C × C ⥤ C の `obj` を選んだ積 `p.1 ⨯ p.2` として書いて渡し、
                `map`（f × g）と関手則を演習にする。Mathlib の `prod.functor` はカリー化
                した `C ⥤ C ⥤ C` なので形が違う。本の A × g は `map (𝟙 A, g)` で書く
  演習3.3.ii    五角形を補題3.3.6 で組んだ同型で述べる。W × α は `prod.map (𝟙 W) _`、
                α × Z は `prod.map _ (𝟙 Z)` で書く

statement を置かない節末問題: なし

載せない例と Remark:
  例3.3.2 の弧状連結成分の関手、例3.3.4 の G-集合、例3.3.5 の種、例3.3.7 の結合性の同型が
  恒等射でない例（脚注11 を含む）、選んだ極限の両立性についての注意（Freyd–Scedrov）、
  命題3.3.1 の直後のアナ関手についての注意は載せない。補題3.3.6 の直後の「α_{X,Y,Z} が
  恒等射であるのは射影が等しいときに限る」も載せない。二つの繰り返し積が対象として等しい
  状況を前提にする主張で、Lean では `eqToHom` を挟む不自然な形になるためである。

参考: 主に扱う Mathlib のファイル
  - `Mathlib/CategoryTheory/Limits/Cones.lean`（`Cone.postcompose`）
  - `Mathlib/CategoryTheory/Limits/IsLimit.lean`（`IsLimit.map`・
    `IsLimit.conePointsIsoOfNatIso`）
  - `Mathlib/CategoryTheory/Limits/HasLimits.lean`（`lim`・`limMap`・`limMap_π`）
  - `Mathlib/CategoryTheory/Limits/Shapes/BinaryProducts/BinaryProducts.lean`（`prod.map`・
    `prod.associator`・`prod.pentagon`・`prod.functor`）
-/

open CategoryTheory Limits

universe v u

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]

-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  本文の定義と主張
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 命題3.3.1
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
C がすべての J 型の極限を持つとき、各図式に極限を一つずつ選ぶと関手 lim : Cᴶ → C が定まる。
射 α : F ⇒ G は、錐 α·ε を G の極限錐から分解する射 lim α : lim F → lim G に送られる。
より一般に、極限が存在する図式全体が張る Cᴶ の充満部分圏の上に極限関手が定まる。

構成: 選んだ極限の頂点を対象の行き先として関手を組み、lim α が α·ε を分解することを示す。
-/

#check Cone.postcompose
def myPostcompose (F G : J ⥤ C) (σ : F ⟶ G) :
    Cone F ⥤ Cone G where
  obj s := {
    pt := s.pt
    π := s.π ≫ σ
  }
  map {s t} τ := {
    hom := τ.hom
    w := by
      intro j; dsimp only [NatTrans.comp_app, Functor.const_obj_obj]
      rw [<- Category.assoc, <- τ.w]
  }
  map_id s := by ext; simp
  map_comp s t := by ext; simp

namespace CategoryTheory

@[reducible]
noncomputable def NatTrans.mapCone {F G : J ⥤ C} [HasLimit F] (σ : F ⟶ G) : Cone G :=
  (Cone.postcompose σ).obj (limit.cone F)

end CategoryTheory

#check limMap
noncomputable def myLimMap {F G : J ⥤ C} [HasLimit F] [HasLimit G] (σ : F ⟶ G) :
  limit F ⟶ limit G := limit.lift G σ.mapCone

#check IsLimit.map
def myIsLimitMap {F G : J ⥤ C} (s : Cone F) {t : Cone G} (P : IsLimit t) (σ : F ⟶ G) :
  s.pt ⟶ t.pt
:= P.lift ((Cone.postcompose σ).obj s)


#check lim
noncomputable def myLim [HasLimitsOfShape J C] : (J ⥤ C) ⥤ C where
  obj F := limit F
  map {F G} σ := limit.lift G σ.mapCone -- limMap σ
  map_id F := by
    ext j
    rw [limit.lift_π]
    simp only [NatTrans.mapCone]
    rw [Cone.postcompose_obj_π, NatTrans.comp_app, NatTrans.id_app]
    simp
  map_comp {F G H} τ ι := by
    ext j
    rw [Category.assoc]
    rw [limit.lift_π, limit.lift_π]
    simp only [NatTrans.mapCone]
    rw [Cone.postcompose_obj_π, Cone.postcompose_obj_π]
    rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    rw [limit.cone_π, limit.cone_π]
    rw [<- Category.assoc _ (limit.π G j), limit.lift_π]
    rw [Cone.postcompose_obj_π]
    simp



#check limMap_π

theorem prop_3_3_1_fac [HasLimitsOfShape J C] {F G : J ⥤ C} (α : F ⟶ G) (j : J) :
    limMap α ≫ limit.π G j = limit.π F j ≫ α.app j := by
  simp only [limMap, IsLimit.map]
  rw [limit.isLimit_lift, limit.lift_π]
  rw [Cone.postcompose_obj_π]
  simp


-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 系3.3.3
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 図式の間の自然同型は、極限の間、あるいは余極限の間に、存在する限り同型を誘導する。

#check IsLimit.map
#check IsLimit.conePointsIsoOfNatIso

def cor_3_3_3 {F G : J ⥤ C} {s : Cone F} (hs : IsLimit s) {t : Cone G} (ht : IsLimit t)
    (σ : F ≅ G) : s.pt ≅ t.pt where
  hom := ht.map s σ.hom
  inv := hs.map t σ.inv
  hom_inv_id := by
    apply hs.hom_ext
    intro j
    rw [Category.assoc, IsLimit.map, IsLimit.map]
    rw [hs.fac, Cone.postcompose_obj_π, NatTrans.comp_app]
    rw [<- Category.assoc, ht.fac,  Cone.postcompose_obj_π]
    simp
  inv_hom_id := by
    apply ht.hom_ext; intro j; simp




#check IsColimit.map
#check IsColimit.coconePointsIsoOfNatIso

theorem cor_3_3_3_colim {F G : J ⥤ C} {s : Cocone F} (hs : IsColimit s) {t : Cocone G}
    (ht : IsColimit t) (α : F ≅ G) : IsIso (hs.map t α.hom) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 補題3.3.6
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
二項積を持つ圏の任意の対象 X, Y, Z について、X, Y, Z への射影と可換な自然同型
α_{X,Y,Z} : X × (Y × Z) ≅ (X × Y) × Z がただ一つ存在する。

構成: 同型を組み、それが射影と可換であることを示す。射影と可換な射はそれだけであること、
      同型が X, Y, Z について自然であることを示す。
-/

#check prod.associator

@[simp]
noncomputable def assocl C [Category C] [HasBinaryProducts C] : (C × C × C) ⥤ C where
  obj p := (p.1 ⨯ p.2.1) ⨯ p.2.2
  map {p q} f := prod.map (prod.map f.1 f.2.1) f.2.2
  map_id p := by simp
  map_comp := by simp

@[simp]
noncomputable def assocr C [Category C][HasBinaryProducts C] : (C × C × C) ⥤ C where
  obj p := p.1 ⨯ (p.2.1 ⨯ p.2.2)
  map {p q} f := prod.map f.1 (prod.map f.2.1 f.2.2)
  map_id p := by simp
  map_comp := by simp

noncomputable def assocIso [HasBinaryProducts C] : assocl C ≅ assocr C where
  hom := {
    app p := prod.lift (prod.fst ≫ prod.fst) (prod.map prod.snd (𝟙 _))
    naturality {p p'} f := by
      dsimp
      rw [prod.comp_lift, <- Category.assoc, prod.map_fst, Category.assoc, prod.map_fst]
      rw [prod.map_map, prod.map_snd, Category.comp_id]
      rw [prod.lift_map, Category.assoc, prod.map_map, Category.id_comp]
  }
  inv := {
    app p := prod.lift (prod.map (𝟙 _) prod.fst) (prod.snd ≫ prod.snd)
    naturality := by simp
  }
  hom_inv_id := by
    ext p; simp only [assocl, prod_Hom, assocr, NatTrans.comp_app, prod.comp_lift, prod.lift_map,
      Category.comp_id, prod.map_fst, limit.lift_π_assoc, BinaryFan.mk_pt, pair_obj_right,
      BinaryFan.mk_snd, prod.map_snd, NatTrans.id_app]
    apply prod.hom_ext
    · rw [prod.lift_fst]
      rw [<- prod.comp_lift, prod.lift_fst_snd]
      rw [Category.id_comp, Category.comp_id]
    · rw [prod.lift_snd, Category.id_comp]
  inv_hom_id := by
    ext p; apply prod.hom_ext
    · simp only [assocr, prod_Hom, assocl, NatTrans.comp_app, prod.comp_lift, limit.lift_π_assoc,
      BinaryFan.mk_pt, pair_obj_left, BinaryFan.mk_fst, prod.map_fst, Category.comp_id,
      prod.lift_map, prod.map_snd, limit.lift_π, NatTrans.id_app, Category.id_comp]
    · simp only [assocr, prod_Hom, assocl, NatTrans.comp_app, prod.comp_lift, limit.lift_π_assoc,
      BinaryFan.mk_pt, pair_obj_left, BinaryFan.mk_fst, prod.map_fst, Category.comp_id,
      prod.lift_map, prod.map_snd, limit.lift_π, BinaryFan.mk_snd, NatTrans.id_app,
      Category.id_comp]
      rw [<- prod.comp_lift, prod.lift_fst_snd, Category.comp_id]





















-- ╔═════════════════════════════════════════════════════════════════════════
-- ║  節末問題
-- ╚═════════════════════════════════════════════════════════════════════════

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.3.i
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
/-
二項積を持つ圏 C で命題3.3.1 を特殊化すると、積の双関手 − × − : C × C → C が定まる。
射 f : A → B, g : C → D の像 f × g : A × C → B × D は積の射影と可換であり、
(f × D)·(A × g) = f × g = (B × g)·(f × C) が成り立つ。

構成: 双関手を組み、f × g が二つの射影と可換であることを示し、四角形の二つの三角形が可換で
      あることを示す。
-/

#check prod.functor

noncomputable def ex_3_3_i (C : Type u) [Category.{v} C] [HasBinaryProducts C] : C × C ⥤ C where
  obj p := p.1 ⨯ p.2
  map f := sorry
  map_id := sorry
  map_comp := sorry

#check prod.map_fst

theorem ex_3_3_i_fst [HasBinaryProducts C] {A B C' D : C} (f : A ⟶ B) (g : C' ⟶ D) :
    (ex_3_3_i C).map ((f, g) : (A, C') ⟶ (B, D)) ≫ prod.fst = prod.fst ≫ f := sorry

#check prod.map_snd

theorem ex_3_3_i_snd [HasBinaryProducts C] {A B C' D : C} (f : A ⟶ B) (g : C' ⟶ D) :
    (ex_3_3_i C).map ((f, g) : (A, C') ⟶ (B, D)) ≫ prod.snd = prod.snd ≫ g := sorry

theorem ex_3_3_i_comm_top [HasBinaryProducts C] {A B C' D : C} (f : A ⟶ B) (g : C' ⟶ D) :
    (ex_3_3_i C).map ((𝟙 A, g) : (A, C') ⟶ (A, D)) ≫
        (ex_3_3_i C).map ((f, 𝟙 D) : (A, D) ⟶ (B, D)) =
      (ex_3_3_i C).map ((f, g) : (A, C') ⟶ (B, D)) := sorry

theorem ex_3_3_i_comm_bottom [HasBinaryProducts C] {A B C' D : C} (f : A ⟶ B) (g : C' ⟶ D) :
    (ex_3_3_i C).map ((f, 𝟙 C') : (A, C') ⟶ (B, C')) ≫
        (ex_3_3_i C).map ((𝟙 B, g) : (B, C') ⟶ (B, D)) =
      (ex_3_3_i C).map ((f, g) : (A, C') ⟶ (B, D)) := sorry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 演習3.3.ii
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 四つの対象 W, X, Y, Z の二項積の繰り返しの間で、補題3.3.6 の同型は五角形を可換にする。
-- 補題3.3.6 の証明は、上の補題3.3.6 のセクションの宣言が受け持つ。

#check prod.pentagon

theorem ex_3_3_ii [HasBinaryProducts C] (W X Y Z : C) :
    prod.map (𝟙 W) (lemma_3_3_6 X Y Z).hom ≫ (lemma_3_3_6 W (X ⨯ Y) Z).hom ≫
        prod.map (lemma_3_3_6 W X Y).hom (𝟙 Z) =
      (lemma_3_3_6 W X (Y ⨯ Z)).hom ≫ (lemma_3_3_6 (W ⨯ X) Y Z).hom := sorry
