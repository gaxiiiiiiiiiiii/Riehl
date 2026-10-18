# 2026-10-18 自前実装の `my` 接頭辞をやめ、ファイルを `namespace Riehl` で包んだ(対象 規約と 3.4・3.5)

[同日の改名](2026-10-18-content-based-declaration-names.md)の直後に決めた。

## 症状

自前実装は `my` で始める規則だったが、`myEv`、`MyStrictlyCreatesLimit` のように以後の statement から何度も参照される宣言ほど、接頭辞が目に付く。一方、Mathlib に対応物がある自前実装(`MyIsConnected` など)は一致を示す宣言で 1 回参照されるだけで、名前はほとんど読まれない。`my` が区別していたのは「自前か Mathlib か」だが、読者にとって重いのは前者のほうの名前だった。

## 検討

ファイル全体を `namespace Riehl` で包むと、中では自前実装を素の名前で呼べる。`open CategoryTheory` していても、名前空間内の宣言が open より優先されるので曖昧にならない(確認済み)。

ただし Mathlib に同名の宣言があると、以後のファイルすべてで Mathlib 側を `CategoryTheory.IsConnected` のように修飾する必要が生じる。同名になるのは Mathlib に対応物がある自前実装、つまり一致を示したあと使わない宣言に限られるので、そちらにだけ目印を付ければ衝突は起きない。

## 変更

`/exercises` skill の 1 の骨組みに `namespace Riehl` … `end Riehl` を足し、5.1 を次にした。

> 自前実装は本の用語で名付け、Mathlib に同名の宣言があるときだけ `'` を付ける。

判定は概念の対応ではなく名前の衝突で、衝突すれば Lean が曖昧エラーを出すので機械的に決まる。5.2 の `my` への言及は消した。

## 遡及

3.4 と 3.5 を改名した。1.5〜3.3 は旧名のまま残す(`MyEquivalence` など)。

| 旧 | 新 |
|---|---|
| `myMapCone` / `myMapCocone` / `myConeFunctoriality` / `myLimitPost` | `mapCone` / `mapCocone` / `coneFunctoriality` / `limitPost` |
| `MyPreservesLimit` / `MyPreservesColimit` / `MyReflectsLimit` / `MyCreatesLimit` | `PreservesLimit'` / `PreservesColimit'` / `ReflectsLimit'` / `CreatesLimit'` |
| `MyPreservesLimitsOfShape` / `MyPreservesColimitsOfShape` | `PreservesLimitsOfShape'` / `PreservesColimitsOfShape'` |
| `MyReflectsIsomorphisms` | `ReflectsIsomorphisms`(Mathlib は `Functor.ReflectsIsomorphisms` で衝突しない) |
| `myIsLimitOfIso` / `myCreatesLimit_iff_createsLimit` | `isLimitOfIso` / `createsLimit'_iff` |
| `MyStrictLift` / `MyStrictColift` / `MyStrictlyCreatesLimit` / `MyStrictlyCreatesColimit` | `StrictLift` / `StrictColift` / `StrictlyCreatesLimit` / `StrictlyCreatesColimit` |
| `myZag` / `MyIsConnected` / `myIsConnected_iff` | `Zag'` / `IsConnected'` / `isConnected'_iff` |
| `myUnderForget` / `myUnderForgetCone` / `myConeWhisker` | `underForget` / `underForgetCone` / `coneWhisker` |
| `myObIncl` / `myEv` / `myEvStrictlyCreatesLimit` | `obIncl` / `ev` / `evStrictlyCreatesLimit` |
| `myLimitHomEquivCone` | `limitHomEquivCone` |
| `myCoproductD` / `myCoproductC` | `coproductDom` / `coproductCod` |
| `MyFiniteCategory` / `myFiniteCategory_iff` | `FinCategory'` / `finCategory'_iff` |
