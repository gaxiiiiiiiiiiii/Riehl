# 2026-10-18 宣言の名前を本の番号から statement の内容に変えた(対象 規約と 3.4・3.5)

## 症状

演習ファイルの宣言名は `prop_3_4_8_limits`、`thm_3_5_5_ii_reflects` のように `<種別>_<番号>` で付けていた。節を読み進めて別の宣言から参照するとき、名前から何の主張かが読めず、見出しコメントまで戻って番号を照合する必要があった。番号は見出しコメントに既にあるので、名前で繰り返しても情報が増えない。

## 変更

`/exercises` skill の 5.1 を次にした。

> 宣言の名前は statement の内容から付け、Mathlib の命名規則(定義・構成は lowerCamelCase、定理は snake_case)に揃える。自前実装は `my` で始める。`example` は使わず、ファイル内の通し番号は振らない。

`my` と `example` の規則は変えていない。

## 遡及

3.4 と 3.5 の宣言を改名した。3.4 は読み進めている最中で、3.5 は新しい規約で作った直後のため。1.5〜3.3 は旧名のまま残す。

| 旧 | 新 |
|---|---|
| `def_3_4_1_creates` | `myCreatesLimit_iff_createsLimit` |
| `lemma_3_4_3` | `preservesLimit_iff_isIso_post` |
| `lemma_3_4_5` | `reflectsLimit_of_fullyFaithful` |
| `lemma_3_4_6_preserves` / `_reflects` / `_creates` | `preservesLimit_of_isEquivalence` / `reflectsLimit_of_isEquivalence` / `createsLimitOfIsEquivalence` |
| `prop_3_4_8_limits` / `_colimits` | `underForgetStrictlyCreatesLimit` / `underForgetStrictlyCreatesColimit` |
| `prop_3_4_8_hasLimits` / `_hasColimits` | `under_hasLimitsOfShape` / `under_hasColimitsOfShape_of_isConnected` |
| `prop_3_4_9` / `_i` / `_ii` | `myEvStrictlyCreatesLimit` / `functorCategory_hasLimitsOfShape` / `evaluationObj_preservesLimitsOfShape` |
| `ex_3_4_i_i` / `_ii` | `colimitComparison` / `preservesColimit_iff_isIso_colimitComparison` |
| `ex_3_4_ii_i` / `_ii` | `elementsPiStrictlyCreatesLimit` / `elementsPiStrictlyCreatesColimit` |
| `ex_3_4_iii` | `createsLimitOfPreservesOfReflectsIso` |
| `ex_3_4_iv_set` / `_top` | `pointedSet_forget_not_preservesBinaryCoproducts` / `pointedTop_forget_not_preservesBinaryCoproducts` |
| `ex_3_4_v_i` / `_ii` / `_ii_isLimit` / `_hasLimits` | `piEval_preservesLimitsOfShape` / `piConeOfComponents` / `isLimitPiConeOfComponents` / `pi_hasLimitsOfShape_iff` |
| `ex_3_4_vi_i_fork_condition` / `_equalizer` / `_cofork_condition` / `_coequalizer` | `splitIdempotent_fork_condition` / `isLimitSplitIdempotentFork` / `splitIdempotent_cofork_condition` / `isColimitSplitIdempotentCofork` |
| `ex_3_4_vi_iii_equalizer` / `_coequalizer` | `preservesLimit_splitIdempotent` / `preservesColimit_splitIdempotent` |
| `thm_3_5_2_iso` / `_natIso` / `_preserves` | `isIso_limit_post_coyoneda` / `yonedaObjLimitIso` / `coyonedaObj_preservesLimit` |
| `thm_3_5_5_i` / `_ii_preserves` / `_ii_reflects` | `coyonedaObj_preservesLimits` / `yonedaEmbedding_preservesLimits` / `yonedaEmbedding_reflectsLimits` |
| `thm_3_5_6_iso` / `_preserves` | `isIso_limit_post_yoneda` / `yonedaObj_preservesLimit` |
| `thm_3_5_10_i` / `_ii_preserves` / `_ii_reflects` | `yonedaObj_preservesLimits` / `coyonedaEmbedding_preservesLimits` / `coyonedaEmbedding_reflectsLimits` |
| `thm_3_5_11_cocone` / `_isColimit` / `_cocomplete` | `coproductCoequalizerCocone` / `isColimitCoproductCoequalizerCocone` / `hasColimits_of_hasCoproducts_of_hasCoequalizers` |
| `lemma_3_5_15` / `_wide` / `_finiteProducts` | `isLimitBinaryFanOfPullbackTerminal` / `isLimitFanOfWidePullbackTerminal` / `hasFiniteProducts_of_hasTerminal_of_hasPullbacks` |
| `lemma_3_5_16_condition` / `lemma_3_5_16` / `_equalizers` | `fork_condition_of_pullback_diag` / `isLimitForkOfPullbackDiag` / `hasEqualizers_of_hasBinaryProducts_of_hasPullbacks` |
| `thm_3_5_17` | `hasFiniteLimits_of_hasTerminal_of_hasPullbacks` |
| `ex_3_5_i` | `limCoyonedaIsoCones` |
