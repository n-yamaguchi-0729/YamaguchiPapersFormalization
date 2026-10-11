# YamaguchiPapersFormalization

[![Lean](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Naganori Yamaguchi の論文に対応する Lean 4 形式化と、その証明を支える数論・副有限群・代数幾何の基礎ライブラリです。論文別の中心は `Yamaguchi26AbfaithfulGalois` と `Yamaguchi26SolvableCoverings` です。両ライブラリ全体と、そのローカル依存先を収録しています。

以下は 2026年10月11日時点のソースに基づく対応表です。「証明実装」は、記載した仮定から結論を導く Lean の証明項がソースにあることを意味します。現行版のビルド結果は本リポジトリの CI を参照してください。定義の実装、一般的な条件付き定理の実装、特定の体・スキームへの適用を区別しています。

## 対象論文

| 論文 | 著者・公開資料 | 形式化の入口 |
|---|---|---|
| *Ab-faithfulness of absolute Galois groups in number theory* | Naganori Yamaguchi、[arXiv:2610.05634](https://arxiv.org/abs/2610.05634)、[v1 本文](https://arxiv.org/html/2610.05634v1) | [Yamaguchi26AbfaithfulGalois.All](Lean4/Yamaguchi26AbfaithfulGalois/All.lean) |
| *Extension of solvable coverings across horizontal divisors over the integers* | Naganori Yamaguchi、[arXiv:2610.02948](https://arxiv.org/abs/2610.02948)、[v1 本文](https://arxiv.org/html/2610.02948v1) | [Yamaguchi26SolvableCoverings.All](Lean4/Yamaguchi26SolvableCoverings/All.lean) |

ソース内では前者の原稿名として `AbfatifhulGalois.tex`（一部に旧名 `AbfaithfulHLF_final.tex`）、後者には `SolvableCoverings.tex` が記されています。下表は原稿の番号と現行の宣言を対応させています。論文本文は外部リンクで参照し、Lean ソースのライセンスと論文の配布条件を混同しません。

## 絶対 Galois 群の ab-faithfulness

副有限群 `G` の ab-faithfulness は、任意の開部分群 `H` とその開正規部分群 `N` に対し、`H/N` が `N` の位相的アーベル化に忠実に作用する性質です。`Σ` 版では最大 pro-`Σ` 商のアーベル化を使います。主な算術的成果は、混標数離散付値体および正の次元の高次局所体の絶対 Galois 群がこの性質を満たすことです。

さらに、formal Hilbert 90 を使って有限段可解商の中心自明性と slimness（任意の開部分群の中心化群が自明）を扱います。位相的導来列の各段では閉包を取り、`MaxSolvQuot G m` はその実際の商として定義されています。

| 番号 | 現在の内容・状態 | 主なソース |
|---|---|---|
| Definition 1.1 | `Σ`-ab-faithfulness と通常の ab-faithfulness の定義。 | [1.1](Lean4/Yamaguchi26AbfaithfulGalois/Theorem1Dot1AbFaithfulness.lean) |
| Lemma 1.2 | 素数位数の層、素数冪によるアーベル化の商、連続一次コホモロジーの作用による四条件の同値を証明実装。 | [1.2](Lean4/Yamaguchi26AbfaithfulGalois/Theorem1Dot2PrimeOrderTest.lean) |
| Remark 1.3 | 素数集合の拡大と最大 pro-`Σ` 商への継承を証明実装。 | [1.3](Lean4/Yamaguchi26AbfaithfulGalois/Theorem1Dot3SigmaProperties.lean) |
| Proposition 2.1 | 初等アーベル核を持つ有限分裂埋め込み問題の proper solution の存在から、単一素数の ab-faithfulness を導く一般定理を証明実装。 | [2.1](Lean4/Yamaguchi26AbfaithfulGalois/Theorem2Dot1ElementarySplitCriterion.lean) |
| Example 2.2 | **未形式化。** Hilbertian 体、二変数形式冪級数体の分数体、非 `ℓ`-可除値群を持つ標数 `ℓ` の体について、引用された埋め込み問題の可解性を供給する適用は含めない。 | [範囲の宣言](Lean4/Yamaguchi26AbfaithfulGalois/All.lean) |
| Lemma 3.1 | 混標数離散付値体の `p` 冪根の有限性を証明実装。 | [3.1](Lean4/Yamaguchi26AbfaithfulGalois/Theorem3Dot1PrimePowerRoots.lean) |
| Lemma 3.2 | 素数次数 Galois 拡大の mod-`p` 一次コホモロジーへの非自明作用を、根の包含・完備性を要求しない強い形で証明実装。`prime_degree_cohomology_of_mixedChar` が供給する。 | [Kummer/PrimeDegreeCohomology](Lean4/Yamaguchi26AbfaithfulGalois/Kummer/PrimeDegreeCohomology.lean) |
| Lemma 3.3 | 奇素数 `p`、捩れのない分離的な `ℤ_p` 加群に対し、mod-`p` で自明な有限位数自己同型の自明性を証明実装。 | [3.3](Lean4/Yamaguchi26AbfaithfulGalois/Theorem3Dot3FiniteOrderModP.lean) |
| Lemma 3.4 | 主単数の収束対数について、同変性、`ℤ_p` スカラーによる像の閉性、像に入る近傍、分離性を証明実装。 | [3.4](Lean4/Yamaguchi26AbfaithfulGalois/Theorem3Dot4PrincipalUnitLogarithm.lean) |
| Proposition 3.5 | 完備混標数離散付値体の素数次数 Galois 拡大で、mod-`p` 一次コホモロジーの作用が非自明であることを証明実装。 | [3.5](Lean4/Yamaguchi26AbfaithfulGalois/Theorem3Dot5CompletePrimeDegree.lean) |
| Theorem 3.6 | 任意の混標数離散付値体 `K` の有限 Galois 拡大 `L/K` について、実際の `G_L^ab/p` への作用の忠実性と `G_K` の `p`-ab-faithfulness を証明実装。`K` の完備性は仮定しない。 | [3.6](Lean4/Yamaguchi26AbfaithfulGalois/Theorem3Dot6MixedCharacteristic.lean) |
| Lemma 4.1 | 剰余体の ab-faithfulness を仮定した Hensel 離散付値体について、剰余標数零での ab-faithfulness、slimness、有限剰余拡大における primary roots の有限性の同値を証明実装。 | [4.1](Lean4/Yamaguchi26AbfaithfulGalois/Theorem4Dot1ResidueZeroLift.lean) |
| Theorem 4.2 | 正の次元の高次局所体の絶対 Galois 群の ab-faithfulness を証明実装。 | [4.2](Lean4/Yamaguchi26AbfaithfulGalois/Theorem4Dot2HigherLocalFields.lean) |
| Lemma 5.1 | 指定した可解長を増やさず、忠実作用を持つ有限アーベル拡大を構成。 | [5.1](Lean4/Yamaguchi26AbfaithfulGalois/Theorem5Dot1FaithfulAbelianExtension.lean) |
| Proposition 5.2 | アーベル核を持つ有限分裂埋め込み問題が proper solution を持つという仮定から、`m ≥ 2` の最大 `m` 段可解商の slimness を証明実装。Hilbertian 体への適用に必要な Ikeda の定理は未形式化。 | [5.2](Lean4/Yamaguchi26AbfaithfulGalois/Theorem5Dot2AbelianSplitSolvableSlim.lean) |
| Definition 6.1 | 連続 `ℓ` 進 orientation と捩れた係数を構成し、mathlib の連続一次コホモロジーの剰余写像の全射性で formal Hilbert 90 を定義。 | [6.1](Lean4/Yamaguchi26AbfaithfulGalois/Theorem6Dot1FormalHilbert90.lean) |
| Lemma 6.2 | formal Hilbert 90 の下での primary アーベル化の不変元消滅、および無限像 orientation の下での開部分群不変元消滅を証明実装。 | [6.2](Lean4/Yamaguchi26AbfaithfulGalois/Theorem6Dot2IntegralInvariants.lean) |
| Lemma 6.3 | 最大アーベル pro-`Σ` 核による商の中心化群が、指定した閉正規部分群の像に入ることを証明実装。 | [6.3](Lean4/Yamaguchi26AbfaithfulGalois/Theorem6Dot3CentralizerCriterion.lean) |
| Theorem 6.4 | `Σ`-ab-faithfulness と formal Hilbert 90 を満たす orientation から相対商の中心自明性を、無限像の追加仮定から slimness を導く一般定理を証明実装。 | [6.4](Lean4/Yamaguchi26AbfaithfulGalois/Theorem6Dot4RelativeCriterion.lean) |
| Corollary 6.5 | ab-faithful 群の全素数の orientation に上記条件を課し、有限段可解商の中心自明性・slimness を証明実装。 | [6.5](Lean4/Yamaguchi26AbfaithfulGalois/Theorem6Dot5GroupCriterion.lean) |
| Corollary 6.6 | ab-faithful な絶対 Galois 群の有限段可解商の中心自明性を証明実装。無限円分拡大と正標数での巡回素数次拡大という論文の仮定から slimness も導く。必要な orientation と formal Hilbert 90 は証明内で供給する。 | [6.6](Lean4/Yamaguchi26AbfaithfulGalois/Theorem6Dot6AbsoluteCenter.lean) |
| Example 6.7(1)–(3) | 標数零で torally Kummer-faithful かつ ab-faithful な体、sub-`p`-adic 体、正の次元の高次局所体への slimness の適用を証明実装。sub-`p`-adic の場合は `ℚ_p` 上有限生成な体への実際の埋め込みを入力とする。 | [6.7](Lean4/Yamaguchi26AbfaithfulGalois/Theorem6Dot7FieldSlimExamples.lean) |
| Lemma 6.8 | **未形式化。** PAC 体を用いる論文末尾の反例。 | [範囲の宣言](Lean4/Yamaguchi26AbfaithfulGalois/All.lean) |

導入の Theorem A は Proposition 2.1 と Theorems 3.6・4.2、Theorem B は Corollary 6.5、Corollary C は Corollary 6.6 に対応します。Corollary D の sub-`p`-adic 体と高次局所体の結論は Example 6.7 にありますが、一般 Hilbertian 体の場合まで形式化済みとはしていません。旧原稿にあった「素体上無限有限生成体の有限段可解商は slim」という結論も `finitelyGenerated_finiteStepSolvable_slim` として保持しています。

## 整数上の水平因子を越える可解被覆

連結な局所 Noether スキーム `X`、水平な有効 Cartier 因子 `D`、補集合 `U = X ∖ Supp(D)` に対し、包含が誘導する**実際のエタール基本群**の写像を扱います。主定理 2.5 は、論文の境界条件 `(†)` の下で `π₁ᵉᵗ(U) → π₁ᵉᵗ(X)` の核が位相的完全であり、最大 prosolvable 商が同型になることです。同型は包含から誘導される写像と一致することまで表現しています。

`(†)` は、境界の台上での正則性、各素成分に剰余標数 `2` の normal crossings 点があること、**すべての連結有限エタール被覆の後で**各被約境界成分の一般ファイバーが幾何的整であること、の三条件です。完全核や商同型を入力として仮定する定義ではありません。

| 番号 | 現在の内容・状態 | 主なソース |
|---|---|---|
| Lemma 1.1 | 補集合の連結性、基本群写像の全射性、核が各境界成分の strict henselization の分数体から来る惰性群の閉正規生成に等しいことを証明実装。水平性や `X` 全体の正則性は追加しない。 | [1.1](Lean4/Yamaguchi26SolvableCoverings/Theorem1Dot1BoundaryQuotient.lean) |
| Lemma 1.2 | 剰余標数 `p` の normal crossings 点から、境界惰性群の実際の有限商への像の位数が `p` で割れないことを証明実装。 | [1.2](Lean4/Yamaguchi26SolvableCoverings/Theorem1Dot2InertiaControl.lean) |
| Proposition 1.3 | すべての素数について上記の点がある場合、包含によるエタール基本群の位相群同型を証明実装。 | [1.3](Lean4/Yamaguchi26SolvableCoverings/Theorem1Dot3BoundaryInvariance.lean) |
| Example 1.4(1) の一部 | 任意の幾何的基点で `π₁ᵉᵗ(Spec ℤ) = 1` を証明実装。Minkowski の判別式評価を経由する。 | [1.4](Lean4/Yamaguchi26SolvableCoverings/Theorem1Dot4FundamentalGroupIntegers.lean) |
| Example 1.4 の残り | **未形式化。** (1) の射影空間・アフィン空間、(2) の `M₀,ₙ,ℤ`、(3) の `Spec ℤ[x,y,1/(xᵃ−yᵇ)]` の結論。 | [明示された対象範囲](Lean4/Yamaguchi26SolvableCoverings/Theorem1Dot4FundamentalGroupIntegers.lean) |
| Lemma 2.1 | 一般ファイバーの幾何的整性と標数 `2` の境界条件から、包含が位相的アーベル化の同型を誘導することを証明実装。 | [2.1](Lean4/Yamaguchi26SolvableCoverings/Theorem2Dot1AbelianInvariance.lean) |
| Definition 2.2 | 論文の条件 `(†)` を `BoundaryCondition` として定義。有限エタール被覆は Galois 被覆に限定しない。 | [2.2](Lean4/Yamaguchi26SolvableCoverings/Theorem2Dot2BoundaryCondition.lean) |
| Remark 2.3 | 整数上滑らか・有限型・全射かつ一般ファイバーが幾何的連結という条件から、有限エタール被覆後の各被約成分の一般ファイバーの幾何的整性を証明実装。境界条件の第三条件への適用も収録。 | [2.3](Lean4/Yamaguchi26SolvableCoverings/Theorem2Dot3SmoothBoundary.lean) |
| Lemma 2.4 | 連結有限エタール被覆への引き戻しによる、水平性と `(†)` の保存を証明実装。 | [2.4](Lean4/Yamaguchi26SolvableCoverings/Theorem2Dot4FiniteEtaleStability.lean) |
| Theorem 2.5 / Theorem A | `perfect_kernel_2_5` が位相的完全核と最大 prosolvable 商の同型を証明実装。 | [2.5](Lean4/Yamaguchi26SolvableCoverings/Theorem2Dot5PerfectKernel.lean) |
| Corollary 2.6 | 有限剰余体を持つ完備 Noether 局所環上の連続行列表現について、`X` への延長と剰余表現の延長の同値、および延長の一意性を証明実装。 | [2.6](Lean4/Yamaguchi26SolvableCoverings/Theorem2Dot6ResidualExtension.lean) |
| Corollary 2.7 / Corollary B | **未形式化。** 射影超平面配置の補集合に対する最大 prosolvable 基本群、および追加条件下の全基本群の自明性。 | [明示された対象範囲](Lean4/Yamaguchi26SolvableCoverings/Theorem1Dot4FundamentalGroupIntegers.lean) |

このライブラリではスキームと幾何点の体を Lean の universe zero に置いています。補助層は正規化、strict henselization、局所惰性、純性、有限被覆による比較、完全核の群論、合同部分群のフィルトレーションから構成されています。

## 関連論文と共有基礎

依存ライブラリ `ProCGroups` には、Naganori Yamaguchi, [*Center-freeness of finite-step solvable groups arising from anabelian geometry*（arXiv:2601.07112）](https://arxiv.org/abs/2601.07112) の Proposition 2.5 に対応する一般群論の結論もあります。[SlimnessAndTorsion](Lean4/ProCGroups/FiniteStepSolvableQuotients/SlimnessAndTorsion.lean) の `center_eq_bot_maxSolvQuot_of_isAbTorsionFree_of_isAbFaithful` が、ab-torsion-free かつ ab-faithful な副有限群の `m ≥ 2` 段可解商の中心自明性を証明しています。これは当該論文の幾何的応用や Grothendieck 予想までの全体形式化を意味しません。

論文別の入口は次の二つです。

```lean
import Yamaguchi26AbfaithfulGalois.All
import Yamaguchi26SolvableCoverings.All
```

基礎部分は論文を越えて再利用するため、`ProCGroups`、`ValuedFieldTheory`、`GaloisCohomology`、`SchemeTheory`、およびそれらを用いる幾何学ライブラリに配置しています。全体の収録範囲は [`Lean4/All.lean`](Lean4/All.lean) と [`lakefile.toml`](lakefile.toml) で確認できます。mathlib 等の外部依存は [`lake-manifest.json`](lake-manifest.json) に固定し、取得可能な依存ソースやビルド生成物は同梱しません。

## 著者・出典

独自に作成した Lean ソースの著作権者は [Naganori Yamaguchi](https://github.com/n-yamaguchi-0729)、著者表示は `Naganori Yamaguchi (assisted by OpenAI Codex)` です。外部プロジェクトに由来する依存先のソースには、その上流の著者・著作権・出典表示を保持しています。各ファイルのヘッダと [`LICENSE`](LICENSE) を参照してください。

## 依存関係を含む配布範囲

各行のライブラリの **全 maintained source** を収録しています。主ライブラリだけでなく、ローカル import の依存先をライブラリ単位で再帰的に含めた独立パッケージです。別の非公開リポジトリを clone する必要はありません。外部依存の mathlib とその依存は Lake が固定 revision から取得します。

| 深さ | ライブラリ | Lean ファイル数 |
|---:|---|---:|
| 1 | [ProCGroups](Lean4/ProCGroups/All.lean) | 724 |
| 1 | [ValuedFieldTheory](Lean4/ValuedFieldTheory/All.lean) | 591 |
| 1 | [GaloisCohomology](Lean4/GaloisCohomology/All.lean) | 309 |
| 1 | [SchemeTheory](Lean4/SchemeTheory/All.lean) | 975 |
| 2 | [ClassFieldTheory](Lean4/ClassFieldTheory/All.lean) | 1,246 |
| 2 | [AlgebraicCurves](Lean4/AlgebraicCurves/All.lean) | 2,452 |
| 2 | [EtaleFundamentalGroups](Lean4/EtaleFundamentalGroups/All.lean) | 1,608 |
| 2 | [EtaleCohomology](Lean4/EtaleCohomology/All.lean) | 125 |
| 3 | [Yamaguchi26AbfaithfulGalois](Lean4/Yamaguchi26AbfaithfulGalois/All.lean) | 156 |
| 3 | [Yamaguchi26SolvableCoverings](Lean4/Yamaguchi26SolvableCoverings/All.lean) | 33 |

パッケージ全体の入口は [`All`](Lean4/All.lean) です。各ライブラリの元のモジュール名を保持しているため、重複するソースを含む他の分割パッケージと同じ Lake 環境へ重ねて導入することは想定していません。

## ビルドと CI

Lean は [`lean-toolchain`](lean-toolchain) の **4.35.0-rc2**、mathlib は [`lakefile.toml`](lakefile.toml) の **065356127b1dc0016f66b7283ce0ce2c4055aa55** に固定しています。再現時は同梱の [`lake-manifest.json`](lake-manifest.json) を使います。

Git と [elan](https://github.com/leanprover/elan) を用意して実行します。

```sh
git clone https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization.git
cd YamaguchiPapersFormalization
lake exe cache get Mathlib
python3 .github/scripts/audit.py
lake --wfail build +ProCGroups.All +ValuedFieldTheory.All +GaloisCohomology.All +SchemeTheory.All
lake --wfail build +ClassFieldTheory.All +AlgebraicCurves.All +EtaleFundamentalGroups.All +EtaleCohomology.All
lake --wfail build +Yamaguchi26AbfaithfulGalois.All +Yamaguchi26SolvableCoverings.All
lake --wfail build +All
```

[`CI`](.github/workflows/lean.yml) は公開済みの [ProCGroups](https://github.com/n-yamaguchi-0729/ProCGroups)・[ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory)・[SawinTotallyRealTowers](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers) の版固定・依存深さ順の検証・成果物キャッシュの構成を参考にしています。今回の CI は次を行います。

- 全物理ソースと Lake glob、入口からの到達、import の欠落・循環・逆依存を静的検査。
- 深さ1、2、3のライブラリを順に通常ビルドし、最後に `+All` をビルド。
- `autoImplicit = false`、未使用引数、文書化、mathlib 標準 linter を Lake 設定で有効化。
- 段階間でプロジェクトのコンパイル成果物を再利用し、失敗時も診断ログを保存。

`lake --wfail build` を使い、警告・エラーを失敗にします。この配布範囲には AnabelianGeometry の未証明定理を含みません。新たな `sorry` / `admit` / 独自 `axiom` は静的検査でも拒否します。静的検査は証明項の独立検証ではありません。この CI では NanoDa や別途の全宣言 kernel replay を実行したとは主張しません。

**private の push / pull request ではビルドジョブを開始せず、Actions の手動実行は可能**です。public に切り替えた後は push / pull request で動作します。初回配布では private のまま作成し、公開設定の変更も CI の手動起動も行っていません。

初回の検証結果と検証範囲は [VALIDATION.md](VALIDATION.md) に記録しています。

## ソースの来歴

分割元、固定コミット、同梱ファイルの SHA-256 は [SOURCE_SNAPSHOT.json](SOURCE_SNAPSHOT.json) にあります。Lean 本文・既存の著作権表示は分割元から変更せず、配布用 `Lean4/All.lean`、Lake の対象範囲、README と CI を作成しました。ライブラリ内の既存計画には古い配置・当時の停止点が残る場合があります。

[第三者由来のコードと帰属](THIRD_PARTY.md) および [pi1 の25ファイル対応表](PI1_ATTRIBUTION.md) も参照してください。
