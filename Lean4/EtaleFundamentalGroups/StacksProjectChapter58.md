# Stacks Project Chapter 58 formalization

This document consolidates the project scope, implementation roadmap, all three audit ledgers, and the historical handoff. The scope and ledgers are authoritative; the dated handoff is retained only as history. Current counts must be recomputed from the ledger rows.

## 1. Scope, completion criteria, and ownership


### Active work order (2026-10-09 01:42 UTC user update)

The current priority is **M2 of EtaleCohomology**, as defined in
[its plan](../EtaleCohomology/PLAN.md): proper base change and compactification.
Chapter 58 editing and validation are paused at a safe boundary. Preserve all
accepted source, successful evidence and caches; preserve remaining candidates
separately with their exact verification status. The most recent published
Chapter 58 source is source104, including both original conclusions of 0BQI.
No completion is claimed for 58.9, 58.10.6/8, 0EJX/0BLG candidates, or the
current-policy regular-local purity check.

When Chapter 58 work resumes, the latest standing preference is to choose
original theorems and lemmas that can be completed most directly from existing
proofs, anywhere in the chapter. There is no fixed section order or pre-15
completion requirement. Reconcile old ledger prose with actual declarations
before adding code. Heavy algebraization for 58.9 remains deferred; the actual
adic cover/algebra constructions are preserved. Independent Examples and Remarks
remain deferred unless a proof needs their mathematics.

The completed original endpoints in 58.8 are 0BQA, 09ZS, 0BQB and 0BQN.
In 58.10, 0BQE, 0BLQ, 0BQF, 0BSA, 0BQG and both conclusions of 0BQI have
normal leaf/required-consumer evidence and direct standard-axiom queries.
58.14.1/0BTV, 58.14.2/0BTW and 58.14.3/0BTX have their original conclusions;
reuse their object/Hom/equality descent instead of rebuilding it. Historical
planned/blocked prose is not evidence that a proof is absent.

58.15 remains paused with accepted partial results published through source96
and private drafts preserved separately. No original 0BUN/0C0J completion is
claimed. 58.13.3 remains paused.

The user explicitly stopped whole-library/broad aggregate validation and the
420-file revalidation campaign. Preserve partial records and successful caches,
but do not resume them as a separate goal. New work retains normal kernel and
resource settings, zero warnings in changed leaves, and necessary consumer
checks. Original 58.13.1, 13.2, 13.4, 13.5 and 13.6 have proved endpoints,
normal leaf/consumer checks and standard-axiom audits, published through
source76. Historical broad-check notes below are not active blockers.

### Objective

既存の `Pi1` ライブラリを import して基盤として使い、Stacks Project
Chapter 58 **Fundamental Groups of Schemes** の数学的内容を完全に形式化する。

対象を再現可能に固定するため、最初の基準版は次とする。

- chapter tag: [`0BQ6`](https://stacks.math.columbia.edu/tag/0BQ6)
- Stacks Project revision: `ed88ff78`
- PDF compile date: 2026-07-14
- tagged sections: 58.1–58.32
- 数学的項目を含む実装範囲: 58.2–58.32

PDF 末尾の “Other chapters” は参照案内で、Chapter 58 の HTML tag corpus
には含まれない。

### Meaning of “complete”

Chapter 58 の全番号付き Definition, Lemma, Proposition, Theorem, Example,
Situation, Equation, Remark を公式タグ単位で台帳に載せ、それぞれを次の
いずれかに分類する。

1. `implemented`: このライブラリで標準 API から証明済み。
2. `covered`: mathlib、`Pi1`、または明示的に許可された既存ライブラリの
   公開宣言が同じ数学的内容を既に与える。重複 theorem は作らず、宣言名と
   型の対応を台帳に記録する。
3. `non-propositional`: 導入、記法だけの equation、歴史的 remark など、
   独立した Lean 命題を作るべきでない項目。理由を台帳に記録する。

完成時には `unmapped`, `planned`, `blocked` がゼロでなければならない。
「reference」と記された Stacks 項目は、参照先の既存定理との直接対応を
確認すればよく、単なる別名 wrapper を作らない。

公式 structure の番号付き項目は 141 件（Definition 3、Lemma 108、
Proposition 11、Theorem 3、Equation 6、Example 5、Remark 4、Situation 1）。
ただし完全性はこの141件だけで判定しない。番号付きの子項目を持たない
58.7 の本文、58.3 内の列挙項目 tag `0BN1`、各節の非環境本文にある独立した
数学的主張も別台帳で監査する。

Chapter 58 の公式 rendered API 本文が直接参照する外部 tag は 284 個ある。
pinned TeX の literal `\ref` まで含めると、API に現れない `0033`, `0EKE`
を加えた286個になる。完全性監査では安全側の286個を分類する。これは28章
全体の形式化を機械的に要求するものではない。各 tag を、既存 Lean 定理、
真の上流依存、比較・例示だけの参照、後続章への参照に分類し、Chapter 58
の証明に必要なものだけを source-producing frontier とする。

### Non-negotiable constraints

- `Pi1` は移動・複製・全面改変しない。このライブラリから `import Pi1`
  する。
- `Pi1` の変更は、import/build を妨げるエラー、警告、または完全性を壊す
  基礎的 placeholder の修正に限定する。公開 API の再設計は別途判断する。
- mathlib と `Pi1` の定義を直接使い、同義の finite étale cover、fiber
  functor、Galois category、fundamental group、geometric point を作らない。
  ユーザーが明示的に許可した `ProCGroups` と `ClassFieldTheory` も、そこに
  canonical な source-producing theorem がある箇所では leaf module を直接
  import してよい。ただし umbrella import や、mathlib 宣言の薄い wrapper
  を公開 API に採用しない。
- 新ライブラリの公開 statement は、存在する場合は現行 mathlib の canonical
  API を正本にする。特に affine finite étale algebra は
  `CommAlgCat.FiniteEtale`、scheme morphism property は
  `@IsFinite ⊓ @Etale`、任意の離散連続 action は
  `DiscreteContAction TopCat G`、有限連続 action は
  `ContAction FintypeCat G` を使う。
- `Pi1` に残る並行定義を新しい公開 API へ複製しない。既存 Pi1 theorem の
  利用に真に必要な場合だけ、一つの非公開 compatibility 境界で canonical
  型へ transport する。その transport 自体を Stacks tag の進捗と数えない。
- bridge-only wrapper、単なる別名、証明付き container、assumption package
  を進捗として追加しない。
- `sorry`, `admit`, `axiom`, `proof_wanted`, `set_option` による抑制、
  `unsafe`, `implemented_by`, `extern`, 証明回避目的の `native_decide`、
  不要な `constant` を追加しない。単に build が通るだけでは完了としない。
- 後で証明すべき比較・存在・同値・全射性を theorem-shaped hypothesis として
  追加しない。
- 各新規仮定には既存定義・既存補題・直前の具体的構成という供給元が必要。
  供給元がない場合は宣言を書かず、最小の source-producing frontier に戻る。
- Stacks の証明文を逐語翻訳することは目的ではない。同じ定理を、現在の
  mathlib/Pi1 の最短で標準的な依存経路から証明する。
- 外部章の結果が必要な場合、mathlib にあれば直接使う。なければ Chapter 58
  の最初の未完了タグを生成するために必要な最小補題だけを明示的に追跡する。

### Final acceptance gates

- Chapter 58 の公式タグ台帳が全項目を網羅し、未分類がゼロ。
- 58.7、`0BN1`、非環境本文の独立主張、および286個の直接外部参照の
  監査台帳にも未分類がない。
- 全公開 Lean 宣言に対応する Stacks tag または内部支援目的が明記される。
- `Pi1` と mathlib の重複定義・不要 wrapper がない。
- 無駄な仮定、未使用の公開引数、placeholder がない。
- 全対象ファイルに `sorry`, `admit`, `axiom` がない。
- 全対象ファイルを proof-escape パターンで反復走査し、主要公開宣言の
  `#print axioms` に `sorryAx` や独自公理が現れない。通常の
  `propext`, `Classical.choice`, `Quot.sound` への依存は許容する。
- `covered` の根拠に使う `Pi1` 宣言の推移的依存にも `sorry` や
  `proof_wanted` がない。
- 小単位検証、ライブラリ全体 build、warning-as-error、公開 facade の import
  検証が成功する。
- 実行した検証コマンドと対象 revision を最終報告に残す。

### Imported-base baseline

初回静的監査では `Pi1` に次の placeholder があった。

- 現 `EtaleFundamentalGroups/GeometricFiber/FundamentalGroup.lean` の
  active `sorry` 10 個は、
  幾何点に `[IsSepClosed]`、絶対 Galois endpoint に `[IsSepClosure]`、
  連続作用に `[Algebra.IsIntegral]` という真に必要な canonical 仮定を置いて
  直接証明した。Pi1 全25 source module と root facade は strict
  `lake --wfail build Pi1`（3287 jobs、warning/error 0）で検証済みである。
- 現 `SchemeTheory/Affine/GeometricIrreducibility.lean` にあった
  `proof_wanted` 4 個と、
  それらだけが支えていた未使用の並行 class
  `Algebra.GeometricallyIrreducible` は削除済み。標準概念は mathlib の
  `AlgebraicGeometry.GeometricallyIrreducible` とし、Tag `00I7` は
  証明を再包装せず上流未実装依存として記録する。

これらに依存する endpoint を健全な `covered` と数えない。必要になった順に
`Pi1` 本体で証明して直すことは、ユーザーが許可した「Pi1 のエラー修正」に
含める。ただしファイル移動、定義複製、API の全面改変は行わない。

また初回所有権監査では、Pi1 の `Algebra.FiniteEtale`,
`RingHom.FiniteEtale`, scheme `IsFiniteEtale`、一部 tensor-product map、
morphism-property instance が現行 mathlib の canonical API と並行している。
新ライブラリではこれらを新設・再包装せず、上記 canonical API を優先する。

`Pi1`, `EtaleFundamentalGroups`, root `Lean4` package
（`ProCGroups` / `ClassFieldTheory`）は Lean/mathlib `v4.32.1` に統一する。
異なる mathlib revision を同一 Lake graph に重ねたり、CFT/ProCGroups の
定義をコピーして回避したりしない。

## 2. Implementation roadmap and current frontier


公式 corpus:

- Stacks Project, Chapter 58, tag `0BQ6`
- pinned revision `ed88ff78` (compiled 2026-07-14)
- tagged sections 58.1–58.32、数学的実装は 58.2–58.32

### Phase 0 — inventory and ownership

- Chapter 58 の全番号付き項目と公式 tag を `STACKS_TAGS.md` に列挙する。
- 各項目に status、Lean owner、既存宣言、直接依存、検証状況を記録する。
- 番号付き141項目とは別に、58.7、列挙項目 `0BN1`、非環境本文の独立主張を
  `BODY_CLAIMS.md` で追跡する。
- 公式 rendered API 本文が直接参照する外部284 tag と、pinned TeX のみに
  現れる `0033`, `0EKE` を `EXTERNAL_TAGS.md` に列挙し、既存 Lean、真の
  上流依存、比較・例示、後続参照へ分類する。
- mathlib、`Pi1`、隣接する `TameAbhyankar` などを検索し、既存結果を先に
  `covered` として確定する。
- `Pi1` の並行定義と現行 mathlib canonical API の所有権表を作り、新しい
  public statement が Pi1 固有 wrapper を増殖させないようにする。
- `Pi1` の `sorry`、エラー、互換 API を監査し、新ライブラリの健全な基礎に
  必要な最小修正だけを特定する。
- 初回 baseline は `Point.lean` の active `sorry` 10 個と
  `Compat/RingTheory/Geometric.lean` の `proof_wanted` 4 個だった。
  `Point.lean` の placeholder は canonical な必要仮定の下で直接証明へ
  置換済みで、Pi1 全25 source module と root facade の strict `--wfail`
  build（3287 jobs、warning/error 0）まで完了した。
  `Geometric.lean` の4件は未使用の並行 class
  `Algebra.GeometricallyIrreducible` にだけ属し、mathlib の canonical
  `AlgebraicGeometry.GeometricallyIrreducible` と両立しないため、その class
  と未証明 endpoint を削除した。Tag `00I7` は上流未実装依存として扱う。

完了条件: 公式 Chapter 58 にある番号付き項目の個数と台帳の個数が一致し、
本文・外部参照の台帳も揃い、最初の `planned` tag が依存関係上最小である。

### Phase 1 — foundations: §§58.2–58.7

- 58.2 Schemes étale over a point
- 58.3 Galois categories
- 58.4 Functors and homomorphisms
- 58.5 Finite étale morphisms
- 58.6 Fundamental groups
- 58.7 Galois covers of connected schemes

`Pi1` の finite étale category、fiber functor、`IsFundamentalGroup`、
profinite automorphism groupを直接使う。ここで基礎定義を作り直さない。

ただし現行 mathlib に canonical API がある箇所ではそちらを public surface
にする。58.2.1 は `DiscreteContAction TopCat G`、58.3/58.6 の有限作用は
`ContAction FintypeCat G` と `functorToContAction` を使い、追加の action
wrapper を作らない。

最初の source-producing frontier は、監査後に §§58.2–58.7 の最初の
未充足 tag とする。既存 `EtaleFundamentalGroups.GeometricFiber.FundamentalGroup`
の placeholder がその tag の健全性を支える場合のみ、同モジュールで直接修正する。

03QR の実装は次の実在モジュールに統合した。

1. `EtaleFundamentalGroups/GeometricFiber/FundamentalGroup.lean` で有限 étale absolute-Galois endpoint
   の placeholder を直接証明へ置換する。
2. `SchemesEtaleOverPoint/GeometricFiber.lean` で有限 étale幾何点の
   factorization と、任意 étale scheme の geometric fiber action を構成する。
3. `SchemesEtaleOverPoint/EtaleDecomposition.lean` で étale `K`-scheme を
   residue-field spectra の canonical coproduct に分解する。
4. `GaloisSets/Finite.lean` と `GaloisSets/Orbits.lean` で Pi1 の有限作用と
   compact group の有限軌道を再利用する。
5. `SchemesEtaleOverPoint/Equivalence.lean` で有限軌道の Pi1 同値を任意の
   離散連続 action へ拡張し、`@[stacks 03QR]` の圏同値を公開する。
6. `SchemesEtaleOverPoint/CoveringFamilies.lean` で `03QS` の covering-family
   比較を公開する。

独自の `GSet`、étale-over-field wrapper、`Fam`、`Ind` completion wrapper
は作らない。

続いて `0BMU`, `0BMV`, `0BN5` を実装済みである。`0BN5` は exact functor
から連続準同型、比較同型の選択変更による内部共役、連続準同型からの exact
functor、元の準同型の回収を別々の canonical API として実装し、まとめ用の
wrapper theorem は追加していない。root facade は全17 source module を
strict `--wfail` で通過した（3389 jobs、warning/error 0）。`0BN6` の
source-producing 補題2モジュール追加後も全19 source module の root build
を再実行し、3391 jobs、warning/error 0 で通過した。`0BN6` 統合後は全20
source module と facade の strict build を再実行し、3392 jobs、
warning/error 0 で通過した。

58.4.1, Tag `0BN6` も実装済みである。
`autHomOfCompIso_surjective_tfae` は Stacks の5条件を直接 `List.TFAE` とし、
公開用の条件 structure やまとめ wrapper は作っていない。非全射からの反例は
profinite group の proper open subgroup を分離し、その有限商を
`Finite.exists_equiv_fin`、`ULift`、`Equiv.mulAction` で正しい universe の
推移的有限連続作用へ移して構成する。主定理の追加仮定は condition (5) に必要な
`H` の terminal-object 保存だけであり、有限 limit/colimit 保存は要求しない。
単独 strict build は1627 jobs、warning/error 0、公理依存は
`propext`, `Classical.choice`, `Quot.sound` のみである。

58.4.2, Tag `0BS8` も実装済みである。
`autHomOfCompIso_comp_eq_one_iff` は複合 continuous homomorphism が `1` に
等しいことと、複合 functor の各像が終対象の有限余積に同型であることを直接
同値化する。有限余積条件は新 predicate を作らず inline で述べ、空の余積も
含める。単独 strict build は1595 jobs、warning/error 0、公理依存は標準3公理
のみで、`H`, `H'` への追加 preservation 仮定はない。統合後は21 source module
と facade の22 targetを明示した strict build が3393 jobs、
warning/error 0 で通過した。

58.4.3, Tag `0BS9` も実装済みである。
`autHomOfCompIso_exact_sequence_tfae` は公式の三条件を `List.TFAE` に直接
記述する。群論条件には ProCGroups の既存
`Subgroup.closedNormalClosure`、圏論条件には mathlib の
`Functor.essImage` と直接の `Epi` を使い、exact-sequence container、
条件 predicate、閉正規包の代替定義は作っていない。再利用可能な不足 API
として、全射連続準同型に沿う有限連続作用の restriction の本質像判定と、
閉正規包を有限連続作用で検出する定理だけを追加した。主定理の追加仮定は
0BN6 に必要な `H` の終対象保存だけで、`H`, `H'` の exactness を仮定として
再包装していない。単独 strict build は2179 jobs、root facade は全24 source
module と合わせて3450 jobs、warning/error 0、公理依存は標準3公理のみ、
禁止構文は0件である。

58.4.4, Tag `0BN7` も実装済みである。
`autHomOfCompIso_injective_iff_exists_epi_mono_span` は、誘導される profinite
group homomorphism の単射性と、各連結対象 `X'` に対する公式の
`X' ← Y' ↪ H.obj X` という epi/mono span の存在を直接同値化する。再利用可能な
source theorem `ContAction.injective_iff_exists_epi_mono_span` は、ProCGroups の
open normal subgroup API、canonical quotient action、mathlib の `Epi`/`Mono`
だけを使う。span structure、単射性の代替 predicate、exactness や
limit/colimit preservation の追加仮定はない。群作用側の単独 strict build は
2017 jobs、圏論側は2060 jobs、統合後は全26 source module と facade の27 targetを
明示した strict build が3452 jobsで、いずれも warning/error 0、公理依存は
標準3公理のみ、禁止構文は0件である。

58.4.5, Tag `0BTS` も実装済みである。
`autHomOfCompIso_range_normal_iff_terminal_decomposition` は、誘導写像の既存
monoid-hom range が正規であることと、終対象からの射を持つ各連結対象の像が
終対象の有限余積に同型であることを、公式どおり直接同値化する。source theorem
`ContAction.range_normal_iff_fixed_point_implies_trivial` は、mathlib の fixed-point
API、ProCGroups の closed range / open subgroup separation、canonical finite
left-coset action を使う。normal-image predicate、action wrapper、保存仮定は
追加していない。群作用側の単独 strict build は2013 jobs、圏論側は2060 jobs、
統合後は全28 source module と facade の29 targetを明示した strict build が
3454 jobsで、いずれも warning/error 0、公理依存は標準3公理のみ、禁止構文は
0件である。

58.5.1, Tag `0BN8` は既存定理で完全に covered である。Pi1 の
`AlgebraicGeometry.FiniteEtale.equivFintypeCat` が `[IsSepClosed Ω]` の下で
scheme-level の `FiniteEtale (Spec (.of Ω)) ≌ FintypeCat` を直接与える。
`AlgebraicGeometry.IsFiniteEtale.eq_inf` により source category の条件は
mathlib canonical property `@IsFinite ⊓ @Etale` と同一であり、canonical category
を明記した endpoint もこの等式を一度 rewrite するだけで type-check する。
mathlib の affine-algebra 版 `CommAlgCat.FiniteEtale.equivOfIsSepClosed` と再合成した
公開 equivalence は重複 wrapper になるため追加しない。

58.5.2, Tag `0BN9` も Pi1 の finite limit/colimit と base-change exactness API で
covered 済みである。58.5.3, Tag `0BNA` も canonical な2つの忘却関手に対する
finite-limit / finite-colimit preservation を直接実装した。58.5.4, Tag `0BL7` は
有限自由アフィンの場合まで実装済みである。`Affine.WeilRestriction` は有限自由
`R`-代数 `A` と有限表示 `R`-代数 `B` に対して
`C ↦ Hom_R(B, C ⊗_R A)` の corepresenter を構成し、
`Affine.WeilRestrictionProperties` は任意の基底変換との可換性、および `A`, `B`
が有限エタールである場合の corepresenter の有限エタール性を証明する。一般の
有限エタール `A` は有限射影であって大域的に自由とは限らないため、局所構成の
貼り合わせと任意 scheme への降下を用いる。その構成は
`AlgebraicGeometry.FiniteEtale.exists_internalHom` に統合済みであり、2026-10-03 の
strict root build と標準公理監査を通過した。

### Phase 2 — invariance and connectedness: §§58.8–58.10

- universal homeomorphism による finite étale category / π₁ の不変性
- proper schemes の finite étale covers
- local connectedness と connected components

### Phase 3 — normal schemes and ramification: §§58.11–58.13

- normal schemes の π₁
- group actions and integral closure
- decomposition/inertia groups と ramification theory

既存の field-theoretic Galois/ramification API を優先する。

0BUA/0BUB では CFT の
`RamificationTheory.HilbertRamification.ResidueExactSequence`,
`RamificationTheory.GaloisValuation.Ramification`,
`RamificationTheory.HilbertRamification.CharacterExact` を有限段の正本とし、
ProCGroups の canonical pro-\(p\) predicate
`ProC.HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p)` と有限段因子化を
無限逆極限部分に使う。CFT/ProCGroups の umbrella import はしない。

### Phase 4 — exact sequences and functoriality: §§58.14–58.18

- geometric and arithmetic fundamental groups
- homotopy exact sequence
- specialization maps
- closed subscheme restriction
- pushouts and fundamental groups

連続準同型・exactness は既存の topological/profinite group API で表現し、
独自の exact-sequence container を作らない。

### Phase 5 — punctured spectra and local purity: §§58.19–58.26

- finite étale covers of punctured spectra I–IV
- purity in the local case I–III
- purity of branch locus

外部依存が大きいため、各 tag ごとに必要な commutative algebra / scheme
theory の最小 source-producing frontier を明記してから実装する。

### Phase 6 — global purity and specialization: §§58.27–58.30

- Lefschetz for the fundamental group
- purity of ramification locus
- affineness of the complement
- specialization in the smooth proper case

### Phase 7 — tame and positive characteristic: §§58.31–58.32

- tame ramification
- Abhyankar's lemma
- positive-characteristic tricks

隣接する `TameAbhyankar` に対応する標準的な公開定理がある場合は直接再利用し、
Chapter 58 用の別定義・別 theorem を重複して作らない。

### Phase 8 — final integration

- `EtaleFundamentalGroups.lean` から完成した section facades を依存順に public import。
- tag 台帳の `unmapped`, `planned`, `blocked` をゼロにする。
- 仮定・namespace・定義所有先・重複 API・不要 wrapper を全件監査する。
- 共有 WSL の CFT build と専用枠を調整し、小単位から全体へ検証する。
- warning-as-error と root import の検証を通す。

### Current frontier

1. Pi1 の25ソースモジュールと facade は、26 target を明示した
   `--wfail` build で3287 jobs、warning/error 0。
2. Chapter58 の既存基盤、`03QR`, `03QS`, `0BMU`, `03SF`, `02GL`、有限連続作用の
   exactness、fiber functor の有限余極限保存は strict build 済み。root facade
   も warning/error 0。
3. 三台帳は上記の検証結果へ更新済み。今後も各 frontier 完了時に同じ
   strict-build 根拠で更新する。
4. `0BMV`、`0BN5`、`0BN6`、`0BS8`、`0BS9`、`0BN7`、`0BTS` は strict build と
   禁止構文・公理・仮定監査を通過し、`0BN8` は Pi1/mathlib の canonical API
   へ厳密対応付けた。58.5.3, Tag `0BNA` も実装完了した。極限側は
   `ForgetExactness` の canonical functor に対する3個の直接 instance、余極限側は
   `ForgetFiniteCoproducts` と `ForgetFiniteCoequalizers` からなる。後者は有限
   エタール代数を fpqc 局所的に有限 copower へ split し、被覆片と二重交叉上の
   coequalizer を Tag `0BMN` で descent する。公開される coequalizer / finite-colimit
   preservation instance 4個の単独 strict build は2964/2964 jobs、root facade は
   3459/3459 jobsで、いずれも warning/error 0、公理依存は `propext`,
   `Classical.choice`, `Quot.sound` のみ、禁止構文は0件である。
   58.5.4, Tag `0BL7` の有限自由アフィン部分も実装した。明示的 corepresenter、
   任意基底変換同型、有限エタール性まで2 target の strict build は2597/2597 jobs、
   root facade は3460/3460 jobsで、禁止構文・公理・仮定監査も通過している。
   完全な Tag の canonical endpoint は
   `Functor.RepresentableBy` を用いた finite étale relative internal Hom の表現可能性
   であり、有限射影 source の局所貼り合わせと任意 scheme への降下が残る。
   Source update (2026-09-23; no Lean/Lake execution):
   `SchemeTheory.WeilRestriction.Sheaf` now contains the general sheaf argument,
   and `SchemeTheory.WeilRestriction.BaseChange` constructs restriction under
   arbitrary scheme base change and transport of the representability witness.
   `SchemeTheory.Affine.WeilRestriction.Global` extends the affine result to all
   test schemes and identifies the representer with the explicit spectrum.
   `GlobalFiniteEtale` gives its finite etale structure and arbitrary-scheme
   base-change representability; `GlobalBaseChange` identifies affine base
   change with the spectrum of the scalar-extended representing algebra.
   `Local.exists_finiteEtaleInternalHomRepresentable_away` constructs actual
   finite etale representers near every prime, without global freeness of A.
   A further source update constructs the principal cover in `LocalCover`
   and its directed refinement in `Glued`. The general
   `SchemeTheory.WeilRestriction` modules construct canonical local transition
   maps, prove their pullback and composition laws, and build relative gluing
   data. `CoverHypercover` and `GluedUniversal` glue the actual universal
   elements using the sheaf condition. `GluedComparison`, `LocalIsomorphism`,
   and `GluedRepresentable.gluedLocalRepresentable` then establish the global
   representing property. Finite etaleness descends along the same cover.
   `SchemeTheory.Affine.WeilRestriction.GluedRepresentable` supplies
   `finiteEtaleInternalHomGluedRepresentable` and
   `finiteEtaleInternalHomGluedBaseChangeRepresentable`: finite etale A/B now
   have all-test-scheme representations without assuming `Module.Free R A`,
   and these representations persist under arbitrary scheme base change.
   `SchemeTheory.WeilRestriction.Affine` transports this construction to
   arbitrary finite etale objects over an affine scheme via global sections
   and the cartesian naturality square of `isoSpec`. `FiniteEtale` applies the
   gluing theorem on the existing directed affine cover of any base scheme.
   The terminal statement is now source-implemented as
   `AlgebraicGeometry.FiniteEtale.exists_internalHom` in
   `EtaleFundamentalGroups/FiniteEtale/InternalHom.lean`, including arbitrary
   base change and without connectedness or freeness assumptions.
   These source additions were checked against source APIs and statically
   audited for imports, forbidden proof escapes, and unbounded automation;
   they have not been typechecked, as requested. No Lean/Lake command or
   heartbeat measurement was run, so Tag 0BL7 remains `planned` in the
   validation ledger. Its full mathematical statement now has a source
   implementation; strict validation is pending, rather than a missing gluing
   argument. Further source work can proceed to its Chapter 58 consumers.
   This is not a completed-Chapter-58 or completed-validation claim.
5. Source update (2026-09-23; no Lean/Lake execution): full statements for
   `0BND`, `0BNE`, and `0BQE` now have source implementations. Base-point
   comparison includes its topological group isomorphism, explicit dependence
   up to inner conjugation, and compatibility with finite continuous actions.
   The absolute-Galois comparison uses the actual algebraic-closure geometric
   point and supplies the action/forgetful-functor comparison. Dense pullback
   is faithful with no auxiliary finiteness or reducedness hypotheses on the
   base. The seven new modules are integrated into their existing aggregates;
   source API, import, proof-escape, and whitespace checks were performed.
   They remain `planned` for validation: no typechecking or heartbeat
   measurement was run. A further source update completes the statement of
   `0BQA`: `SchemeTheory.FiniteEtale.ClopenPullback` proves unique descent of
   clopen subsets, and the three `SchemeTheory.Topology.ConnectedComponents*`
   modules supply Tag `005F`, Hausdorffness of the connected-component
   quotient, and its homeomorphism criterion. None assumes that the original
   space is Hausdorff. `FiniteEtale.ConnectedComponents` applies these to the
   actual scheme map under the official qcqs hypotheses, and also proves
   preservation and reflection of connectedness without qcqs assumptions.
   `GeometricFiber.PullbackEquivalence` constructs the topological group
   isomorphism with the original canonical homomorphism as its forward map.
   These six source modules are integrated and independently reviewed;
   typechecking remains pending, so `0BQA` also remains `planned`.
6. Source update (2026-09-23; no Lean/Lake execution): the general
   henselian-pair equivalences `09ZL` and `09ZS` now have full source implementations.
   Mathlib already defines `HenselianRing R I` for arbitrary ideals; its
   `jac` field supplies the Jacobson condition. `JacobsonIntegral` proves
   that this condition persists under integral extension, and
   `JacobsonRigidity` uses the unramified separability element to detect
   algebra maps modulo such an ideal. `JacobsonConservativity` proves
   bijectivity of finite etale algebra maps from bijectivity after quotient
   base change, using Nakayama and the finitely generated idempotent kernel.
   `JacobsonBaseChange` packages these results as faithfulness and reflection
   of isomorphisms for the actual `CommAlgCat.FiniteEtale.baseChange` functor.
   `Algebra.Etale.exists_etale_lift_of_quotient` in `EtaleQuotientLift` now
   source-implements `04D1`: lift a finite submersive presentation and
   localize at its Jacobian, then construct the required tensor comparison.
   This lift is etale, without a claim that it is finite as a module.
   For the finite-component extraction used in `09XH`,
   `Scheme.Hom.normalizationFiniteFactor` constructs the map of a finite
   open factor into the base-changed normalization and proves its image
   clopen, using the existing Zariski main theorem for quasi-finite maps.
   `PrimeSpectrum.exists_lift_idempotent_basicOpen_le` constructs a
   representative of a quotient idempotent whose principal open lies in a
   prescribed open neighborhood; the representative need not be idempotent.
   A further source update adds thirteen supporting modules.
   `Normalization.Affine` identifies relative normalization with the spectrum
   of the literal integral closure. `OpenImmersionQuotient` constructs the
   quotient pushout and its spectrum pullback, and `QuotientBaseChange`
   supplies the canonical quotient algebra map and tensor naturality.
   `FiniteOpenFactor` and `IdempotentQuotientFactor` construct the product
   decomposition of a finite open factor. `OpenImmersionLocalization` then
   proves bijectivity of the actual localization map on a principal open
   contained in the image. `OpenImmersionFiniteFactor` combines these with
   the controlled representative, and `Normalization.QuotientFiniteFactor`
   supplies the integral-closure product and localized inclusion for a
   finite-type quasi-finite algebra. This proves the specialization of the
   finite-factor extraction needed for etale algebras; the full `09XH`
   statement without global quasi-finiteness is not claimed.
   `DeterminantTrickCongruence` works with finite generating families, without
   freeness, and `CyclicIdempotentAnnihilator` constructs a monic annihilator
   reducing to `(X - 1) * X ^ d`, with positive d. `HenselianCyclicIdempotent`
   applies the native henselian-pair axiom to lift a quotient idempotent whose
   component is generated over the base by its unit. This is a cyclic-factor
   result, not yet general finite-algebra idempotent lifting.
   `IntegralLocalizationFiniteModel` extracts a finite subalgebra with the
   same principal localization. `IntegralLocalizationIdempotentModel`
   additionally captures the finite coefficients of the ideal-membership
   witness, so the quotient idempotent actually descends to this model.
   All thirteen modules are integrated into the existing aggregates and
   independently reviewed against source APIs.
   A subsequent source update adds sixteen modules and extends the finite
   model construction. `IdempotentLocalizationCyclicity` now proves the
   missing cyclicity by clearing denominators in extended ideals.
   `HenselianIntegralCyclicIdempotent` applies the finite model and lifts its
   idempotent in the integral closure. `JacobsonIdempotentFactor` makes the
   chosen principal element a unit on the lifted factor, and
   `LocalizationIdempotentFactor` identifies the actual quotient factors.
   `EtaleSection`, `CyclicIdempotentFactor`, `IdempotentFactor`, and
   `JacobsonSection` supply the section's open immersion, residual scalar
   surjectivity, etaleness of the factor, and its identification with the
   base. `Normalization.HenselianSectionFactor` combines these constructions.
   The resulting `Algebra.Etale.bijective_comp_quotient_of_henselian` in
   `HenselianEtaleSection` proves existence and uniqueness of sections over
   an arbitrary native henselian pair, without module finiteness of the
   etale algebra.
   `HenselianFactorization` applies this theorem to the native universal
   coprime factorization ring to lift monic coprime factorizations with
   exact reductions. `IdempotentAnnihilator` constructs annihilators for
   arbitrary quotient idempotents using a doubled generating family;
   `IdempotentFromCoprimeFactors` evaluates a Bezout identity to produce a
   lift. `HenselianFiniteIdempotent` therefore lifts every quotient
   idempotent in a finite algebra, without the earlier cyclicity condition.
   The finite-model construction now also works without a finite-type
   localization hypothesis. `HenselianIdempotents` extends existence to
   every integral algebra and combines `JacobsonIdempotentRigidity` with
   `JacobsonIntegral` to prove that the actual quotient map is bijective on
   idempotents. Thus the etale-section and integral-idempotent implications
   of `09XI` needed by `09ZL` now have source implementations; the full
   equivalence of all characterizations of `09XI` is not claimed here.
   `IdempotentFactorReduction` identifies the actual double quotient with
   the reduced idempotent factor, including explicit formulas on quotient
   representatives. `HenselianQuotientLift` now extracts a finite etale
   factor of the arbitrary etale lift: the lifted integral-closure
   idempotent selects a factor on which the principal element is a unit,
   localization identifies that factor with an etale quotient, and
   integrality gives module finiteness. Its reduction is the prescribed
   algebra, via the canonical quotient/tensor comparison.
   `HenselianFullness` lifts the idempotent of the graph of a residual map
   in the tensor product. The resulting finite etale factor is isomorphic
   to the target algebra by Jacobson conservativity. This constructs maps
   without assuming a Henselian structure on the target algebra.
   `CommAlgCat.FiniteEtale.baseChange_isEquivalence_of_henselian` in
   `HenselianBaseChange` combines these actual constructions with
   faithfulness, proving Tag `09ZL` for the canonical base-change functor.
   `AlgebraicGeometry.FiniteEtale.pullback_isEquivalence_of_henselian` in
   `EtaleFundamentalGroups/FiniteEtale/HenselianPair.lean` transports this
   along the existing affine naturality isomorphism. Its public statement
   is the canonical pullback for `@IsFinite ⊓ @Etale`, proving the full
   source statement of Tag `09ZS`. The five new modules are integrated
   into the existing aggregates and independently reviewed.
   Tag `0BQB`, invariance under arbitrary scheme thickenings, now also
   has a full source implementation. `HenselianRing.of_le_nilradical` in `HenselianNilIdeal`
   now proves the Henselian assertion for an arbitrary nil ideal, with no
   uniform nilpotence exponent. Each polynomial's initial error generates
   a nilpotent principal ideal, whose terminating adic filtration is
   complete; the native Henselian axiom then supplies the required root.
   `FiniteEtale.AffineThickening` applies the Henselian equivalence to nil
   quotients, factors arbitrary surjective ring maps with nil kernel
   through the actual kernel quotient, and proves the canonical pullback
   equivalence for every surjective closed immersion with affine target.
   Its proof extracts the quotient spectrum using `IsClosedImmersion.Spec_iff`
   and derives the nil condition from surjectivity on prime spectra.
   `FiniteEtale.PullbackRepresentable` supplies the final comparison
   needed by the global construction: if `T ↦ Hom(i* T, V)` is represented
   by `W` and `i` is a monomorphism, then `i* W` is isomorphic to `V`, using
   the actual slice adjunction and uniqueness of representing objects.
   These three modules are independently reviewed and integrated.
   `FiniteEtale.ThickeningFullyFaithful` now proves unique lifting of maps
   into finite etale schemes across any surjective closed immersion, by
   gluing the affine lifts on the directed affine cover. This gives Hom
   bijectivity for arbitrary slice-source schemes and finite-etale target
   objects, and hence the canonical pullback's full faithfulness.
   `FiniteEtale.ThickeningGluing` chooses the actual affine lifts and uses
   this Hom bijection to make them local representers of the pulled-back
   Hom presheaf. Explicit pullback comparison isomorphisms identify the
   local restrictions. The existing sheaf-gluing construction supplies
   transition maps, cocycles, and the global finite-etale representer;
   `pullbackIsoOfRepresentable` identifies its reduction with the given
   cover. Thus essential surjectivity is proved without an assumed descent
   equivalence or gluing witness.
   The terminal theorem is
   `AlgebraicGeometry.FiniteEtale.pullback_isEquivalence_of_surjective_closedImmersion`
   in `EtaleFundamentalGroups/FiniteEtale/Thickening.lean`. It has exactly
   the native closed-immersion and surjectivity hypotheses, uses
   `@IsFinite ⊓ @Etale`, and imposes neither quasicompactness nor a uniform
   nilpotence bound. These three further modules have independent static
   review and are integrated. Tag `0BQB` is now `planned` for validation,
   rather than blocked by a missing global source proof.
   Further source work for `0BQN` constructs the canonical comparison of
   the two finite-etale pullbacks along a separated universally injective
   morphism. `RadicialDescentIso` lifts the identity comparison through the
   fully faithful diagonal pullback and proves its normalization and
   uniqueness. `RadicialDescentCocycle` proves the actual equation on the
   threefold fiber product, using faithfulness along the small diagonal.
   `Morphisms.EtaleRadicial` proves that a universally injective etale map
   is an open immersion; surjectivity makes it an isomorphism.
   `Morphisms.RadicialDescent` descends universal injectivity through a
   surjective first factor. `Etale.UniversalHomeomorphismSections` then
   constructs actual descended sections: the image of a section is open,
   its image under the base-change homeomorphism gives an open subscheme,
   and this subscheme projects isomorphically to the base. This proves
   existence of relative maps into arbitrary etale schemes.
   `FiniteEtale.UniversalHomeomorphismFullyFaithful` derives Hom
   surjectivity for arbitrary slice-source objects, Hom bijectivity for
   separated etale targets, and Full/Faithful/FullyFaithful structures for
   the canonical finite-etale pullback. No effective-object-descent
   assumption or custom descent container is used.
   `Morphisms.FiniteDescent` proves finiteness of a separated etale map
   dominated surjectively by an integral composite. For the object
   descent route, `Normalization.HenselianIntegralSection` lifts etale
   sections over integral extensions of a Henselian pair, and
   `RingTheory.HenselianIntegral` constructs the native HenselianRing on
   the extended ideal, without a module-finiteness assumption.
   `FiniteEtale.Algebra.IntegralFiniteModel` constructs an actual finite
   subalgebra and finite-etale model of any finite-etale algebra over an
   integral extension. It uses the native etale finite-presentation
   model and flatness to reflect integrality into that model.
   All ten new leaves have source API and independent static review.
   A further eleven leaves supply concrete input for effective object descent:
   `AffineUniversalHomeomorphismModel` retains surjectivity and universal
   injectivity in the finite intermediate model; `ResidueFieldExtension`
   realizes a prescribed finite separable residue extension in an actual
   etale neighborhood (`00UD`); `IsomorphismNeighborhood` constructs the
   isomorphism neighborhood of a finite etale singleton fiber (`04DH`).
   `FaithfullyFlatAlgebra` reconstructs an algebra from its genuine comonad
   coaction as an equalizer subalgebra, and `Algebra.FaithfullyFlatDescent`
   proves that this constructed algebra is finite etale. `AlgebraCoaction`
   extracts a native coaction from a tensor-form overlap isomorphism and
   its actual diagonal and triple-cocycle equations. `ChosenResidueExtension`
   constructs a selected tensor-product prime with purely inseparable residue
   extension. `FiniteNeighborhoodSection` constructs an actual finite open
   factor and sections after shrinking the base. `ResidueBaseChange` proves
   the needed pointwise residue-field property under arbitrary base change.
   `AffineAlgebraCoaction` transports an affine scheme overlap isomorphism
   and its diagonal law to the literal algebra form. `SectionFactor`
   splits a section off with an actual finite-etale complementary quotient.
   These source proofs are independently statically reviewed and integrated,
   without a build.
   Source implementation and validation update (2026-10-03):
   `Etale/AffineResidueField.lean` supplies
   `AlgebraicGeometry.Scheme.Spec.residueFieldIso_inv_residueFieldMap`, the naturality equation
   between `Scheme.Spec.residueFieldIso`, the scheme residue map, and
   `Ideal.ResidueField.map`, using global evaluation and residue-field
   extensionality. `residueFieldMap_isPurelyInseparable_iff` transports pure
   inseparability through these canonical isomorphisms.
   `Etale.FiniteRadicialLocalSection` now supplies
   `AlgebraicGeometry.Etale.exists_affine_section_over_finite_radicial_neighborhood`:
   for a finite etale local factor with a singleton fiber, pure inseparability
   of its composite residue extension from the bottom ring produces an
   actual section over the inverse image of an open neighborhood on the
   finite universally injective base. The intermediate residue extension
   is derived from the actual residue-field tower, not assumed separately.
   Both leaves are reachable from `SchemeTheory.All` through `Etale.All`.
   Direct imports, proof-escape/automation scans, and the local assumption
   sources were checked. Both leaves pass `lake --wfail build` (3067 jobs),
   and `SchemeTheory.Etale.All` passes its strict aggregate build (3174 jobs).
   All three endpoints depend only on `propext`, `Classical.choice`,
   and `Quot.sound`. Source snapshots did not change during either build.
   This completes the ring/scheme residue-map comparison substep. It does
   not yet assemble the finite factors into the needed etale covering family:
   the factor-to-base-change map, its singleton-fiber property, and the
   residue comparison after factor localization still need to be constructed
   from `ChosenResidueExtension`, `ResidueBaseChange`, and
   `exists_etale_finite_factor_of_quasiFiniteAt`.
   The remaining source gap for `0BQN` is constructing the needed
   etale local covers, expressing their scheme overlap isomorphisms in
   the required tensor form, and effecting object descent for finite
   universal homeomorphisms.
   The comparison, cocycle, and fully faithful functor do not by
   themselves supply an object preimage or an equivalence.
   No local, Noetherian, or completeness hypothesis replaces the general
   henselian pair. The dated no-execution records above describe their
   original source-only stage; current validation is recorded below.
7. 2026-10-03 のユーザー指示により Chapter 58 全体の完了目標を設定し、
   Lean/Lake 実行を再開した。以前の58.8.4までという範囲上限は解除する。
   `EtaleFundamentalGroups.All` は strict build (6008 jobs) を warning/error 0、
   exit code 0 で通過した。増分 build の job 数であり、再コンパイル数ではない。
   ローカル import closure の source snapshot に変化はない。
   `0BL7`, `0BND`, `0BNE`, 完全性判定 `0BS9` と新規局所補題の計13宣言は
   標準3公理のみで、`sorryAx` と独自公理はない。
   番号付き台帳は106未完、本文台帳は19未完。全章の数学的完了は未達成。
8. 同日の anabelian geometry 優先指示により、次の frontier は `0BTX` に必要な
   有限 étale 被覆・射・同型の有限体拡大への降下とする。`0BQN` の未完部分は
   後続に保持する。有限 factor の射・剰余体比較、étale 局所 section 被覆、
   scheme cocycle の tensor 形への移送は未完であり、
   `AffineAlgebraCocycle.lean` は未作成。ac・jvライブラリは変更しない。

9. 同日の重複回避・import 制限の指示を反映し、有限中間体への affine な対象降下を
   `SchemeTheory.FiniteEtale.Algebra.FiniteFieldModel` に実装した。
   `Algebra.FiniteEtale.exists_finiteIntermediateField_model` は、代数拡大 `L/k` と
   実際の `CommAlgCat.FiniteEtale (R ⊗[k] L)` から、有限中間体 `F`、
   `CommAlgCat.FiniteEtale (R ⊗[k] F)` のモデル、包含の literal tensor map による
   scalar extension の同型を構成する。モデルの存在・比較を仮定していない。
   既存の有限 integral subalgebra モデルと有限係数 tensor lift を再利用し、
   tensor lift の有限個の係数環を一つの有限中間体へまとめた。
   leaf の strict build (2581 jobs)、最小の `SchemeTheory.FiniteEtale.Algebra.All`
   (3212 jobs)、標準3公理のみの監査を通過し、両 build 中の source は不変。
   `SchemeTheory.All` からの集約到達性を reverse import graph で確認した。
   射・同型の有限中間体への降下、qcqs の貼り合わせ、誘導される群の極限比較は
   未完であり、`0BTV` / `0BTX` の全体 status と未完台帳数は変更しない。

10. `EtaleFundamentalGroups.GenericTensor.FilteredColimit.IntermediateFieldDiagram`
    に実際の中間体 diagram / cocone / `IsColimit` を構成した。
    `Finset L` を同じ universe の filtered index とし、各点は
    `IntermediateField.adjoin k s`、射と cocone leg はその包含である。
    各係数は単元集合の生成体に属し、各 leg は equality を検出するため、
    mathlib の filtered type colimit 判定と forgetful functor の反映により
    元の拡大体 `L` が `Under (CommRingCat.of k)` で colimit になる。
    diagram 自体は任意の体拡大に対して構成した。代数拡大の場合の各段の
    有限次元性は mathlib の `IntermediateField.finiteDimensional_adjoin` が供給する。
    leaf strict build (1839 jobs) と `GenericTensor.FilteredColimit.All`
    (1949 jobs)、3公開定義の標準3公理のみの監査を通過し、source は不変。
    root への到達性を reverse import closure (5 modules) で確認した。
    既存の一般同型降下 theorem への接続は未完。
    具体的には tensor base-change functor の点で `mkUnder k L` の
    algebraMap-derived 作用と元の `Algebra k L` が別の instance 表現になり、
    その上の `R`-tensor / `Under R` の作用も通常の tensor 作用へ移送する必要がある。
    点の projection 展開と `toAlgebra_algebraMap` による局所的照合を試したが、
    literal tensor 同型との型比較は未解決。仮定の追加・instance の shadowing・
    上限変更による回避はしていない。未検証の `FiniteFieldAlgEquiv` 接続は本番から
    除き、作業用 prototype のみに保持する。`0BTV` / `0BTX` の status は変えない。

11. 同日のエージェント利用許可により、既存 API・型変換・検証監査を並行した。
    `GenericTensor.FilteredColimit.FiniteFieldTensorDiagram` に、有限次元の実際の
    `IntermediateField k L` を添字とする `R ⊗[k] F` の diagram、literal な包含
    tensor map の cocone、代数拡大の場合の `IsColimit` を構成した。
    有限段の共通上界は既存の `finiteDimensional_sup`、元の有限段への lift は
    `ValuedFieldTheory.Valuation.Completion.FiniteSubfieldTensor`、等式の検出は
    mathlib の flat tensor injectivity を再利用した。点の内側で `Under k` の
    作用を再生成せず、native tensor ring を `Under R` に置く。
    `AlgEquivDescent` の既存の有限表示 compactness 証明から
    `exists_tensorProduct_algHom_stage_of_filteredColimit` を切り出した。
    始域のみの有限表示から、実際の有限段の代数射と cocone の可換図式を構成する。
    既存の同型降下はこの定理を往復に二回使用し、別の降下 algorithm は追加しない。
    strict leaf build は新 diagram が2190 jobs、一般射降下が1944 jobs。
    最小 aggregate は2209 jobs、一般射降下 owner の既存 direct consumers
    `ChosenFactorFilteredDescent` / `GeometricStalkTensorDescent` は3069 jobs。
    すべて warning/error 0、実行中の local source hash は不変。
    新 diagram の6宣言、一般射降下と既存同型降下の計8宣言を公理監査し、
    `propext`, `Classical.choice`, `Quot.sound` のみだった。
    変更 module の reverse import closure は機械的に27 module と判定し、
    root 到達性を確認した。新 leaf は canonical aggregate に収録した。
    実行した closure はすべて ac・jv を含まず、禁止中の root build は行わない。
    native finite-field tensor と一般降下の接続はまだ未完である。
    `Under` の代数作用は `toAlgebra_algebraMap` の左辺まで照合できたが、
    作用を書き換えると、それに依存する `SMulCommClass` の証明が残る。
    型全体の変換は carrier・環構造・代数作用の一致に分解できるが、その移送と
    literal な往復の可換性は未検証。未検証の接続は本番から除き、今回の
    `tmp/efg-ch58-20261003-build/FiniteFieldAlgEquivNativePrototype.lean` に保持する。
    次の最小事実はこの正準構造の移送と可換図式の検証であり、比較を仮定しない。
    その後、先に選んだ有限中間体 `F₀` 上の2モデルについて、有限 `E ≥ F₀`
    上の射・同型へ移す。相対拡大 `L/F₀` は既存の algebraicity tower、
    `IntermediateField.restrictScalars`、`Module.Finite.trans` を使用する。
    native tensor の比較には既存の `commRight` / `cancelBaseChange` を用い、
    `FieldComponent.Tower` の既存 base-change owner と重複する API を作らない。
    qcqs の貼り合わせ・群の極限比較は後続のまま。`0BTV` / `0BTX` の status、
    番号付き106未完・本文19未完、および全章完了の目標は維持する。

12. 同日の native な有限部分体への射・同型降下を完成した。
    `GenericTensor.FilteredColimit.FiniteFieldDescent` に、固定した `R`-代数
    `B`, `D` について、代数拡大後の射・同型を実際の有限中間体へ降ろす
    `exists_finiteIntermediateField_tensorProduct_algHom` と
    `exists_finiteIntermediateField_tensorProduct_algEquiv` を追加した。
    射では始域だけの有限表示、同型では両側の有限表示を用いる。
    前段の native diagram と既存の一般降下 owner を直接使用し、同型では
    literal tensor map に対する往復両方の可換性を保存する。
    `toAlgebra_algebraMap` の等式に沿う移送は、作用を添字に持つ非公開の
    tensor family と mathlib の `AlgEquiv.cast` を用いた。同じ正準の
    tensor dictionary を共有し、既存対象の作用を再設置しない。
    作用変更の可換性と同型の往復回収は、記号的な作用の等式を場合分けして
    証明する。公開定理の data-bearing instance は9、共通の可換性補題は11、
    同型回収補題は8として監査した。競合する作用・追加仮定・制限値の増加はない。
    `FieldComponent.Tower` の既存4宣言の右因子を `Field` から `CommRing`
    に一般化した。座標環 `R` に適用するために必要な変更で、後続の field
    component 側の仮定は維持した。新しい base-change owner は作らない。
    Tower の strict leaf は2451 jobs、6 direct consumer 全件を含む最小
    aggregate / consumer 検証は3260 jobs。native 射・同型の strict leaf は
    2208 jobs、最小 `FilteredColimit.All` は2210 jobsである。
    すべて warning/error 0、local source hash 不変。Tower 4宣言と native
    2定理は標準公理 `propext`, `Classical.choice`, `Quot.sound` のみ。
    変更3 module の reverse import closure の union は141 moduleで、root
    到達性を確認した。native leaf は canonical aggregate に収録した。
    実行した closure は ac・jv を含まず、両者16 moduleを含む root は再 build
    しない。番号付き106未完・本文19未完と、全章完了の目標は維持する。
    次は、先に選んだ2モデルの有限体を合成体 `F₀` にそろえ、相対拡大
    `L/F₀` へ今回の降下を適用して有限 `E ≥ F₀` 上の射・同型を得る。
    既存 `Tower` owner、`Algebra.IsAlgebraic.tower_top`、
    `IntermediateField.extendScalars.orderIso`、`restrictScalars`、
    `Module.Finite.trans` の実際の組み合わせは scratch で検証済みであり、
    これらの検証用 wrapper は本番に追加しない。モデル間の tensor 比較と
    literal map の塔の互換性、qcqs の貼り合わせ、群の核・像の一致は未完。
    `0BTV` 全体と `0BTX` の status は引き続き未完である。

13. **2026-10-03 — 先に選んだ有限体上のモデルの射・同型降下。**
    `RelativeFiniteFieldTensorDiagram` は有限 `F₀` を含む実際の有限中間体を
    `Under F₀` で添字付けし、native な `R ⊗[k] E` を `R ⊗[k] F₀` の下で扱う。
    既存の tensor colimit に mathlib の `Under.post` / `IsColimit.underPost`
    を適用する。有限係数の持ち上げ・単射性・compactness の証明は再実装しない。
    3つの RingHom 境界は literal inclusion tensor map と `rfl` で一致する。
    `RelativeFiniteFieldDescent` の2公開 endpoint は、有限 `F₀` 上のモデル間の
    射・同型を、実際の有限 `E ≥ F₀` 上の native tensor products へ降ろす。
    射では始域のみの有限表示、同型では両側の有限表示を用い、同じ `E` で
    forward / inverse の可換式を保存する。stage の base-change leg は既存
    `filteredTensorToColimitAlgHom` を native 型へ移し、その pure tensor 上の式が
    literal `TensorProduct.map (id R R) E.val` と一致することを `rfl` で確認した。
    point の作用は局所登録のみ、stage の作用は結論内の1回のみで、本文で再設置しない。
    公開文脈の data-bearing binders は9、正準 point/stage の2作用込みで最大11、
    helper は最大9。追加の降下仮定・競合 instance・制限値の増加はない。
    strict leaf は diagram が2191 jobs、相対射・同型が2209 jobs、最小 aggregate は
    2212 jobs。すべて warning/error 0、local source hash 不変。9公開宣言の kernel
    audit は標準3公理のみ。reverse import union は6 moduleで root 到達を確認した。
    実行 closure は ac・jv を含まず、両者16 moduleを含む root は再 build しない。
    canonical `CommAlgCat.FiniteEtale` の2対象と実際の射・同型を、新 endpointへ
    直接適用する consumer を strict 検証した。有限表示は既存
    `Algebra.Etale.finitePresentation` が供給し、新しい仮定を置かない。
    先に選んだ `F₁`, `F₂` のモデルを合成体 `F₀ = F₁ ⊔ F₂` にそろえる比較は、
    既存 `FiniteEtale.baseChange` と `TensorProduct.cancelBaseChange` の組合せを
    scratch で strict 検証した。literal inclusion の合成から scalar tower を供給し、
    合成体の有限性も既存 instance で得る。検証用 wrapper は本番に追加しない。
    次の最小 frontier は射の等式の native 接続：`E,G ≥ F₀` で定義した射が
    `L` 上で一致すれば、有限 `H ≥ E,G` 上で literal transition maps の像が一致する。
    一般の supplier は既存 `IsFinitelyPresentable.exists_eq_of_isColimit` と
    `CommRingCat.isFinitelyPresentable_under` であり、再実装しない。
    その後に有限 affine cover と overlap/cocycle を共通段で構成して qcqs に貼り合わせ、
    基本群の核・像を比較する。`0BTV` / `0BTX` と全章完了は未達成のままで、
    番号付き106未完・本文19未完を維持する。

14. **2026-10-03 — 射の等式を共通の有限中間体へ降ろす native 接続。**
    `RelativeFiniteFieldDescent` に
    `exists_finiteIntermediateField_tensorProduct_algHom_eq_of_finiteModel` を追加した。
    有限 `E,G ≥ F₀` 上の2射が `L` 上で一致するとき、実際の有限中間体
    `H ≥ E,G,F₀` と、literal inclusion tensor transition 後の射の一致を構成する。
    有限表示は始域 `B` のみを要求し、終域の有限表示・flatness・比較同型・
    colimit の存在を公開仮定に置かない。既存の tensor-colimit owner と
    mathlib の `IsFinitelyPresentable.exists_eq_of_isColimit` /
    `CommRingCat.isFinitelyPresentable_under` を使用し、compactness を再実装しない。
    transition の pure-tensor 式は literal inclusion tensor map と `rfl` で一致する。
    公開 endpoint の data-bearing context は最大13、private core と transition は
    最大10で、同じ対象の作用の shadowing・本文での再設置・制限値の増加はない。
    strict leaf は2209 jobs、最小 `FilteredColimit.All` は2212 jobsで、
    warning/error 0、source hash 不変。新 equality と既存 point/Hom/ISO の4公開宣言は
    kernel audit で標準3公理のみだった。canonical `CommAlgCat.FiniteEtale` への直接適用も
    strict 検証し、始域の有限表示は既存 `Algebra.Etale.finitePresentation` が供給した。
    reverse import closure は5 moduleで root 到達を確認し、唯一の direct consumer は
    最小 aggregate である。leaf/aggregate の local closure は6/9 module、ac・jv は0。
    次は有限 affine cover、二重交叉の射・同型、三重交叉の cocycle 等式を共通段へ降ろし、
    qcqs に貼り合わせる。有限被覆の選択と細分は既存の `finiteSubcover`、
    貼り合わせは `Scheme.Cover.glueMorphisms` / `hom_ext` / `Scheme.GlueData` を再利用する。
    有限部分被覆が `LocallyDirected` を保つとは仮定しない。一般の qcqs inverse limit と
    誘導される基本群の核・像の比較は未完で、`0BTV` / `0BTX` の status と
    番号付き106未完・本文19未完、全章完了の目標は維持する。

15. **2026-10-03 — affine な有限 étale スキームの有限中間体モデル。**
    `FiniteEtale.FiniteField.Model` の
    `AlgebraicGeometry.FiniteEtale.exists_finiteIntermediateField_affine_model` は、
    実際の `FiniteEtale (Spec (R ⊗[k] L))` から、有限中間体 `F`、実際の
    `FiniteEtale (Spec (R ⊗[k] F))`、literal coefficient inclusion による
    pullback と元の対象の category iso を構成する。既存の algebra モデルと
    `affineEquivalence` / `affineEquivalenceCompBaseChangeIso` の counit・fully faithful
    preimage を使用し、モデルや比較を仮定しない。係数作用は本文に一度だけ設置する。
    strict leaf は2981 jobs、1 newly built target、warning/error 0、source hash 不変。
    canonical 対象への直接適用と compiled kernel audit も通過し、標準3公理のみ。
    保守的な data-bearing instance 計数は最大12、closure に ac・jv はない。
    新しい `FiniteField.All` と親 facade への到達経路を保存した。ユーザーの停止指示により
    新 aggregate の build は未実行で、再開時の gate に残す。親 `FiniteEtale.All` は
    禁止対象の ac 5 module を含むので、この制限中に build しない。
    スキームの定数体拡大の具体的 inverse-limit diagram/cone/IsLimit と、affine transition・
    qcqs stage の supplier は作業用 scratch で strict 検証済みだが、本番に未統合である。
    次の未完部分は、この具体的極限を既存の scheme Hom 降下へ接続し、実際の overlap
    同型・cocycle を作ること。その後に global object gluing と基本群の核・像の比較が残る。
    `0BTV` / `0BTX` の status、番号付き106未完・本文19未完と全章完了目標は維持する。
    ユーザー指示で作業を一時停止し、詳細を作業用フォルダの `HANDOFF.md` に保存した。

16. **2026-10-04 — 任意標数の算術完全列 `0BTX`。**
    `GeometricFiber.ArithmeticAlgebraicClosure` の
    `AlgebraicGeometry.FiniteEtale.arithmetic_exactSequence_of_isAlgClosure` は、
    qcqs な `X/k` と連結な `X_L`（`L/k` は任意の代数閉包）から、実際の
    `π₁(X_L) → π₁(X) → Aut(SeparableClosure k/k)` の単射・全射・核と像の一致を証明する。
    幾何的群は canonical fiber functor の自己同型群であり、核として定義し直していない。
    `FiniteField.GlobalModel` は有限 affine cover、重なりの射・同型・cocycle を
    実際の共通有限中間体へ降ろし、qcqs な有限 étale 被覆のモデルと回収同型を構成した。
    分離閉包版はその降下から証明した。任意標数への接続では、Frobenius の具体的な
    分解、純非分離拡大に沿う局所モデル、実際の大域貼り合わせと回収同型を使い、
    `PureInseparableDescent.pullback_isEquivalence_of_purelyInseparable_constant_extension`
    （namespace `AlgebraicGeometry.FiniteEtale`）を供給した。
    元のスキームへの射と基点の比較も構成し、共役による差を保存して完全性を移した。
    最終 leaf、最小 `GeometricFiber.Arithmetic` / `FiniteField.All` は strict build 済み。
    有限体降下側203宣言と算術側37宣言の公理監査は標準3公理のみ。
    `AlgebraicClosure k` / `SeparableClosure k` を用いる実際の consumer も strict 検証済み。
    実行中の source hash 変更、`sorry`、独自公理、核心の追加仮定、制限値の引上げはない。
    対象50 module は全て root から到達可能で、local import closure 159に ac・jv はない。
    `0BTX` を implemented に変更した。一般の `0BTV`、`0BTW`、`0BQN` は未完のまま。
    台帳を再集計した現在の未完数は番号付き105、本文19であり、全章完了は未達成。

17. **2026-10-05 — 正規化・剰余体・基底変換の四項目を完成。**
    `0BQK` は `Normalization.UnramifiedNormalization` の
    `unramified_normalization_iff_etale_iff_finiteEtale` で、実際の相対正規化について
    不分岐・étale・有限 étale の三条件を同値にした。
    正規整域上の étale 代数の忠実な整域商を generic fibre の冪等元から構成し、
    不分岐代数の標準 étale 商表示と局所性から有限表示性も導く。Noetherian 性や
    有限表示性を追加仮定していない。正規化の優勢性は実際の一般点から証明した。
    `0BQL` は既存の `FiniteEtale.Integral` と
    `Purity.PuncturedSpectrumConnectedRestriction` を一般化した。
    有限 étale 被覆の整な開被覆から被約性を供給し、関数体・正規化との比較に
    残っていた局所 Noetherian 仮定を除去した。通常の `[IsFinite f] [Etale f]`
    と位相的連結性だけを渡す consumer も検証済み。
    `0BSP` は `StrictHenselian.SeparablyClosedFractionResidue` の
    `isAlgClosed_primeResidueField_of_isSepClosed_fractionRing` が供給する。
    monic な剰余多項式の持ち上げ、Gauss の補題、極大イデアル内の非零元による
    一次摂動で局所版を証明し、任意の非零素イデアルへ正準局所化で移した。
    `0BSS` は `Inertia.InvariantBaseChange` の `inertia_invariantBaseChange`
    （namespace `EtaleFundamentalGroups.Inertia`）が、実際の tensor 作用を構成して
    証明する。有限群・素イデアルという制限さえ不要な一般の ideal inertia 等式である。
    ValuedFieldTheory の既存の有限層検出と有限分岐群を再利用し、無限 Galois 拡大の
    剰余標数0で wild inertia が自明となる定理も追加した。これは `0BUA` の一部分であり、
    full tag の完成とは数えない。
    変更 leaf、全15の許可された直接利用先、`Normalization.All` / `Inertia.All` の
    strict build と主要宣言の標準3公理監査を通過した。利用先の間接 import 依存1件と
    不要になった Noetherian binder 1件も修正した。変更15 module は全て root 到達可能。
    `StrictHenselian.All` は ac 依存を検出して build を開始せず、leaf と実際の素点 consumer
    を検証した。root acceptance は実施していない。
    台帳の未完数は番号付き101、本文19。次は `0BQM` の実際の generic Galois map の
    全射性と、有限中間体の正規化が不分岐であることとその fixing subgroup が核を
    含むことの同値を構成する。その後に `fixedField(kernel)` と最大不分岐拡大を同定する。
    `0BSQ` の Hensel 持ち上げと `0BST` の固定部分代数の flat base change・局所 étale
    表示も未完であり、結論や比較を仮定として追加しない。

18. **2026-10-05 — 一般点の Galois 商と Hensel 性を完成し、ユーザー指示で一時停止。**
    `0BQM` は実際の絶対 Galois 群からの全射、有限被覆の generic pullback と
    核の作用の比較、有限部分体の fixing subgroup 条件を構成した。
    `Normalization.GenericExtensionFiber` は任意の整スキームと代数拡大について
    正規化の一般ファイバーを実際の `Spec L` と同定し、両射の一致も証明する。
    逆向きは dominant preimmersion の generic-stalk 同型から既存の source normalization
    同型・連結有限 étale 被覆の正規化定理へ戻し、比較を追加仮定していない。
    `Normalization.UnramifiedSubfield` は有限部分体の不分岐性と核の fixing 条件を同値にし、
    `fixedField(kernel)` が有限不分岐部分体の実際の和集合であることを元の元ごとに証明した。
    `GeometricFiber.GenericPointGaloisQuotient` はその Galois 性、基本群との位相群同型、
    元の写像と自己同型の制限との一致を供給する。独立レビューで full `0BQM` を確認した。
    `0BSQ` は monic 因子による次数帰納法と既存の Gauss の補題から Hensel の単純根を
    持ち上げ、剰余体の分離閉性も証明した。局所環が体の場合を含み、非零極大イデアルを
    仮定しない。`HenselianLocalRing` と `IsSepClosed` の既存クラスを使用する。
    `0BST` の準備として有限群の固定部分代数の flat base change 同型と包含の可換性、
    Hensel 局所環上の整拡大の有限閉ファイバーを切る一意な冪等元・実際の局所因子を構成した。
    `0BST` と外部 `0BSR` の étale 近傍への降下・固定環の射影比較は未完のままとする。
    変更 leaf、具体的 consumer、公理監査、許可された直接利用先、
    `Normalization.All` / `Inertia.All` / `GaloisCovers.All` が strict green。
    最終集約は Built 11 / Replayed 0、warning/error 0、local source 554の前後ハッシュ一致。
    変更21 module は root 到達可能、reverse closure は56。AC/JV を含む集約は build していない。
    台帳の未完数は番号付き99、本文19。全章完了ではない。
    ユーザーの「一度いいところでやめて」に従い、この検証済み区切りを保存して一時停止する。
    再開時は `0BSM`、`0BST`/`0BSR` と strict henselization・惰性群比較から継続する。

現在の実行方針: ユーザー指示で一時停止。再開時は対象 leaf の小さい strict build と必要な最小 aggregate を行う。
2026-10-03 はユーザー指示で ac・jv の直接・推移的 import を禁止する。
各 build の local import closure を事前に確認し、両ライブラリを含む root build は
この制限中は実行しない。それ以外のライブラリは再利用してよい。
以前の不実行指示は同日の明示的な build 指示で置き換えられた。
専用 heartbeat 計測は未実施。

### Completion scope: 58.13.1–6 (2026-10-07)

The active request is to complete58.13.1,58.13.2,58.13.4 and the remaining5-F/6-D integration checks.
On2026-10-08 the user paused further58.13.3 work; its already proved algebraic
results are retained, and its remaining geometry is deferred. Continue the shared
normalization, fixed-field, local-neighborhood and equivalence suppliers for1,2,4.
Each original statement keeps its own hypotheses and verification status.
Unrelated usage or demonstration examples remain excluded.

| Statement | Original completion target | Current verified state and next missing mathematical input |
| --- | --- | --- |
| 58.13.1 / [0BSW](https://stacks.math.columbia.edu/tag/0BSW) | The local fundamental-group diagram agrees with the decomposition/inertia diagram, with the specified normal-closure kernel. | The literal strict-stalk fraction image is the original inertia fixed field, and its absolute Galois restriction and actual scheme fundamental-group map have range the same I. originalInertia_normalLocal_exactSequence constructs the actual continuous surjection Gal(L/K) to pi1(Spec A), with kernel the closed normal closure of I (6.9s, standard axioms). The actual ordinary henselization is constructed from the residue-pointed etale colimit, with Henselianity, the literal residue-field isomorphism and the universal unique local lift (3.3s). Its injection into B_Q and L, fraction-field injection, coefficient equations and D-fixedness are proved. Existing strict normalization, fixed-field, restriction and DVR consumers are checked. The same actual FracH image now equals the original D fixed field (3.2s), via proved unit preservation in an integral henselian extension and the actual D fixing-group criterion (5.3s). The original K coefficient map, tower and ambient separable-closure structure pass3.3s. Fourteen named axiom queries use only standard axioms. The literal strict-stalk residue is now proved separable over the base residue, and its actual embedding image equals the separable part of the normalization residue (3.4/2.9s). This does not assume the entire normalization residue extension separable or algebraically closed. The ordinary absolute Galois restriction has the same original D as image (3.3s), and the actual FracH to Frac(strictH) map preserves both the original K coefficient map and the original L embedding (4.3s). Eleven named axiom queries are standard. The original maximal unramified M is now independently defined from the finite unramified subfields. Its equality with the actual generic-map kernel fixed field, Galois structure, topological isomorphism pi1(Spec A) with Gal(M/K), and the literal restriction equation are proved. The same original kernel and fixing subgroup equal the closed normal closure of I. The final quotient/kernel roots pass4.1/6.1s, and24 named queries use only standard axioms. The original normalization residue extension is now proved normal from finite Galois stages (5.9s). The original D action on its actual separable part is surjective with exactly the original I kernel (2.4s); the literal strict-stalk residue is identified with this same separable part (12s). Actual generic-to-residue points of finite etale algebras over the ordinary henselization are naturally D-equivariantly identified (8.4s), reusing the Henselian section-lifting theorem. Five exact producer closures and27 named queries3.21s use only standard axioms. Original mathematical endpoint verified: originalLocalGaloisDiagram_of_actualHenselizations gives the literal ordinary-henselization scheme-induced lower arrow, transported by the actual strict-residue and independent maximal-unramified-field comparisons. Both original vertical arrows are surjective with kernels original I and its closed normal closure. The same generic map from original D has exactly the original I kernel, and both actual scheme/residue squares commute. Nineteen supplier closures and20 queries7.37s pass; the combined original endpoint passes6.0s and five final named queries8.39s use only standard axioms. No Noetherian, DVR, nonzero-prime or whole-residue separability premise is added. Broad aggregate/all420 validation was stopped by the user; the original changed-leaf and necessary-consumer checks are complete. The allowed field/Q=0 case remains; no DVR or residue-separability premise is added |
| 58.13.2 / [0BTD](https://stacks.math.columbia.edu/tag/0BTD) | For an arbitrary normal integral scheme, identify three subgroups: the generic-point π₁ kernel, the closed normal subgroup generated by all normalization inertia groups, and the closed normal subgroup generated by all strict-henselization fraction-field Galois groups. | Original mathematical endpoint verified. genericAbsoluteGaloisHom_ker_eq_pointInertia_and_chosenStrictGalois states both equalities with the actual generic-point kernel: literal inertia at every point of the normalization, and literal Gal(Ksep/Frac(actual strict stalk)) restriction ranges for an arbitrary choice of one maximal normalization prime over each x. Actual chart equivariance, localization/contraction, profinite prime conjugacy and normal-closure independence supply the comparisons. No Noetherian hypothesis, supplied comparison or prescribed kernel is assumed. Point endpoint14s, selected strict endpoint4.5s, combined endpoint4.7s, and19 named original-conclusion/actual-consumer axiom queries8.88s pass with zero own diagnostics and standard axioms. Exact53-producer admission also includes necessary ordinary/local suppliers. Inertia.All and all420 configuration checks remain open |
| 58.13.3 / [0BTE](https://stacks.math.columbia.edu/tag/0BTE) | Formalize the original simultaneous-sign quotient example in characteristic different from2: its quadratic-monomial invariant ring, finite degree-two normalizing cover for n≥1, and ramification confined to the origin with codimension n; n≥2 gives the codimension-one counterexample. | Paused at the user request on2026-10-08. The concrete sign action, quadratic invariant-ring equality, finite polynomial extension, normality of that invariant ring, and identification of the original polynomial ring as its integral closure in its fraction field are proved for all n. For n>0, the actual sign action is faithful and the original fraction-field inclusion has degree2. Normal producers and named standard-axiom checks pass with zero diagnostics; sources are admitted. Actual Spec normalization identification and the exact ramification-locus/codimension calculation remain deferred. |
| 58.13.4 / [0BTF](https://stacks.math.columbia.edu/tag/0BTF) | Prove the original global/local/fiberwise nonramification equivalences for a general finite extension: conditions1–8 in general, with inertia-triviality condition9 added when the extension is Galois. | Existing0BQK gives(2) iff(3) iff(4), and the actual fiber rank comparison gives(2) implies(8) with degree exactly[L:K]. etale_genericNormalization_iff_trivial_point_residue_inertia now proves global finite-Galois(3) iff(9) with literal normalization points and residue actions (7.6s). Actual faithfully-flat pointed-stalk descent proves(2) implies(5) and pointwise(5) iff(6),(7); the ordinary specialization is checked on the constructed henselization without a separably-closed residue premise. A non-Noetherian finite-model/unramified-locus argument proves the ring local-to-global criterion for literal normalization, with standard-axiom checks. finiteEtale_normalization_of_stalk_unramified now closes the actual scheme implication(5) to(4) for arbitrary finite L/K, with no Noetherian or separability assumption (4.1s and standard axioms). Original mathematical endpoint verified: finiteEtale_normalization_of_fiber_etale_degree proves(8) to(4) for the actual scheme fibers and original lower bound degree >= [L:K] (7.1s). unramified_normalization_criteria_tfae gives all eight original conditions, and unramified_normalization_galois_criteria_tfae adds literal point/residue inertia only in the Galois case (5.7s). Orthogonal-idempotent lifting in the actual strict henselian base change forces generic splitting from the degree bound and supplies etale descent. Ten exact normal producers and13 named queries3.87s are clean with standard axioms. Conditions1–8 retain arbitrary finite L/K without Noetherian or separability hypotheses. Normalization.All and StrictHenselian.All now pass with their exact source closures after the necessary existing-owner diagnostic repairs. Broader Inertia/all420 configuration acceptance remains open |
| 58.13.5 / [0BUA](https://stacks.math.columbia.edu/tag/0BUA) | The two exact sequences and every wild/tame conclusion for the original DVR and arbitrary possibly infinite Galois extension. | Fixed5-A–5-E and the complete original5-F mathematical endpoint are proved and admitted. Necessary remaining aggregate/new-settings coding verification is in progress; whole-tag completion is not yet claimed. |
| 58.13.6 / [0BUB](https://stacks.math.columbia.edu/tag/0BUB) | The original separable-closure specialization, literal residue algebraic closure, and equivariant identification with the full positive residue-invertible root limit. |6-A/6-B/6-C are proved.6-D now supplies `normalizationDVR_absolute_ramification`: all original conclusions, the SAME θ/P/quotient, and the full separable-root target. All eight producers and nine named axiom queries pass with zero diagnostics; sources are locally admitted. Required subtree/global integration checks remain open. In characteristic zero the index includes every positive integer. |

### Fixed remaining work: 58.13.5–6 (2026-10-07)

After the active58.13.1/2/4 work and required5/6 verification, with58.13.3 paused, continue EFG at the general qcqs inverse-limit theorem58.14.1, then58.14.2.58.14.3 is already implemented; the following planned geometric goals are58.15.1–2. M2 of EtaleCohomology remains paused, following the user's2026-10-08 instruction.

For the5/6 portion, use the fixed **5-A–5-F / 6-A–6-D** identifiers in subsequent progress reports. A step is complete
only when its stated conclusion is assembled from the original inputs and its
actual source passes the required checks. A private helper's successful kernel
check is partial progress. Both whole tags remain unfinished. Status below is
recorded in each dated row; M2 remains paused. The mathematical completions and accepted kernel results below retain their original configuration evidence. On 2026-10-07 the AGENTS/Lake settings from branch commit `8f1f1e90` were adopted; verification of all420 previously added/modified Lean files under those settings is pending and must not be inferred from earlier passes.

For [0BUA](https://stacks.math.columbia.edu/tag/0BUA), use the original DVR A,
its fraction field K, arbitrary possibly infinite Galois L/K, literal
normalization B, and chosen maximal prime Q. No residue separability, supplied
wild comparison, canonical character, or limit comparison may be added.
In particular, the general wild kernel is **not** replaced by the subgroup
acting trivially on B/Q²; the relevant equivalence needs extra residue
separability in [09EE](https://stacks.math.columbia.edu/tag/09EE).

| Fixed ID | Mathematical completion condition | Current state and remaining input | Depends on |
| --- | --- | --- | --- |
| **5-A** | The actual residue map gives the exact sequence I → D → Aut(κQ/κA), with surjectivity and kernel I. | **Completed at its original-input theorem and required individual checks (2026-10-07).** `EtaleFundamentalGroups.Inertia.normalizationResidueDVR_exact` (module `Inertia.NormalizationResidueDVR`) uses the actual DVR, arbitrary Galois extension and literal normalization maximal prime; contraction to the base maximal ideal and the canonical quotient/residue-field coefficient comparison are proved. New-settings root2.3s and its exact60-source closure now pass; historical normal root4.0s, standard-axiom queries and unchanged actual direct consumer 2.5s pass; exact source-scope review is at most16. Inertia.All remains unverified: its900-second aggregate window ended while rebuilding unchanged dependencies, with zero diagnostics. Shared Ramification.All registration is retained with a separate hold on15 pre-existing letI warnings in three unchanged owners. The unchanged 60-source proof closure still matches its accepted source39 window. These broad aggregate holds belong to5-F; this does not complete5-B–5-F or either whole tag. | Existing normalization invariance and Krull continuity. |
| **5-B** | Construct actual finite-stage wild groups, p-primary/trivial-characteristic-zero laws, and nλ = card(Iλ/Pλ), with the original ramification arithmetic. | **Completed at the original-input conclusions and required individual/integration checks under the new settings (2026-10-07); exact source accepted, with publication identified by the increment receipt.** The SAME originalFiniteFieldWildSubgroup is residue-p-primary (including IsPGroup), trivial in base-residue characteristic zero, and the actual tame degree equals Nat.card(I/P). The explicit originalFiniteNormalizationTameOrder_mul_wildOrder_eq_ramificationIdx_mul_finInsepDegree supplies n*w=e*f_insep for the literal maximal quotient fields, using the existing stored Field/Algebra structures and no separability or comparison premise. All13 mathematical producers, refreshed actual5-C/6-A consumers, and10 named production axiom queries pass with zero own-closure warnings; the final arithmetic is2.8s and the final query4.34s. Native source-scope review is at most16. The combined source-bound proof closure is242 maintained/private source records. No B-only canonical aggregate exists: HilbertRamification.All and Inertia.All are broader shared aggregates; the attempted new-settings Hilbert.All window has699 pre-existing-source lint warnings and no typing error, retained for5-F/all420 revalidation. This does not complete5-D or either whole tag. | Existing Hilbert ramification and actual localization equivalence; verified original finite-inertia equivalence. |
| **5-C** | Construct the eλ/nλ-normalized finite canonical character: onto the full μ_nλ, kernel Pλ, equivariant, and independent of uniformizer and stage choices. | **Completed mathematically and with the required individual gates (2026-10-07); new-settings actual endpoint/consumer refresh also passes.** The original finite field-inertia character is onto the full root group, with the independently defined principal-unit wild kernel, the SAME original D/residue equivariance, and the checked arbitrary-uniformizer formula. `actualFiniteTameCoordinate_tower` proves the SAME ambient coordinate obeys the actual nF/nE power transition from the original DVR/Galois/normalization data. `actualFiniteTameCoordinate_eq_of_tameOrder_eq` uses the actual finite Galois compositum E⊔F to prove degree-representative independence. No comparison, tower index, or existence premise is supplied. Final endpoint kernel 2.7s, all five named production axiom queries (standard axioms only), required actual consumers, independent scope reviews at most16, and HilbertRamification.All 2.4s pass with zero warnings and zero source directives. Four unused private predecessor-route modules are excluded from promotion. New-settings SAME-coordinate endpoint2.8s and original D-equivariance2.1s pass on the final5-B owner closure. Broader Inertia/normalization aggregate holds remain for5-F; this does not complete5-D–5-F or either whole tag. | 5-B. |
| **5-D** | Actual finite D/I/P restrictions are surjective; residue inclusions and canonical characters commute with the nλ/nλ′ power maps, including common-upper-stage compatibility. | **Completed at the actual original-input conclusions and required individual gates under the new settings (2026-10-07).** The SAME original infinite inertia and decomposition groups surject onto intrinsic inertia/decomposition of every literal finite normalization. The actual finite I/D restrictions are surjective, compose through towers, and satisfy the literal coefficient-inclusion squares. The SAME independent principal-unit wild subgroup maps onto the target wild subgroup under actual inertia restriction in all residue characteristics; the induced actual P restriction is onto, using the proved p-group/prime-to-p-index laws and Sylow image theorem. `actualFiniteInertiaTowerRestriction_tameValue` and its common-upper theorem connect these SAME restrictions to the existing canonical character and actual nF/nE power maps. No residue separability, field/intrinsic comparison, image, or surjectivity premise is assumed. Finite I roots2.7/2.2s, finite D roots2.0/2.2s, P image/restriction2.3/2.2s, and final canonical square2.2s pass with zero own-closure warnings. A common exact-source query window validates31 producer sources and13 named actual endpoint queries with only standard axioms; necessary real consumers and independent direct-context reviews (at most16) pass. Both existing canonical facades register the new leaves; broader unchanged aggregate holds remain assigned to5-F/all420. Sources are locally admitted, preserved in Library, and published on the dot development branch. This completes5-D, not5-E/5-F or either whole tag. | 5-B, 5-C; existing inertia-image and finite group theorems. |
| **5-E** | Construct directed S with primitive n-th roots, continuous surjective canonical θ, kernel P, D-equivariance, D-normality of P, pro-p/characteristic-zero triviality, and I/P isomorphic to the root limit. | **Completed and exact-source admitted under the new settings (2026-10-07).** The literal actual finite-degree range is nonempty and divisibility-directed, and every degree has a primitive root in the literal normalization quotient. `actualTameCharacter` is built from the SAME normalized finite coordinates and existing restricted roots system, with proved choice independence, original Krull/subgroup continuity and compactness-based surjectivity. Its kernel is the independently defined original wild subgroup. The SAME original decomposition/residue action gives `actualTameCharacter_conjugate`; that P is normal in D, compact and pro-p in positive base-residue characteristic, and trivial in characteristic zero. `actualTameQuotientEquiv` identifies the literal original I/P continuously with the SAME roots limit and has the actual representative formula. No core comparison, continuity, surjectivity, kernel, normality or quotient premise is added. A common normal gate covers103 targets with zero warnings; final equivariance2.0s, D-normality2.0s and quotient2.1s pass. Seventeen named original-input axiom queries use only propext, Classical.choice and Quot.sound. Independent direct-scope audits are at most16. Receipt `admission-5e-original-tame-character-20261007-01` admits101 producer rows plus four import-only canonical registrations. Broader existing aggregate and all420 revalidation holds remain assigned to5-F; neither whole tag is complete. | 5-A–5-D. |
| **5-F** | One original-scope endpoint covers every conclusion of 58.13.5 and passes the necessary kernel, source, existing-consumer and minimal aggregate gates. | **Original all-conclusion endpoint proved and exact-source admitted; broader coding verification remains open (2026-10-07).** `normalizationDVR_ramification` in `Inertia.NormalizationDVRRamification` proves all18 literal output clauses from the original DVR, fraction field, arbitrary possibly infinite Galois extension and maximal normalization prime. Its data owners actually construct the existing fields, degree set, maps, subgroups and topologies; the root target is intrinsically the SAME actual-degree limit. The full generated output constructor and concrete factories satisfy the independent16-target bound. The pro-p clause explicitly includes compactness, Hausdorffness, total disconnectedness and topological-group structure, together with the finite-p quotient basis. The normal endpoint takes2.2s; all new producers and required existing direct consumers are warning-free. Seven named axiom queries, including the whole theorem, use only standard axioms. Receipt `admission-5f-original-dvr-endpoint-20261007-01` accepts9 producer sources and one import-only registration. On2026-10-08 both original5/6 endpoints were refreshed under the current native inertia interfaces with exact344/376-source closures and standard-axiom queries. The required `ProCGroups.InverseSystems.All` aggregate now passes1.5s after two diagnosed documentation/source-option repairs and correction of one misplaced import; its two modified roots pass1.3/1.8s. The ordinary cached endpoint checks reuse their unchanged successful closures. Inertia.All, the dense shared-owner repairs and all420 new-settings validation remain unresolved; this does not claim whole-tag coding completion. No new demonstration fixture is used. | 5-A–5-E. |

For [0BUB](https://stacks.math.columbia.edu/tag/0BUB), specialize to the prescribed
separable closure Ksep and its literal normalization quotient κbar. The full
index is positive integers invertible in κ, represented by `InvertibleExponent`;
in residue characteristic zero this includes **all positive integers**.
`Nat.Coprime n 0` must not be used as that index.

| Fixed ID | Mathematical completion condition | Current state and remaining input | Depends on |
| --- | --- | --- | --- |
| **6-A** | The literal κbar is an algebraic closure of κ; actual restriction identifies its automorphism group with Gal(κsep/κ), giving the original residue exact sequence. | **Original-input endpoint verified (2026-10-07).** `normalizationAbsoluteResidue_isAlgClosure` proves the literal normalization quotient is an algebraic closure of the literal base residue field. `normalizationAbsoluteResidue_exact` postcomposes the same original D-map with the actual separable-part restriction isomorphism and proves its kernel remains the same I. All seven exact source roots and the actual final application pass; the five new producers take3.6/4.4/3.0/3.0/2.5s, and named production axiom queries use only standard axioms. Exact independent scope review is at most16. Inertia.All is registration-only with the earlier unchanged-dependency aggregate hold retained; no new demonstration example or whole-tag completion is claimed. | 5-A and existing 0BSP. |
| **6-B** | For every invertible positive d, construct an actual finite Galois radical stage and prove d divides its actual tame degree nλ, not merely its ramification index. | **Actual normalization divisibility verified (2026-10-07).** Every positive residue-invertible d is realized by an original finite Galois radical stage and divides that stage's actual intrinsic normalization tame order nλ. The actual wild prime-power law discharges cancellation; no wild or degree comparison is assumed. The original-input actualFiniteTameDegreeSet_cofinal is proved for the literal range of these same orders, including all positive integers in characteristic zero. Field-Galois presentation compatibility remains in5-D. | 5-B; actual finite-stage suppliers. |
| **6-C** | The actual image S is cofinal in the full index; κbar/κsep root comparisons preserve power maps and the D residue action, giving the actual equivariant limit isomorphism. | **Complete.** `actualTameRootsSeparableEquiv` identifies the SAME actual tame roots group with the literal full separable-root limit. Concrete coefficient/power squares, actual residue-action compatibility and both directions of D equivariance are proved. Twenty source producers pass the ordinary kernel with zero warnings; seven named declarations use only standard axioms. Sources and two import registrations are locally admitted; whole-tag and aggregate completion are not asserted. | 6-A, 6-B; 5-C, 5-D. |
| **6-D** | Transport the same θ and P to the full κsep-root limit, preserve exactness, equivariance, normality, pro-p/zero-characteristic laws and quotient isomorphism; validate the complete original 58.13.6 endpoint. | **Original endpoint verified; integration pending.** `normalizationDVR_absolute_ramification` proves the literal residue algebraic closure and separable closure, both exact sequences, SAME P with full profinite/pro-p and characteristic-zero laws, SAME continuous surjective equivariant character and SAME quotient isomorphism. Eight normal producers have zero diagnostics; nine named declarations use only standard axioms; all generated constructors and direct interfaces pass the16-target audit. Sources are locally admitted. Inertia.All and the420-source configuration validation remain open. | 5-E, 5-F; 6-A–6-C. |

Reports must state **fixed ID / newly verified actual conclusion / remaining
input or exact error / next proof task**. Counts of files, helpers or lines do
not mark these steps complete. Preserve zero source `set_option`, explicit
inputs, canonical type/instance consistency and unchanged default resources; the user removed the numerical data-target cap on2026-10-08, so earlier counts below are historical reviews and no longer implementation gates;
reuse existing owners and validate required real consumers without new examples.

### Anabelian geometry priority (2026-10-03)

[AnabelianGeometry/PLAN.md](../AnabelianGeometry/PLAN.md) §4.1–4.3 と A4/A5/A7/A9
を照合した。初期対象は標数0の有限生成体上の双曲的曲線であり、算術完全列の A5
は解析化・GAGA・RET の A1–A4 と独立に進めてよい。全章の完了条件は維持し、
番号順より次の成果とその最小依存を先行する。

| 優先順 | Chapter 58 の対象 | Anabelian 計画への出口と必要な構成 |
|---|---|---|
| 基盤 | §§58.3–58.6、特に `0BN5`–`0BTS`, `0BND`, `0BNE` | A5 の基点変更・共役・絶対 Galois 群。既存の canonical fiber functor / 有限連続作用 API を使用。`0BND`, `0BNE` は今回 strict build と公理監査済み。 |
| 1 | [§58.14.3 / `0BTX`](https://stacks.math.columbia.edu/tag/0BTX) と必要な [§58.14.1 / `0BTV`](https://stacks.math.columbia.edu/tag/0BTV) | A5: `1 → π₁(U_k̄) → π₁(U) → G_k → 1` は任意標数で実装・検証済み（point 16）。実際の有限被覆降下、単射・全射・正規像・核の一致を供給した。外作用への接続は後続の anabelian 側で扱う。 |
| 2 | §§58.11–58.13: `0BQK`, `0BQL`, `0BQM`, `0BSM`, `0BSW`, `0BTD`, [`0BUA`](https://stacks.math.columbia.edu/tag/0BUA), `0BUB` と必要な §58.12 | §4.3/A7: 境界の分解群・惰性群。正規化と関数体の対応、有限段の ideal inertia / strict henselian 局所群 / 大域固定群の比較を構成し、互換性を保って逆極限へ進む。§58.10 は必要な分だけ供給。 |
| 3 | §58.31: `0EYF`, [`0EYG`](https://stacks.math.columbia.edu/tag/0EYG) とその必要依存 | §4.1/4.3、A4/A7: cusp inertia、Kummer 被覆、円分作用。正則境界上の tame 被覆の標準局所形と pro-ℓ 惰性群 / `Z_ℓ(1)` の比較。ℓ は剰余標数と異なる。RET との境界比較は Chapter 58 外にも依存。 |
| 4 | [§58.9.3 / `0A49`](https://stacks.math.columbia.edu/tag/0A49) と必要な `0A48`, `0BTV` | A4: 複素数体から一般の代数閉体への比較。固有曲線の代数閉体拡大不変性を供給。開曲線では固有版だけでは足りず、境界の tame 比較を併せて扱う。 |
| 5 | §§58.15–58.16、§58.30、特に [`0C0R`](https://stacks.math.columbia.edu/tag/0C0R) | A9: 良い還元・有限体・特殊化。族の homotopy 完全列と特殊化、剰余標数に素な商の同型条件を保存。 |

`0BTV` の affine な対象降下は、代数的な定数体拡大について上記の
`exists_finiteIntermediateField_model` により完成した。有限係数体の diagram /
colimit は point 10、native な `R ⊗[k] F` の diagram / colimit と一般の射降下は
point 11、固定 `R`-モデルの native 射・同型接続は point 12 で完成した。
先に選んだ有限 `F₀` 上のモデルについても、有限 `E ≥ F₀` 上の射・同型と
literal 往復互換性は point 13 で完成した。共通合成体へモデルを移す際は既存の
canonical finite-étale base change と tensor cancellation を使う。
射の等式を共通の実際の有限中間体へ移す native 接続も point 14 で完成した。
affine なスキームの対象モデルと literal pullback の回収同型は point 15 で完成した。
有限 affine cover とその overlap/cocycle を共通段へ降ろす構成、qcqs の貼り合わせ、
実際の scheme base change と fiber functor への接続は point 16 で完成した。
純非分離な定数体拡大に沿う有限 étale category の同値も構成し、`0BTX` は
一般標数で完成した。一般の逆極限に対する `0BTV` と一般の `0BTW`/`0BQN` は
全章完了目標に残る。次の anabelian 優先対象は上表の分解群・惰性群である。

重複回避のために確認した再利用先:

| 既存 owner | この frontier で使う内容 |
|---|---|
| `SchemeTheory.FiniteEtale.Algebra.IntegralFiniteModel` | `Algebra.FiniteEtale.exists_finite_subalgebra_model`。有限 étale 性を保つ実際の finite integral subalgebra モデル。 |
| `ValuedFieldTheory.Valuation.Completion.FiniteSubfieldTensor` | `ValuationTheory.Completion.exists_finiteSubfield_tensor_lift`。tensor の実際の係数を有限中間体へ持ち上げる。 |
| `EtaleFundamentalGroups.GenericTensor.FilteredColimit.AlgEquivDescent` | 一般の射・同型・逆写像の等式の降下 owner。実際の有限中間体への native 接続は point 12–13 で検証済み。 |
| mathlib `CommAlgCat.FiniteEtale` | 有限 étale 代数の canonical category と base change。独自のモデル category は作らない。 |

ac に既存の有限表示 scheme / 射 / 同型の降下があることも確認済み。
それを別名で複製せず、今日の import 禁止中は他の上記 owner と mathlib を使う。
新規定理は一般の有限表示降下の再実装ではなく、有限 étale モデルの基礎環を
実際の有限中間体の tensor に拡張する接続である。

§§58.19–58.29 の高次元 purity・形式幾何と §58.32 は、上記の最小依存を除き
後続とする。これはユーザーの優先指示に基づく順序変更であり、数学的に不要と
判定したものではない。ac・jvの実装作業は別担当に任せる。

## 3. Numbered Chapter 58 tag ledger


Source:

- Chapter: [Fundamental Groups of Schemes, `0BQ6`](https://stacks.math.columbia.edu/tag/0BQ6)
- Stacks revision: `ed88ff78`
- PDF compile date: 2026-07-14
- Extracted: 2026-07-29

The official chapter page contains 32 section tags (58.1–58.32) and 141
numbered entries below.  This ledger tracks the 141 entries.  A section is
complete only when every entry in it has a terminal status.

This file alone is not the full corpus: non-environment body claims (including
58.7 and `0BN1`) and the chapter's 284 direct external references are tracked
separately as required by `GOAL.md`.

Statuses:

- `unmapped`: not yet compared with Lean.
- `planned`: no existing theorem found; implementation frontier identified.
- `implemented`: proved in `EtaleFundamentalGroups`.
- `covered`: directly supplied by an existing public theorem; no duplicate
  wrapper is created.
- `non-propositional`: no independent Lean declaration is appropriate.
- `blocked`: a concrete missing source-producing dependency is recorded.

| Number | Tag | Kind | Title | Status | Lean owner / evidence |
|---|---|---|---|---|---|
| 58.2.1 | [04JJ](https://stacks.math.columbia.edu/tag/04JJ) | Definition | Discrete continuous `G`-sets | covered | `Mathlib.CategoryTheory.Action.Continuous.DiscreteContAction`; equivariant maps are the inherited `Action` morphisms. |
| 58.2.2 | [03QR](https://stacks.math.columbia.edu/tag/03QR) | Lemma | Étale schemes over a field are equivalent to discrete continuous absolute-Galois sets | implemented | `AlgebraicGeometry.Scheme.Etale.equivDiscreteContAction` is the opaque public equivalence with forward functor `geometricFiber`; `geometricFiberIsEquivalence` exposes the corresponding canonical typeclass fact. All orbitwise construction helpers are private. `EtaleFundamentalGroups.SchemesEtaleOverPoint.Equivalence` and the root facade are verified by strict `--wfail` builds. |
| 58.2.3 | [03QS](https://stacks.math.columbia.edu/tag/03QS) | Remark | Étale covers correspond to jointly surjective equivariant families | implemented | `AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff_geometricFiber_jointlySurjective` identifies small-étale covering families with jointly surjective geometric-fiber maps. These maps are morphisms in the continuous-action category and hence equivariant; no wrapper restatement is needed. `EtaleFundamentalGroups.SchemesEtaleOverPoint.CoveringFamilies` is verified by strict `--wfail` build. |
| 58.3.0.1 | [0BS7](https://stacks.math.columbia.edu/tag/0BS7) | Equation | Canonical map from `Aut(F)` to the product of the automorphism groups of all fibers | covered | `CategoryTheory.PreGaloisCategory.autEmbedding`; injectivity is `autEmbedding_injective`. |
| 58.3.1 | [0BMR](https://stacks.math.columbia.edu/tag/0BMR) | Lemma | `Aut(F)` is a closed subgroup of the product and is profinite when all fibers are finite | covered | `autEmbedding_range_isClosed`, `autEmbedding_isClosedEmbedding`, and the `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`, `IsTopologicalGroup` instances in `Mathlib.CategoryTheory.Galois.Topology`. |
| 58.3.2 | [0BMS](https://stacks.math.columbia.edu/tag/0BMS) | Example | Forgetful functor from finite continuous `G`-sets to finite sets | covered | The inherited forgetful functor `CategoryTheory.forget₂ (ContAction FintypeCat G) FintypeCat`; no second functor is introduced. |
| 58.3.2.1 | [0BMT](https://stacks.math.columbia.edu/tag/0BMT) | Equation | The finite continuous-action forgetful functor | non-propositional | Displayed notation for 58.3.2; the functor is the existing `forget₂`. |
| 58.3.3 | [0BMU](https://stacks.math.columbia.edu/tag/0BMU) | Lemma | Automorphisms of the finite-action forgetful functor are the profinite completion of `G` | implemented | `FiniteContinuousAction.profiniteCompletionEquivAutForget` is the canonical topological group equivalence, with a simp theorem identifying the completion map with the canonical action on every finite continuous `G`-set. `EtaleFundamentalGroups.GaloisCategories.ProfiniteCompletion` is verified by strict `--wfail` build. |
| 58.3.4 | [0BMV](https://stacks.math.columbia.edu/tag/0BMV) | Lemma | Every exact finite-set-valued functor on finite continuous `G`-sets is isomorphic to the forgetful functor | implemented | `FiniteContinuousAction.nonempty_iso_forget_of_exact` constructs the natural isomorphism from preservation of finite limits and finite colimits alone. Its proof uses coherent points on regular finite quotients, right-action torsors, finite coproduct covers, and pullback descent. `EtaleFundamentalGroups.GaloisCategories.FiberFunctorUniqueness` is verified by strict `--wfail` build. |
| 58.3.5 | [0BMW](https://stacks.math.columbia.edu/tag/0BMW) | Example | A finite-valued functor factors through finite continuous `Aut(F)`-sets | covered | `CategoryTheory.PreGaloisCategory.functorToContAction`; continuity is supplied by `continuousSMul_aut_fiber`. |
| 58.3.5.1 | [0BMX](https://stacks.math.columbia.edu/tag/0BMX) | Equation | Canonical functor to finite continuous `Aut(F)`-sets | covered | `CategoryTheory.PreGaloisCategory.functorToContAction`. |
| 58.3.6 | [0BMY](https://stacks.math.columbia.edu/tag/0BMY) | Definition | Galois category and fiber functor | covered | `CategoryTheory.PreGaloisCategory`, `FiberFunctor`, and `GaloisCategory`; the axioms are split across the existing canonical classes. |
| 58.3.7 | [0BN0](https://stacks.math.columbia.edu/tag/0BN0) | Lemma | Basic consequences of the Galois-category axioms | covered | `FiberFunctor` faithfulness and finite-limit/colimit preservation together with `initial_iff_fiber_empty`, `epi_of_nonempty_of_isConnected`, `surjective_on_fiber_of_epi`, `evaluation_injective_of_isConnected`, and the connected-component API in `Mathlib.CategoryTheory.Galois.Basic`/`Decomposition`. |
| 58.3.8 | [0BN2](https://stacks.math.columbia.edu/tag/0BN2) | Lemma | Every connected object is dominated by a Galois object | covered | `CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_connected`. |
| 58.3.9 | [0BN3](https://stacks.math.columbia.edu/tag/0BN3) | Lemma | `Aut(F)` acts transitively on the fiber of every connected object | covered | `CategoryTheory.PreGaloisCategory.FiberFunctor.isPretransitive_of_isConnected`. |
| 58.3.10 | [0BN4](https://stacks.math.columbia.edu/tag/0BN4) | Proposition | A Galois category is equivalent to finite continuous `Aut(F)`-sets | covered | `CategoryTheory.PreGaloisCategory.functorToContAction` has `IsEquivalence`; mathlib marks the instance itself `@[stacks 0BN4]`. |
| 58.3.11 | [0BN5](https://stacks.math.columbia.edu/tag/0BN5) | Lemma | Exact functors correspond to continuous homomorphisms, up to inner conjugacy | implemented | `nonempty_iso_comp_of_exact`, `autHomOfCompIso_eq_conj`, `functorOfContinuousHom`, `comparisonIsoOfContinuousHom`, and `autHomOfCompIso_comparisonIsoOfContinuousHom` implement the four directions without wrapper hypotheses; all targets pass strict `--wfail`, the proof-escape scan, and the standard-axiom audit. |
| 58.4.0.1 | [0BTR](https://stacks.math.columbia.edu/tag/0BTR) | Equation | Diagram relating exact functors and restriction along continuous group homomorphisms | non-propositional | Implemented directly as `CategoryTheory.PreGaloisCategory.functorToContActionCompIso`; strict `--wfail` build and standard-axiom audit pass. |
| 58.4.1 | [0BN6](https://stacks.math.columbia.edu/tag/0BN6) | Lemma | Surjectivity of the group map, full faithfulness, and preservation of connected objects | implemented | `autHomOfCompIso_surjective_tfae` states the five Stacks conditions directly as `List.TFAE`.  Its converse constructs the finite transitive coset action from a proper open subgroup using `Finite.exists_equiv_fin`, `ULift`, and `Equiv.mulAction`; it does not assume the counterexample action.  The target passes strict `--wfail`, the proof-escape scan, and the standard-axiom audit. |
| 58.4.2 | [0BS8](https://stacks.math.columbia.edu/tag/0BS8) | Lemma | Trivial composite group map iff the composite functor has trivial finite objects | implemented | `autHomOfCompIso_comp_eq_one_iff` states triviality as equality of the composite continuous homomorphism with `1`, and states the categorical condition inline as an isomorphism with a finite coproduct of terminal objects.  Empty coproducts are included.  No object predicate, condition wrapper, or preservation hypothesis is added; the target passes strict `--wfail`, the proof-escape scan, and the standard-axiom audit. |
| 58.4.3 | [0BS9](https://stacks.math.columbia.edu/tag/0BS9) | Lemma | Exactness of profinite groups characterized by essential images of exact functors | implemented | `autHomOfCompIso_exact_sequence_tfae` states the three official conditions directly as `List.TFAE`: surjectivity/trivial composite/closed normal closure, `H.essImage`, and epimorphic covers.  It uses ProCGroups' existing `Subgroup.closedNormalClosure`, mathlib's `Functor.essImage`, and direct `Epi` hypotheses.  The two reusable source results characterize the essential image of restriction along a surjective continuous homomorphism and detect a closed normal closure by finite continuous actions.  No exact-sequence container, condition predicate, replacement closure, or extra exactness hypothesis is introduced; strict target and root builds, the proof-escape scan, and the standard-axiom audit pass. |
| 58.4.4 | [0BN7](https://stacks.math.columbia.edu/tag/0BN7) | Lemma | Injectivity of the group map characterized by epi/mono spans after restriction | implemented | `autHomOfCompIso_injective_iff_exists_epi_mono_span` states the official equivalence directly for connected target objects.  Its reusable source theorem `ContAction.injective_iff_exists_epi_mono_span` constructs and detects the required finite continuous-action span using canonical quotient actions, `Epi`, `Mono`, and ProCGroups' open-normal-subgroup API.  No span wrapper, replacement injectivity predicate, or preservation/exactness assumption is added.  Both strict targets, the 26-source-plus-facade build, the proof-escape scan, and the standard-axiom audit pass. |
| 58.4.5 | [0BTS](https://stacks.math.columbia.edu/tag/0BTS) | Lemma | Normality of the image characterized by connected objects becoming trivial | implemented | `autHomOfCompIso_range_normal_iff_terminal_decomposition` states the official two conditions directly: normality of the existing monoid-hom range, and finite-terminal-coproduct decomposition for connected objects that acquire a point.  The reusable source theorem `ContAction.range_normal_iff_fixed_point_implies_trivial` proves the finite-action criterion using mathlib fixed points, ProCGroups' closed-range/open-subgroup separation, and the canonical finite left-coset action.  No normal-image predicate, action wrapper, or preservation hypothesis is introduced; both strict targets, the 28-source-plus-facade build, the proof-escape scan, and the standard-axiom audit pass. |
| 58.5.1 | [0BN8](https://stacks.math.columbia.edu/tag/0BN8) | Example | Finite étale schemes over a separably closed field are finite sets | covered | Pi1 `AlgebraicGeometry.FiniteEtale.equivFintypeCat` is exactly the scheme-level equivalence `FiniteEtale (Spec (.of Ω)) ≌ FintypeCat` under `[IsSepClosed Ω]`.  Its source is canonical: `AlgebraicGeometry.IsFiniteEtale.eq_inf` identifies Pi1's property with `(@IsFinite ⊓ @Etale : MorphismProperty Scheme)`, and the corresponding canonical-category endpoint type-checks by this single rewrite.  Mathlib also supplies the affine-algebra version `CommAlgCat.FiniteEtale.equivOfIsSepClosed`; recomposing it into another public equivalence would be a duplicate wrapper. |
| 58.5.2 | [0BN9](https://stacks.math.columbia.edu/tag/0BN9) | Lemma | Finite limits, finite colimits, and exact base change for finite étale schemes | covered | Pi1 `AlgebraicGeometry.FiniteEtale` supplies terminal objects, pullbacks, finite colimits, and finite-limit/finite-colimit preservation for pullback. New public statements must use the canonical property `@IsFinite ⊓ @Etale`. |
| 58.5.3 | [0BNA](https://stacks.math.columbia.edu/tag/0BNA) | Remark | Forgetful functors preserve finite colimits and the appropriate finite limits | implemented | `EtaleFundamentalGroups.FiniteEtale.ForgetExactness` proves the finite-limit half on the canonical functors. `ForgetFiniteCoproducts` proves finite-coproduct preservation, and `ForgetFiniteCoequalizers` constructs fpqc-local split finite-copower models, verifies their coequalizers on cover members and pairwise overlaps, descends them with the exact Tag `0BMN` theorem, and publishes `forgetCompOverForgetPreservesCoequalizers`, `forgetPreservesCoequalizers`, `forgetPreservesFiniteColimits`, and `forgetCompOverForgetPreservesFiniteColimits`. The strict target build passes 2964/2964 jobs and the root facade passes 3459/3459; all four public instances use only `propext`, `Classical.choice`, and `Quot.sound`, and the proof-escape scan has zero matches. |
| 58.5.4 | [0BL7](https://stacks.math.columbia.edu/tag/0BL7) | Lemma | The relative internal Hom of finite etale schemes is finite etale and base-change compatible | implemented | The finite-free algebraic construction and its finite etaleness/base-change comparison have previous strict-build evidence. On 2026-09-23, source implementations were added in `SchemeTheory.WeilRestriction.{Sheaf,BaseChange}` and `SchemeTheory.Affine.WeilRestriction.{Global,GlobalFiniteEtale,GlobalBaseChange,Local}`: all-test-scheme representation by an explicit spectrum, finite etale packaging, arbitrary-scheme base-change representation, affine tensor-product comparison, and actual principal-neighborhood representers for finite etale A/B without global freeness. Further source additions construct principal and directed covers, canonical cartesian transitions, finite etale gluing, a relative hypercover, the glued universal section, and the generic sheaf-gluing theorem `SchemeTheory.WeilRestriction.gluedLocalRepresentable`. `SchemeTheory.Affine.WeilRestriction.finiteEtaleInternalHomGluedRepresentable` and `finiteEtaleInternalHomGluedBaseChangeRepresentable` apply this to finite etale A/B without global freeness. The new `SchemeTheory.WeilRestriction.Affine` and `FiniteEtale` modules transport to arbitrary affine bases and glue on the directed affine cover of any base. The full statement, including arbitrary base change, is source-implemented in `AlgebraicGeometry.FiniteEtale.exists_internalHom` (`EtaleFundamentalGroups/FiniteEtale/InternalHom.lean`). Validated on 2026-10-03 by the strict root build (6008 jobs, warning/error 0, unchanged source snapshot); `exists_internalHom` depends only on the three standard axioms. No connectedness or global-freeness assumption is added. |
| 58.5.5 | [0BNB](https://stacks.math.columbia.edu/tag/0BNB) | Lemma | The geometric fiber makes finite étale schemes over a connected scheme a Galois category | covered | Pi1 `AlgebraicGeometry.FiniteEtale.fiberFunctor` and `galoisCategory`; their proof is independent of `Point.lean` placeholders. |
| 58.6.1 | [0BNC](https://stacks.math.columbia.edu/tag/0BNC) | Definition | Étale fundamental group as automorphisms of the geometric fiber functor | covered | Pi1 notation `π₁ᵉᵗ(ξ) := Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)` together with mathlib's canonical topology on `Aut`. No parallel bundled group is introduced. |
| 58.6.2 | [0BND](https://stacks.math.columbia.edu/tag/0BND) | Theorem | Finite-action equivalence, base-point change, and functoriality of `π₁` | implemented | Part (1) is the canonical `functorToContAction`. `GeometricFiber/BasePoint.lean` now supplies `nonempty_fiber_iso`, `fundamentalGroupIsoOfFiberIso`, its explicit inner-conjugacy identity, `basePointContActionIso`, and `pullbackContActionIso`, using `GaloisCategories/FiberIso.lean` and existing functoriality. Validated on 2026-10-03 by the strict root build (6008 jobs, warning/error 0, unchanged source snapshot). All five listed base-point endpoints depend only on the three standard axioms. |
| 58.6.3 | [0BNE](https://stacks.math.columbia.edu/tag/0BNE) | Lemma | `π₁(Spec K)` is the absolute Galois group, compatibly with the finite-action equivalence | implemented | `GeometricFiber/AlgebraicClosure.lean` constructs the canonical field-extension fiber map by precomposition on geometric points and proves it invertible. `absoluteGaloisEquivFundamentalGroup k` identifies `Gal(SeparableClosure k/k)` with `Aut (fib k (AlgebraicClosure k))` as topological groups. `equivContActionAlgebraicClosureForgetIso` identifies the underlying finite-action functor with the algebraic-closure fiber, and `equivContActionExtendedFiberIso` proves compatibility with restriction along the group isomorphism. The separable closure is mathlib's actual subfield of the algebraic closure. Validated on 2026-10-03 by the strict root build (6008 jobs, warning/error 0, unchanged source snapshot). All three listed comparison endpoints depend only on the three standard axioms. |
| 58.6.4 | [0BQ9](https://stacks.math.columbia.edu/tag/0BQ9) | Remark | Explicit absolute-Galois action on the geometric fiber | covered | Pi1 `Point.lean` defines the action by precomposition with `Spec.map`, proves functoriality and continuity, and supplies the `IsFundamentalGroup` instance under `[IsSepClosure k K]`. Static source has no placeholders; the strict root build passed on 2026-10-03. |
| 58.8.1 | [0BQA](https://stacks.math.columbia.edu/tag/0BQA) | Lemma | An equivalence on finite étale covers preserves connected components and fundamental groups | implemented | The exact qcqs connected-component homeomorphism and connectedness criterion are proved in `FiniteEtale.ConnectedComponents`. `GeometricFiber.PullbackEquivalence.fundamentalGroupEquivOfPullbackEquivalence` gives the connected-scheme topological group isomorphism, with its forward map equal to the actual `fundamentalGroupHom`. On 2026-10-08, the component leaf passed normally in 1.5s with its corrected clopen/topology suppliers; the existing group comparison normal evidence was reused. Direct named endpoint, group isomorphism and forward-map equation queries passed with only propext, Classical.choice and Quot.sound. Exact original hypotheses are retained; no new duplicate endpoint was introduced. |
| 58.8.2 | [09ZS](https://stacks.math.columbia.edu/tag/09ZS) | Lemma | Finite étale covers lift uniquely across a henselian pair | implemented | `AlgebraicGeometry.FiniteEtale.pullback_isEquivalence_of_henselian` in `FiniteEtale/HenselianPair.lean` proves the exact original statement for every commutative ring R, ideal I and `HenselianRing R I`, using the canonical finite-etale pullback along Spec(R/I) → Spec(R). Actual algebra lifts and the affine naturality comparison are constructed; there is no local, Noetherian or completeness assumption. On 2026-10-08, the prior 2.7s normal producer was reused after exact source/closure/configuration/pin/artifact checks. A direct named endpoint axiom query passed in 3.84s with warning/error 0 and only propext, Classical.choice and Quot.sound, in `chapter8-henselian-pair-original-axioms-01`. No duplicate theorem or normal rebuild was added. |
| 58.8.3 | [0BQB](https://stacks.math.columbia.edu/tag/0BQB) | Lemma | Finite étale covers are invariant under scheme thickenings | implemented | `AlgebraicGeometry.FiniteEtale.pullback_isEquivalence_of_surjective_closedImmersion` proves the exact original statement for arbitrary schemes and a surjective closed immersion. Actual affine models, unique Hom lifts, and global gluing are supplied, using arbitrary nil ideals without a uniform nilpotence exponent or Noetherian/qcqs assumption. On 2026-10-08, the affine lifting proof was corrected to use typed scheme arrows at slice-category boundaries; all source options were removed from the changed necessary closure. The fully faithful supplier, gluing, and original leaf passed normal checks in 2.2s, 1.0s and 1.4s. The direct original-endpoint query uses only the three standard axioms. |
| 58.8.4 | [0BQN](https://stacks.math.columbia.edu/tag/0BQN) | Proposition | Universal homeomorphisms induce equivalences on finite étale covers and isomorphisms on `π₁` | implemented | `AlgebraicGeometry.FiniteEtale.pullback_isEquivalence_of_universalHomeomorphism` in `FiniteEtale/UniversalHomeomorphism.lean` proves the original equivalence for arbitrary schemes under the standard integral, universally injective and surjective characterization. `universalHomeomorphism_fundamentalGroup_invariance` gives the connected-scheme topological group isomorphism with its forward map exactly the original `fundamentalGroupHom`. The existing general fully faithful theorem was reused. New actual local split algebras, finite cover/product models, constructed coaction and invariant-algebra comparison supply finite-radicial essential surjectivity; existing finite intermediate models extend it to arbitrary integral maps. Existing local-model gluing now uses proved injectivity only into its actual separated etale overlap targets, so no Flat premise is added. There are no finite-presentation, Noetherian, or global connectedness assumptions in the categorical theorem. On 2026-10-09 the final leaf passed normally in 2.2s, finite/integral model leaves in 3.1s/2.8s, and both actual legacy gluing consumers passed after necessary diagnostics repairs. Seven named original/model/consumer queries passed in 3.56s with warning/error 0 and only propext, Classical.choice and Quot.sound. |
| 58.9.1 | [0A48](https://stacks.math.columbia.edu/tag/0A48) | Lemma | Proper schemes over a henselian local ring have the same finite étale covers as the closed fiber | blocked | The original scope is an arbitrary henselian local ring A and proper X/A, without flatness, finite presentation or Noetherian hypotheses. `SchemeTheory.FiniteEtale.ProperClosedFiberFaithful` now proves closed-fiber faithfulness for a proper scheme over any local base, without Henselian, Noetherian or flatness assumptions; its normal leaf passed in 2.1s and both named axioms queries are standard. `FiniteEtale.ProperHenselianFullyFaithful` now proves canonical closed-fiber fullness and full faithfulness over a Noetherian henselian local base using the actual finite-etale internal Hom and existing section lift (normal 2.7s, both named axiom queries standard). No flatness assumption is added. This intermediate does not algebraize an arbitrary closed-fiber cover and does not complete the unrestricted original 0A48. Completed 58.14.1 object/Hom/equality descent is reusable. `FiniteEtale.AdicCoverTower.exists_proper_finiteEtale_cover_tower` now constructs actual infinitesimal finite-etale lifts, transitions, cartesian successor squares and properness from the literal closed-fiber cover (normal 2.2s, standard axioms). This is input to algebraization, not effectivity. Missing shared suppliers remain coherent completion effectivity with algebra structure over a complete Noetherian proper base, G-ring approximation, and unrestricted proper Noetherian-limit approximation. The flat finitely presented models from paused 58.15 do not supply the original scope. `SchemeTheory.Modules.FiniteRelativeSpec` now constructs the actual relative spectrum of a native quasicoherent ring sheaf, its literal affine spectra, cartesian charts and finite structure morphism (normal 9.4s; six named queries standard). This is ready to consume an algebraized coherent algebra; it does not assert coherent existence. |
| 58.9.2 | [0GS2](https://stacks.math.columbia.edu/tag/0GS2) | Lemma | Proper schemes over a henselian pair have the same finite étale covers as the closed fiber | blocked | The original scope is an arbitrary henselian pair (A,I) and proper X/A. Actual finite-etale cover algebraization and approximation for the pair remain missing; no local, Noetherian, flatness or finite-presentation assumption may be added. Completed 58.14.1 limit descent is available and should be reused. |
| 58.9.3 | [0A49](https://stacks.math.columbia.edu/tag/0A49) | Lemma | Proper schemes are invariant under extension of algebraically closed base fields for finite étale covers | blocked | The original statement allows every extension of algebraically closed fields, including transcendental extensions, and proper X. It requires the proper Henselian comparison and finite-type coefficient-subalgebra descent. Existing finite-intermediate-FIELD descent assumes an algebraic extension and does not cover this scope. A henselization-to-extended-field map need not be local, so the local universal-property endpoint alone is insufficient. |
| 58.10.1 | [0BQE](https://stacks.math.columbia.edu/tag/0BQE) | Lemma | Dense base change is faithful on finite étale covers | implemented | `AlgebraicGeometry.FiniteEtale.pullback_faithful_of_denseRange` proves the full original dense-image statement without reducedness, Noetherianity or quasicompactness. The actual dominance/open-base-change and clopen equalizer suppliers are reused. On 2026-10-08, the endpoint passed normal current-policy verification in 1.6s with warning/error 0, and its direct named axiom query uses only propext, Classical.choice and Quot.sound. |
| 58.10.2 | [0BLQ](https://stacks.math.columbia.edu/tag/0BLQ) | Lemma | Connected punctured strict henselization implies full faithfulness from a local spectrum | implemented | `AlgebraicGeometry.FiniteEtale.puncturedSpectrumPullbackFullyFaithful_of_connected_geometricStalk` in `Purity/PuncturedStrictStalk.lean` proves the original statement for every local ring R, using the actual geometric strict stalk at a local map into a separably closed field. The only geometric premise is connectedness of its actual puncture; no domain, reducedness, normality, Noetherianity, dimension or quasicompactness premise is added. Actual maximal-ideal/puncture comparison, strictly local section extension, flat overlap density, proved fpqc compatibility, EffectiveEpi descent and naturality of the same actual internal-Hom representer supply the canonical finite-etale pullback Full/Faithful structure. On 2026-10-08, actual section descent passed normally in 3.5s and the original endpoint in 3.5s; direct named queries passed with warning/error 0 and only propext, Classical.choice and Quot.sound. This completes 0BLQ, not the remaining global extension criteria. |
| 58.10.3 | [0BQF](https://stacks.math.columbia.edu/tag/0BQF) | Lemma | Noetherian local-connectedness criterion for full faithfulness from a dense open | implemented | `AlgebraicGeometry.FiniteEtale.denseOpenPullbackFullyFaithful_of_noetherianSpace` in `Purity/LocallyConnectedRestriction.lean` proves the original dense-open criterion with only `NoetherianSpace X` and connected actual punctured strict stalks outside U. It derives the finite-component criterion from topological Noetherianity; locally Noetherian, normal, reduced, domain and extra quasicompactness assumptions are absent. Actual finite-presentation stalk spreading, generic-complement puncture identification, compatible affine-chart spreading, maximal open section gluing and the same global internal-Hom representer provide the proof. On 2026-10-08, the original leaf passed normally in 2.9s, and the named original/global-section queries passed with warning/error 0 and only propext, Classical.choice and Quot.sound. |
| 58.10.4 | [0BSA](https://stacks.math.columbia.edu/tag/0BSA) | Lemma | Retrocompact dense-open local-connectedness criterion for full faithfulness | implemented | `AlgebraicGeometry.FiniteEtale.denseOpenPullbackFullyFaithful_of_retrocompact_closed_complement` in `Purity/RetrocompactRestriction.lean` proves the original statement for arbitrary X, a dense open U with quasi-compact inclusion, every point of X \ U closed, and connected actual punctured strict stalks outside U. The complement may be infinite and X need not be quasi-compact or Noetherian. Constructible compactness removes the actual compact open bad equalizer locus to spread compatible stalk sections; closedness identifies the actual stalk pullback with its puncture; existing maximal section gluing and finite-etale internal Hom yield canonical fully faithful restriction. All seven necessary sources passed ordinary verification with zero warnings; the final endpoint took 2.9s. Nine direct axiom queries use only propext, Classical.choice and Quot.sound. |
| 58.10.5 | [0BQG](https://stacks.math.columbia.edu/tag/0BQG) | Lemma | Finite-irreducible-component criterion for full faithfulness from a dense open | implemented | `AlgebraicGeometry.FiniteEtale.denseOpenPullbackFullyFaithful_of_finite_components` in `Purity/LocallyConnectedRestriction.lean` proves the exact original scope: every quasi-compact open has finitely many irreducible components, and actual punctured strict stalks are connected outside the dense open U. No global finite-component bound or retrocompactness of U is assumed. The proof constructs the maximal open carrying compatible local sections, enlarges it using a generic point of its complement and actual stalk/chart spreading, and then uses native internal-Hom naturality to obtain canonical fully faithful pullback. The actual global section theorem and original endpoint passed normal checks (2.2s and 2.9s) and direct standard-axiom queries on 2026-10-08. The earlier ledger shorthand about finite components has been corrected to this local-on-quasi-compact-opens quantification. |
| 58.10.6 | [0BSB](https://stacks.math.columbia.edu/tag/0BSB) | Lemma | Exact local `π₁` sequence for a punctured spectrum and its strict henselization | blocked | Missing the actual punctured strict-local exact sequence and effective overlap descent. The exact conclusion is right surjectivity, trivial composite, and right kernel equal to the closed normal closure of the left image, not necessarily the image itself. Existing 0BSM concerns fraction fields of normal local domains and cannot replace this original scope. The actual double-overlap algebra is now proved in `StrictHenselian.GeometricStalkTensorLocal` and `GeometricStalkTensorClosedFiber`: the localization above the strictly Henselian closed point is the base ring, and the fiber primes are maximal (normal 3.3s/2.2s; named queries standard). Triple-overlap transport, descent effectivity and the exactness endpoint remain. |
| 58.10.6.1 | [0BQH](https://stacks.math.columbia.edu/tag/0BQH) | Equation | Map from the fundamental group of the generic point to that of the scheme | non-propositional | Displayed map induced by the generic-point morphism; its construction is supplied by `GeometricFiber.Functoriality`, with the action comparison in `GeometricFiber.BasePoint` (source validation pending). |
| 58.10.7 | [0BQI](https://stacks.math.columbia.edu/tag/0BQI) | Lemma | Dense opens and the generic point surject onto the `π₁` of an irreducible geometrically unibranch scheme | implemented | `AlgebraicGeometry.FiniteEtale.irreducible_geometricallyUnibranch_fundamentalGroup_surjections` in `GeometricFiber/UnibranchSurjective.lean` proves both original conclusions for arbitrary irreducible X whose actual stalks are geometrically unibranch in the original normalization-of-reduction sense. It quantifies all nonempty opens and all geometric generic points, and uses the literal `fundamentalGroupHom` for the open immersion and `fromSpecResidueField (genericPoint X)`. No reducedness, normality, Noetherianity or quasicompactness is added. Actual integral normal base change, nil-kernel preservation and strict-stalk irreducibility supply the open criterion; the generic residue-to-stalk map, actual stalk spreading and native finite-cover section criterion supply the generic map. The open endpoint passed in 2.9s, generic supplier in 3.0s and final conjunction in 1.9s. Twelve direct axiom queries passed with zero warnings/errors and only propext, Classical.choice and Quot.sound. |
| 58.10.8 | [0BSC](https://stacks.math.columbia.edu/tag/0BSC) | Lemma | Kernel of `π₁(U) → π₁(X)` for finitely many locally connected punctures | blocked | Missing the finite-puncture kernel theorem for arbitrary X, using 0BSA, 0BSB and actual closed-point gluing. Existing 0BTD describes the generic absolute-Galois kernel for normal integral schemes and does not replace this original scope. `FiniteEtale.StalkObjectSpreading.exists_open_model_fromSpecStalk` and `SchemeTheory.Descent.PunctureSectionSpreading` now construct actual neighborhood covers and overlap morphisms by reusing 58.14.1 (normal 2.2s/2.9s; named queries standard). Overlap invertibility, the final closed-point gluing and kernel conclusion remain. |
| 58.11.1 | [0BQK](https://stacks.math.columbia.edu/tag/0BQK) | Lemma | Unramified field extensions correspond to finite étale normalizations of a normal scheme | implemented | `EtaleFundamentalGroups.unramified_normalization_iff_etale_iff_finiteEtale` in `Normalization.UnramifiedNormalization` proves both equivalences for the literal relative normalization. `EtaleDominantQuotient` and `UnramifiedNormalBase` derive étaleness and finite presentation from the actual generic idempotent and local standard étale quotients. Dominance is proved from the generic point. No Noetherian, finite-presentation, or separability assumption is added. Strict leaf/normalization aggregate, original finite-extension consumer, and standard-axiom audits passed on 2026-10-05. |
| 58.11.2 | [0BQL](https://stacks.math.columbia.edu/tag/0BQL) | Lemma | A connected finite étale cover of a normal integral scheme is its integral normal normalization | implemented | `FiniteEtale.Integral` supplies integral and normal source without Noetherian assumptions, using its integral affine-component open cover. `AlgebraicGeometry.FiniteEtale.connectedCoverGenericNormalizationIso` and `_inv_fromNormalization` in `Purity.PuncturedSpectrumConnectedRestriction` identify the actual normalization with the cover over the base. The corresponding function-field APIs are generalized as well. Strict leaves/direct consumers and a consumer with `[IsFinite f] [Etale f] [ConnectedSpace Y]` passed on 2026-10-05; 15 principal declarations use only the three standard axioms. |
| 58.11.3 | [0BQM](https://stacks.math.columbia.edu/tag/0BQM) | Proposition | `π₁` of a normal integral scheme is the Galois group of its maximal unramified extension | implemented | `GeometricFiber.GenericPointSurjective` constructs the canonical continuous surjection. `GenericPointEssentialImage` and `GenericPointFixedSubfield` compare actual finite generic covers and the kernel. `Normalization.GenericExtensionFiber`, `GenericFieldSource`, and `FiniteEtaleGenericFiber` supply both geometric directions without Noetherian or normalization-finiteness assumptions. `Normalization.UnramifiedSubfield.mem_genericKernelFixedField_iff_exists_unramified_finite_subfield` proves literal union membership; `genericKernelFixedField_eq_iSup_unramified` also gives the supremum. `GeometricFiber.GenericPointGaloisQuotient` supplies Galoisness, the topological group isomorphism, and its exact restriction equation. Strict leaves/consumers/aggregates and standard-axiom audits passed; full-tag independent review accepted on 2026-10-05. |
| 58.11.4 | [0BSM](https://stacks.math.columbia.edu/tag/0BSM) | Lemma | Exact `π₁` sequence for a normal local ring and its strict henselian fraction field | implemented | `StrictHenselian.NormalLocalExactSequence.geometricStalk_normalLocal_exactSequence` proves the original statement for every normal local domain, without DVR or noetherian hypotheses. For the actual geometric stalk A of a local geometric point of Spec R, K = Frac R and L = Frac A, the actual maps π₁(Spec L) → π₁(Spec K) → π₁(Spec R) are surjective on the right, have trivial composite, and identify the right kernel with the closed normal closure of the left image. The fraction-field map, native composition comparison, strictly henselian stalk, and finite étale normalization/essential-image suppliers are constructed, with no assumed comparison or desired exactness premise. The existing categorical criteria 0BS8 and 0BS9 supply the final closed-normal-closure conclusion. On 2026-10-06 the exact root passed the default-resource normal kernel in 4.1s, an actual algebraic-closure-point consumer passed in 5.8s with only propext/Classical.choice/Quot.sound, and StrictHenselian.All passed in 3.3s; independent original-statement review passed for source SHA256 9af92890f27beded4a56a8570ae5b6506932abac1d78293727030bc7f8025358. This completes 0BSM, not the remaining Chapter 58 entries or proper base change M2. |
| 58.12.1 | [0BSP](https://stacks.math.columbia.edu/tag/0BSP) | Lemma | Residue fields at nonzero primes of a normal domain with separably closed fraction field are algebraically closed | implemented | `EtaleFundamentalGroups.StrictHenselian.isAlgClosed_primeResidueField_of_isSepClosed_fractionRing` in `StrictHenselian.SeparablyClosedFractionResidue` proves the original statement for any nonzero prime. Its local source uses a monic lift, Gauss's lemma, and a linear perturbation inside the maximal ideal; localization gives the general prime. No Henselian, valuation, Noetherian, or perfectness assumption. Strict leaf, canonical `FractionRing`/`PrimeSpectrum` consumer, and both public kernel-axiom audits passed on 2026-10-05. |
| 58.12.2 | [0BSQ](https://stacks.math.columbia.edu/tag/0BSQ) | Lemma | A normal local domain with separably closed fraction field is strictly henselian | implemented | `StrictHenselian.SeparablyClosedFractionHenselian.henselianLocalRing_and_isSepClosed_residueField_of_isSepClosed_fractionRing` proves the original statement using native `HenselianLocalRing` and `IsSepClosed`. Simple roots lift by induction on monic factors and the existing Gauss/degree-one theorem. The residue-field proof uses a separable monic lift and also covers the case that the local ring is a field. No nonzero-maximal-ideal or algebraic-closedness assumption is added. Strict leaf, original-domain/field/explicit-root consumers, and standard-axiom audits passed on 2026-10-05. |
| 58.12.3 | [0BSS](https://stacks.math.columbia.edu/tag/0BSS) | Lemma | Inertia subgroups are unchanged by arbitrary base change from an invariant subring | implemented | `EtaleFundamentalGroups.Inertia.inertia_invariantBaseChange` in `Inertia.InvariantBaseChange` constructs the actual right-factor tensor action and proves equality of inertia with its contraction by tensor induction. The statement holds for every ideal and arbitrary group. `Ideal.inertia_le_stabilizer` and `IsFractionRing.ker_stabilizerHom` identify this standard inertia with the residue-field formulation. Strict leaf/inertia aggregate, an actual invariant-ring-map consumer, and standard-axiom audits passed on 2026-10-05. |
| 58.12.4 | [0BST](https://stacks.math.columbia.edu/tag/0BST) | Lemma | The map from full invariants to inertia invariants is étale at the chosen prime | implemented | `EtaleFundamentalGroups.Inertia.inertia_invariants_exists_etale_away` in `Inertia.InvariantEtaleNeighborhood` proves the original statement for an arbitrary commutative ring, finite group action and prime q: it constructs f in the actual inertia-invariant algebra with f outside q and genuine `Algebra.Etale` from the full fixed ring to its localization at f. There are no domain, normality, Noetherian, maximal-prime or finite-presentation assumptions, and the ring/group universes are independent. `OriginalPrimeLift` constructs the actual geometric point and stalk-tensor prime with both literal contractions; the existing inertia base-change theorem identifies its inertia with the original one. Generated complete idempotents and all finite group equations descend to one actual affine pointed stage. The selected factor, its actual localization prime and literal neighborhood square supply the source-cover point; `SchemeTheory.RingTheory.Descent.EtaleSource` and `EtaleOpenImage` derive finite presentation and genuine étaleness on an actual principal open. Existing invariant/tensor/Kähler owners are reused, with no new comparison premise or tensor induction. Exact endpoint8.0s, named nontrivial coordinate-swap action on two integer factors5.3s with standard axioms, independent original-statement/structure-scope review, and final Descent.All3.3s passed under unchanged standard limits. Inertia.All is registration-only; no full-library success or arbitrary-integral external0BSR completion is claimed. The next numbered frontier is58.12.5/0BSU. |
| 58.12.5 | [0BSU](https://stacks.math.columbia.edu/tag/0BSU) | Lemma | Localized inertia invariants in a possibly infinite Galois integral closure are a filtered colimit of étale algebras | implemented; scope repair pending | `EtaleFundamentalGroups.Inertia.finiteLevelEtaleCoconeIsColimit` in `Inertia.FiniteLevelEtaleColimit` proves the original statement for any normal domain A, its fraction field K, any possibly infinite Galois L/K, and any prime Q of B = integralClosure A L. With I = Q.inertia Gal(L/K), the literal vertex is `Localization.AtPrime (inertiaInvariantPrime A K L Q)`, the localization of the actual fixed algebra at its contraction of Q. `FiniteLevelEtaleNeighborhoods` constructs principal étale A-algebras and a nonempty directed index from the finite-Galois 0BST supplier and native Away refinements; `FiniteLevelEtaleDiagram` constructs their literal transition maps and cocone. The shared finite-level invariant localization colimit, its existing inclusion-injectivity owner, and native fraction equations/unit cancellation supply the universal property. Independent universes and the arbitrary normal-domain/infinite-extension scope are preserved. Normal gates: shared owner26s and diagram32s reused, colimit20s, named algebraic-integers consumer4.9868s with standard axioms. The fixture checks the actual filtered étale objects and colimit for ℤ/ℚ/AlgebraicClosure ℚ at the zero prime; it makes no nontrivial-inertia claim. The original-statement and normal/kernel proofs remain valid. A later audit of the actual stage API result types corrected the earlier structural-only scope report: `FiniteLevelEtaleNeighborhood.etale` exposes at least19 actual data targets, and `finiteLevelEtaleNeighborhoodInclusion` at least22 before additional cocone categories. These two maintained stage APIs are held for the coding rule while their actual normalization/étale/inclusion owner boundaries are repaired; the mathematical colimit proof is not retracted. No full current coding-completion claim is made until the exact repairs and required consumers pass. Inertia.All is registration-only. Native-owner progress on 2026-10-06: shared normalization/preimage, categorical coefficient, and principal/prime map owners now construct the original finite-stage maps through a proved D-to-U coefficient map. Unit/base/injectivity are supplied before the principal ring enters; the changed original map scopes are at most16, including both normalization and denominator membership targets. All30 existing original declaration signatures are preserved. The final original owner passed5.2s and actual general injection/old-map consumers passed4.13s/4.79s; the old-map fixture uses actual Q/Q data, zero prime and denominator1, without a nontrivial-ramification claim. The single generic localization-injectivity proof is moved to its shared owner; the old private helper delegates to it with its independent target universe preserved. The unchanged endpoint compatibility gate passed18s and its consumer6.50s; matching dependency artifacts were captured later and explicitly joined to their original normal producer, with no fresh-compilation claim for the intervening cached check. `SchemeTheory.RingTheory.Localization.PrincipalProductEtale` proves actual R[1/f] to R[1/(f*d)] etaleness using native nested localization and the proved coefficient square, without domain or nonzero assumptions. It passed4.3s and the actual Z[1/2] to Z[1/6] consumer5.51s. Its one local Algebra supply projects the prescribed native object, with no competing action. All changed Lean sources have zero directives; newly touched CategoryTheory.All also drops its inherited autoImplicit directive and has no declarations. Four aggregates are registration-only. The finite-Galois seed output and integration into the original etale-index/cocone/representative APIs remain coding-held; these prerequisites do not close0BSU coding repair or0BSW. Reuse pointers: `ClassFieldTheory.AlgebraicNumberTheory.Galois.InfiniteBaseChange` uses the same finite-Galois adjoin owner; `ValuedFieldTheory.Ramification.HilbertRamification.HenselianInertiaRestriction` and `Yamaguchi26SolvableCoverings.Geometry.BoundaryStrictImage` retain their stronger valuation/geometric hypotheses. |
| 58.13.0.1 | [0BSV](https://stacks.math.columbia.edu/tag/0BSV) | Equation | Diagram of local, henselian, and strict-henselian punctured-spectrum fundamental groups | non-propositional | The displayed diagram will be assembled from the functorial `π₁` maps of 0BND; it has no independent theorem beyond commutativity. |
| 58.13.1 | [0BSW](https://stacks.math.columbia.edu/tag/0BSW) | Lemma | The local `π₁` diagram is the decomposition/inertia diagram, with the global kernel normally generated by inertia | implemented | Depends on 0BSU, 0BNE, 09ZS, 0BQM, 0BSM, strict henselization, and the functorial `π₁` comparison. Actual affine pointed étale maps lift uniquely to the constructed geometric stalk (`Algebra.Etale.bijective_comp_quotient_of_henselian_target`, named actual-stalk consumer 5.50s with standard axioms); the normalization/fraction-field comparison is now supplied by the proved owners below. The existing same-name Cartier generic-map, fraction-map compatibility and boundary-kernel owners now apply to normal domain stalks instead of DVR stalks, preserving the original Yamaguchi boundary consumers (three roots and five old consumers clean; named normal-stalk diagram consumer 7.71s with standard axioms). Non-affine pointed lift uniqueness and the actual colimit map `geometricStalkToHenselian` are now proved with literal base/residue squares and locality (shared root 4.7s, map 7.3s, named actual-stalk target consumer 13.49s, standard axioms); The literal localization at a prime of the integral closure is now proved strictly Henselian (`EtaleFundamentalGroups.StrictHenselian.integralClosure_localizationAtPrime_strictHenselian` in `StrictHenselian.NormalizationPrime`), using the existing separably-closed fraction-field owner. `GeometricStalkHenselianEmbedding` proves actual stalk algebraicity and injectivity of `geometricStalkToHenselian` for an injective local base map. `EtaleFundamentalGroups.StrictHenselian.geometricStalkToIntegralClosurePrime_injective` in `StrictHenselian.NormalizationPrimeEmbedding` supplies the literal base injection/locality and actual embedding at a normalization prime above the maximal ideal, with maximal contraction derived from integrality. Zero-directive normal roots passed 4.5s/6.0s/6.9s; the original-fraction-field-input normalization embedding consumer passed 11.12s with standard axioms, and StrictHenselian.All passed13s. Independent supplier and direct-structure scope review passed (maximum16). The original normalization inertia now has a native individual automorphism of the literal prime localization with proved base and residue squares (`EtaleFundamentalGroups.StrictHenselian.normalizationPrimeInertiaRingEquiv` and its two companion equations in `StrictHenselian.NormalizationPrimeInertia`). The shared `SchemeTheory.RingTheory.Ramification.InertiaLocalization` owner derives prime preservation from actual inertia and reuses native localization equivalences; its RingHom-level coefficient interface is supplied by the original Galois commutation proof, with no new localization action. Normal roots4.4s/5.2s, original-inertia consumer7.61s and StrictHenselian.All4.1s are clean; the shared Ramification aggregate is registration-only. The actual normalization inertia now fixes the constructed stalk map (`EtaleFundamentalGroups.StrictHenselian.normalizationPrimeInertia_comp_geometricStalkMap` in `StrictHenselian.NormalizationPrimeInertiaFixedImage`), using its proved base/residue squares and target-endomorphism rigidity. The shared `SchemeTheory.Affine.SpecSectionMap` keeps the GammaSpec intermediate in its natural owner; the existing map owner exposes its defining germ equation with its actual naturality proof. A private strict-implicit binder correction preserves the existing public types and proof bodies. `geometricStalkToHenselian_factorization_of_etale` and `geometricStalkToHenselian_exists_preimage_of_etale` in `StrictHenselian.GeometricStalkHenselianEtaleRange` construct actual affine-etale factorization/preimages using pointed lift uniqueness, with no assumed range equality. Fixed-map root7.7s/actual original-inertia consumer7.78s, affine-range root8.1s/native two-sheet actual-stalk consumer7.69s, and final StrictHenselian.All6.5s are clean with standard axioms; direct scope audits remain at most16. `EtaleFundamentalGroups.StrictHenselian.integralClosurePrimeToAmbientField` in `StrictHenselian.NormalizationPrimeField` now constructs the injective literal normalization-prime localization map into the original ambient Galois field, with coefficient/base equations and its actual inertia commutation square. The existing fraction-field proof is moved once into shared FieldLocalization; native galRestrict forward composition and a G/B-localized inertia supplier keep the original-action applications within16 targets. Shared/normalization/new roots3.4s/3.2s/5.5s, original-input consumer7.55s, unchanged actual normalization-target consumer5.96s and StrictHenselian.All3.3s are clean with standard axioms. `StrictHenselian.NormalizationPrimeStalkFraction` now constructs the actual injective fraction-field map of the geometric stalk into the ambient field for a maximal normalization prime over the original normal local domain, and proves original inertia fixes that map. The contraction is derived by integrality; native fraction-field lifting and extensionality are reused. The root10.0s, named original-data consumer6.01s and StrictHenselian.All4.4s pass. `Inertia.InvariantPrimeLocalizationMap` now constructs the original inertia-invariant contracted-prime localization map and its actual base square through shared `SchemeTheory.RingTheory.Localization.SubalgebraPrime`; shared/original roots4.5s/4.9s and actual original-data consumer5.08s pass. Shared `SchemeTheory.RingTheory.Ramification.InertiaFixedIntegralMultiple` now proves that an ambient element fixed by original inertia has an inertia-fixed integral-closure numerator after multiplying by a nonzero element of A. It reuses the native integral-multiple theorem and moves the existing literal action/inclusion proof, with its two sparse helpers, once into `FiniteLevelInertiaImage`; the old ambient proof is removed and its sole call retargeted. The denominator need not avoid the prime. Shared/new/ambient roots10.0s/3.1s/5.0s, refreshed stalk-fraction7.5s and upper-map4.9s, named Qbar one-half/ambient/fraction consumers5.76s/4.86s/7.41s and StrictHenselian.All3.8s pass. These provide forward fixedness, the upper map and actual integral numerators. The original0BSU principal-neighborhood/diagram/colimit chain is now normally verified, and `inertiaInvariantPrimeLocalization_exists_geometricStalk_preimage` proves the reverse preimage statement for the image of the literal invariant-prime-localization map. Its ordinary gate is3.8s, with six named standard-axiom queries for the exact chain. `geometricStalkFractionToNormalizationField_range_eq_fixedField` now proves equality of the actual fraction-map range with the original inertia fixed field; its computation law and actual reverse/forward proof pass5.4/4.7s. The same actual fraction-image fixing subgroup now equals original inertia, and the actual coefficient tower and separable-closure structure are proved; roots9.9/3.6s and named standard-axiom queries pass. The actual strict pi1 image and continuous original local quotient, including its closed-normal-inertia kernel, are now normally verified. The separately defined maximal unramified field M, its actual topological pi1 quotient and literal restriction equation, and the same closed-normal-I fixing subgroup are now proved with standard axioms. The original D-to-separable-residue sequence, its same-I kernel, the actual strict residue identification, and D-equivariant finite-etale point specialization are now normally verified with standard axioms. Original mathematical endpoint verified: originalLocalGaloisDiagram_of_actualHenselizations gives the literal ordinary-henselization scheme-induced lower arrow, transported by the actual strict-residue and independent maximal-unramified-field comparisons. Both original vertical arrows are surjective with kernels original I and its closed normal closure. The same generic map from original D has exactly the original I kernel, and both actual scheme/residue squares commute. Nineteen supplier closures and20 queries7.37s pass; the combined original endpoint passes6.0s and five final named queries8.39s use only standard axioms. No Noetherian, DVR, nonzero-prime or whole-residue separability premise is added. Broad aggregate/all420 validation was stopped by the user; the original changed-leaf and necessary-consumer checks are complete. Whole-library/configuration completion is not claimed. |
| 58.13.2 | [0BTD](https://stacks.math.columbia.edu/tag/0BTD) | Lemma | The original generic-point kernel, all point inertia groups and all chosen strict-henselization Galois groups have the same closed normal generation | implemented | Inertia.genericAbsoluteGaloisHom_ker_eq_pointInertia_and_chosenStrictGalois proves the two original equalities for every normal integral X and arbitrary pointwise strict choice. Literal point inertia, actual stalk fraction fields, restriction maps and prime conjugacy are proved suppliers. Endpoint gates14/4.5/4.7s and19 named standard-axiom queries pass. Exact53-producer admission is admission-original-global-inertia-20261008-01; aggregate/all420 checks remain open. |
| 58.13.3 | [0BTE](https://stacks.math.columbia.edu/tag/0BTE) | Example | A normal quotient singularity ramified only in codimension greater than one | partial; paused by user | The concrete sign action, quadratic invariant-ring equality, finite extension, normality and actual integral-closure identification are proved for all n; the original fraction-field degree is2 for n>0. Normal leaves and standard-axiom queries pass. Actual scheme normalization comparison, ramification locus and codimension are deferred at the user request on2026-10-08. |
| 58.13.4 | [0BTF](https://stacks.math.columbia.edu/tag/0BTF) | Lemma | Eight global, local and fiberwise unramified criteria, with a ninth inertia criterion for Galois extensions | implemented | Normalization.unramified_normalization_criteria_tfae proves the original eight conditions for an arbitrary finite function-field extension of a normal integral scheme. Actual ordinary and strict henselizations and the original fiber degree lower bound are retained. unramified_normalization_galois_criteria_tfae adds only the Galois inertia condition using literal points and residue actions. Reverse8 passes7.1s and both original TFAE endpoints pass5.7s. All10 producer closures are clean;13 named queries3.87s use standard axioms. Admission is admission-original-unramified-criteria-20261008-01. Normalization.All and StrictHenselian.All pass with exact source closures; broader configuration checks remain open. |
| 58.13.5 | [0BUA](https://stacks.math.columbia.edu/tag/0BUA) | Lemma | Decomposition, wild inertia, and tame inertia exact sequences for a possibly infinite Galois extension of a DVR | implemented | `EtaleFundamentalGroups.Inertia.normalizationDVR_ramification` covers both exact sequences and every original wild/tame clause on the SAME canonical data, including primitive actual degrees, continuous surjective D-equivariant θ, the independent wild kernel, D-normality, full profinite/pro-p properties, characteristic-zero triviality and the literal continuous quotient isomorphism. Original-input scope and generated constructor are independently bounded by16. Normal endpoint2.2s, required real consumers, and whole-theorem/actual-supplier axiom queries pass with zero warnings and standard axioms only. The fixed5-A–5-F rows give exact accepted-source evidence. Broad canonical aggregates and remaining new-settings coding holds are still open; no whole-tag completion is asserted. |
| 58.13.6 | [0BUB](https://stacks.math.columbia.edu/tag/0BUB) | Lemma | Absolute decomposition and tame-inertia sequences for a DVR | implemented | `normalizationDVR_absolute_ramification` supplies every original conclusion on the actual objects, with ordinary zero-warning leaf verification and standard axioms. Required subtree and global configuration checks are still pending; whole-library completion is not claimed. |
| 58.14.1 | [0BTV](https://stacks.math.columbia.edu/tag/0BTV) | Lemma | Finite étale covers and `π₁` commute with inverse limits of qcqs schemes with affine transition maps | implemented | SchemeTheory.FiniteEtale.InverseLimitModel proves exists_inverse_limit_model from the original cofiltered qcqs diagram, affine transitions and actual IsLimit: a finite-etale stage object and literal pullback recovery are constructed from finite affine charts, actual Hom descent, eventual diagonal/triple equations and scheme gluing. EtaleFundamentalGroups.FiniteEtale.InverseLimitEquivalence proves baseChange_isLocalization and inverseLimitEquivalence, representing the directed category colimit by the actual stage-model category localized at cartesian transitions. The proved stage inclusions, unit/composition laws and functor-category universal property retain its colimit meaning; inverseLimitEquivalence_pullbackComparison identifies its original pullback functor. InverseLimitComparison proves bijectivity of the already-constructed fundamentalGroupComparison and fundamentalGroupInverseLimitEquiv with every projection equal to the original fundamentalGroupHom. It applies in particular to the original eventually-connected/geometric-point case without adding stronger connectedness, Noetherian, integral-transition, injectivity or projection-surjectivity hypotheses. Existing constant-field/gluing owners are reused with legacy names preserved. Final normal gates: raw-chart assembly2.9s, original object1.9s, category2.4s, group2.5s, all zero errors/warnings; seventeen named final axiom queries use only propext, Classical.choice and Quot.sound. Necessary0BTW consumer passed2.3s after the shared-owner moves. Whole-library and420 validation remain stopped by explicit user instruction; only changed leaves and necessary consumers were checked. |
| 58.14.2 | [0BTW](https://stacks.math.columbia.edu/tag/0BTW) | Lemma | Perfection preserves connectedness and the étale fundamental group | implemented | GeometricFiber.Perfection proves connectedSpace_of_purelyInseparable_constant_extension and perfection_invariance for an arbitrary connected scheme over a field, including exponential characteristic one. The actual pullback fundamentalGroupHom is the forward map of the constructed topological group isomorphism. No qcqs, Noetherian, or finite-type hypothesis is added. Existing purely inseparable finite-etale descent and pullback-equivalence owners are reused. Unnecessary global-model imports were removed, and only required dependency diagnostics were repaired; generic gluing proofs moved to SchemeTheory with old EFG names preserved. The required-closure normal gate passed with zero errors/warnings (final leaf2.4s); nine named axiom queries3.83s use only standard axioms. |
| 58.14.3 | [0BTX](https://stacks.math.columbia.edu/tag/0BTX) | Lemma | Geometric–arithmetic short exact sequence for a geometrically connected qcqs scheme over a field | implemented | `AlgebraicGeometry.FiniteEtale.arithmetic_exactSequence_of_isAlgClosure` in `GeometricFiber.ArithmeticAlgebraicClosure` proves injectivity, surjectivity, and kernel=image for the actual continuous maps with target `Aut(SeparableClosure k/k)`, assuming only qcqs `X/k`, an algebraic closure `L/k`, and connected `X_L`. Native geometric injection and field-map kernel=image are separate endpoints. Actual finite-cover descent and purely inseparable pullback equivalence supply the proof in arbitrary characteristic. Strict leaf/facade builds, canonical `AlgebraicClosure k` consumer, and standard-axiom audits passed on 2026-10-04. |
| 58.15.1 | [0BUN](https://stacks.math.columbia.edu/tag/0BUN) | Lemma | The Stein factor of a proper, flat, finitely presented morphism with geometrically reduced fibers is finite étale | in progress | Native relative normalization now has a proper first map and a structure-sheaf pushforward isomorphism over an arbitrary base, together with the actual cartesian first-map square and normalization comparison isomorphism under flat affine base change. Finite geometrically reduced algebras over a field are étale. The actual global-section algebra of a proper geometrically reduced scheme over a field is now proved finite étale; étaleness descends along field extensions, giving the étale closed-fibre section algebra of the actual local model. The required actual idempotent-section lift through homeomorphisms, local finite-projective kernel/base-change criterion, and geometric connectedness from a field-valued global-sections isomorphism are now proved. Finite separable splitting fields, actual faithfully flat descent of section-map surjectivity, and the local finite-projective-algebra criterion for étaleness from the closed fibre are also proved. The finite separable residue extension is realized by a constructed faithfully flat local Noetherian ring with the precise residue-map and maximal-ideal equations; its residue pushout, actual closed-fibre cartesian comparison, and original-scalar flat Γ tensor comparison are proved. The finite-projective cokernel criterion now supplies finite projectivity and arbitrary base change for the actual kernel; the original local criterion reuses it, and finite-projective algebras are proved étale from their maximal localizations. The actual Noetherian local proper-flat model is now constructed from the original family over an arbitrary local ring, using the existing finite-presentation approximation and local-ring construction. Finite étale covers are proved geometrically reduced and preserve geometric reducedness of a locally finite-type family. For the actual proper family over a Noetherian local ring, étaleness of its closed-fibre section algebra now gives surjectivity of the original closed-fibre section restriction; the proved cochain comparison transfers section surjectivity to the actual kernel base-change map. Actual finite-étale sections also descend along the existing connected-fibre pullback functor. The proper-family H⁰ comparison must still supply the required finite projectivity/base-change statement and the normalization-fibre section isomorphism from the original hypotheses. |
| 58.15.2 | [0C0J](https://stacks.math.columbia.edu/tag/0C0J) | Proposition | Homotopy exact sequence for a proper flat family with geometrically connected reduced fibers | in progress | The actual geometric-fibre composite is trivial and the actual map to the base fundamental group is surjective for a flat, locally finitely presented morphism with geometrically connected fibres over a connected base. These normal-checked results use the existing maps. Middle exactness still needs 0BUN and the finite-étale degree-one comparison. |
| 58.16.1 | [0C0K](https://stacks.math.columbia.edu/tag/0C0K) | Lemma | Specialization maps are functorial for maps of proper families with geometrically connected fibers | blocked | The specialization-map construction from the unnumbered beginning of §58.16 requires strict henselization, 0A48/0A49, and functorial `π₁`; none is yet a public endpoint. |
| 58.16.2 | [0C0L](https://stacks.math.columbia.edu/tag/0C0L) | Lemma | Composites of specialization maps are specialization maps | blocked | Depends on the missing specialization-map construction and functoriality of strict henselization. |
| 58.16.3 | [0C0M](https://stacks.math.columbia.edu/tag/0C0M) | Lemma | Every specialization map is induced by a strictly henselian valuation ring with algebraically closed fraction field | blocked | Depends on 0BSQ, strict henselization, existence of dominating valuation rings, and the specialization-map comparison. |
| 58.16.4 | [0C0N](https://stacks.math.columbia.edu/tag/0C0N) | Lemma | Over a Noetherian base every specialization map is induced by a strictly henselian DVR | blocked | Depends on 0A49, strict henselization of DVRs, existence of a dominating DVR, and the specialization-map comparison. |
| 58.17.1 | [0EL8](https://stacks.math.columbia.edu/tag/0EL8) | Lemma | Full faithfulness of finite étale restriction from full faithfulness of coherent completion on vector bundles | blocked | Depends on 0BL7, 0BQB, coherent sheaves/formal completion, finite locally free pushforward, and algebra-structure reconstruction. |
| 58.17.2 | [0EL9](https://stacks.math.columbia.edu/tag/0EL9) | Lemma | Equivalence of finite étale restriction from equivalence of coherent completion on vector bundles | blocked | Depends on 0EL8, 0BQB, formal algebraization of finite locally free algebras, relative Spec, and the discriminant criterion for étaleness. |
| 58.17.3 | [0ELA](https://stacks.math.columbia.edu/tag/0ELA) | Lemma | Full faithfulness from the colimit over open neighborhoods to a closed subscheme | blocked | Neighborhood-colimit analogue of 0EL8; depends on 0BL7, 0BQB, coherent completion, and filtered categorical colimits. |
| 58.17.4 | [0EK1](https://stacks.math.columbia.edu/tag/0EK1) | Lemma | Equivalence from the colimit over open neighborhoods to a closed subscheme | blocked | Depends on 0ELA, 0BQB, formal algebraization of finite locally free algebras, and openness of the étale locus. |
| 58.17.5 | [0EJX](https://stacks.math.columbia.edu/tag/0EJX) | Lemma | Restriction to a closed subscheme meeting every connected component is faithful on finite étale covers | planned | This is independent of formal completion; it requires connected-component images for finite étale maps and the open equalizer of two maps into an étale target. |
| 58.17.6 | [0EJZ](https://stacks.math.columbia.edu/tag/0EJZ) | Lemma | Three formal-function hypotheses implying full faithfulness of restriction to a closed subscheme | blocked | Formal consequence of 0EL8 plus the missing coherent-completion criterion for finite locally free sheaves. |
| 58.17.7 | [0EK0](https://stacks.math.columbia.edu/tag/0EK0) | Lemma | Neighborhood-colimit formal-function criteria implying full faithfulness | blocked | Formal consequence of 0ELA plus the missing neighborhood version of the coherent-completion criterion. |
| 58.18.1 | [0EK4](https://stacks.math.columbia.edu/tag/0EK4) | Lemma | Finite étale covers of a scheme pushout are the 2-pullback of the cover categories | planned | Pi1 provides finite-étale categorical colimits, but the required geometric scheme pushout/gluing theorem and finiteness descent for the glued étale morphism are not public endpoints. |
| 58.19.1 | [0BLF](https://stacks.math.columbia.edu/tag/0BLF) | Situation | Local ring, hypersurface, and their punctured spectra | non-propositional | Standing notation for §58.19–58.20; canonical localizations, quotients, spectra, and open complements will be used directly. |
| 58.19.2 | [0BLG](https://stacks.math.columbia.edu/tag/0BLG) | Lemma | Dimension or component-intersection hypotheses make hypersurface restriction faithful | blocked | Reduces to 0EJX plus the missing dimension-theoretic result that relevant irreducible components meet the hypersurface. |
| 58.19.3 | [0BLH](https://stacks.math.columbia.edu/tag/0BLH) | Lemma | Algebraize a compatible finite morphism over a punctured spectrum and the completed local scheme | planned | Requires the Beauville–Laszlo-style gluing equivalence for finite algebras over a completion and localizations; no public endpoint was found. |
| 58.19.4 | [0BLI](https://stacks.math.columbia.edu/tag/0BLI) | Lemma | Full faithfulness after completion descends for a henselian ring or henselian pair | blocked | Depends on 0BL7, 0BLH, Zariski main theorem, henselian lifting of idempotents, and faithfully-flat descent. |
| 58.19.5 | [0EK5](https://stacks.math.columbia.edu/tag/0EK5) | Lemma | Dualizing/depth hypotheses imply full faithfulness across a punctured hypersurface | blocked | Depends on 0BLI, 0EL8, dualizing complexes, local cohomology, Serre conditions, and formal geometry. |
| 58.19.6 | [0BM6](https://stacks.math.columbia.edu/tag/0BM6) | Lemma | Local-cohomology torsion hypotheses imply full faithfulness across a punctured hypersurface | blocked | Depends on 0BLI, 0EL8, completion base change for local cohomology, and formal geometry. |
| 58.19.7 | [0BLJ](https://stacks.math.columbia.edu/tag/0BLJ) | Lemma | Depth at least three implies full faithfulness across a punctured hypersurface | blocked | Formal consequence of 0BM6 plus the missing depth-to-local-cohomology-vanishing theorem. |
| 58.20.1 | [0BM8](https://stacks.math.columbia.edu/tag/0BM8) | Lemma | A depth-two finite scheme over a local spectrum is recovered from functions on the punctured preimage | planned | Requires extension of coherent modules across a depth-two closed subset and identification of a finite scheme with the relative spectrum of its pushforward algebra. |
| 58.20.2 | [0BLK](https://stacks.math.columbia.edu/tag/0BLK) | Lemma | Extension of a finite étale punctured cover is equivalent to its global-sections algebra being finite étale | blocked | Depends on 0BM8, preservation of depth under étale local maps, and the affine reconstruction/base-change comparison. |
| 58.20.3 | [0BM9](https://stacks.math.columbia.edu/tag/0BM9) | Lemma | Finite étale covers of a punctured normal local spectrum are finite normal algebras étale off the closed point | blocked | Depends on 0BM8, 0BLK, normalization in finite separable extensions, finiteness of normalization, reflexive-depth results, and scheme/function-field bridges. |
| 58.20.4 | [0BLL](https://stacks.math.columbia.edu/tag/0BLL) | Lemma | A punctured finite étale cover extends before completion iff it extends after completion | blocked | Depends on the algebraization/gluing theorem 0BLH and faithfully-flat descent of finite étale morphisms. |
| 58.20.5 | [0EK6](https://stacks.math.columbia.edu/tag/0EK6) | Lemma | Dualizing/depth hypotheses algebraize an extension from the punctured hypersurface | blocked | Depends on 0BLL, 0EK5, henselian lifting of finite étale covers, and completion preservation of the hypotheses. |
| 58.20.6 | [0BLS](https://stacks.math.columbia.edu/tag/0BLS) | Lemma | Local-cohomology torsion hypotheses algebraize an extension from the punctured hypersurface | blocked | Depends on 0BLL, 0BM6, henselian lifting of finite étale covers, and completion base change for local cohomology. |
| 58.20.7 | [0BLM](https://stacks.math.columbia.edu/tag/0BLM) | Lemma | Depth at least three algebraizes an extension from the punctured hypersurface | blocked | Formal consequence of 0BLS plus depth-to-local-cohomology vanishing. |
| 58.21.1 | [0BJG](https://stacks.math.columbia.edu/tag/0BJG) | Lemma | A height-one prime in `V(f)` of a positive-dimensional Noetherian local ring | planned | Mathlib provides `Ideal.exists_isPrime_height_eq`, principal-ideal height bounds, and `IsLocalization.AtPrime.ringKrullDim_eq_height`; no new notion is needed. |
| 58.21.2 | [0BJH](https://stacks.math.columbia.edu/tag/0BJH) | Lemma | A flat quasi-finite morphism unramified in codimension one is étale at the point | blocked | Mathlib has canonical `Scheme.Hom.QuasiFiniteAt`; scheme-level pointwise `EtaleAt`/`UnramifiedAt`, the discriminant ramification locus, and the local finite reduction needed for the implication are not public APIs. |
| 58.21.3 | [0BMA](https://stacks.math.columbia.edu/tag/0BMA) | Lemma | Purity for regular local rings and finite normal extensions | blocked | `IsRegularLocalRing` and `FiniteEtale.pullback` exist, but punctured-spectrum extension, 0BM9, 0BLM, and 0BJH are missing. |
| 58.21.4 | [0BMB](https://stacks.math.columbia.edu/tag/0BMB) | Lemma | Purity of branch locus | blocked | Depends on 0BMA and pointwise localization, dimension, normality, unramifiedness, and étaleness infrastructure absent from the current scheme API. |
| 58.21.5 | [0EY6](https://stacks.math.columbia.edu/tag/0EY6) | Lemma | Canonical reflexive finite extension of a finite étale cover across a depth-two complement | blocked | Reflexive coherent sheaves, coherent direct image, relative Spec, stalk depth, and the required flat-base-change theorem are missing. |
| 58.21.6 | [0EY7](https://stacks.math.columbia.edu/tag/0EY7) | Lemma | Local purity outside an open implies essential surjectivity of finite étale restriction | blocked | Requires local purity, Noetherian induction, and finite-presentation spreading from a local spectrum to an open neighbourhood. |
| 58.22.1 | [0BLN](https://stacks.math.columbia.edu/tag/0BLN) | Lemma | Faithfulness of restriction near a punctured hypersurface under a component-dimension bound | blocked | Depends on the unimplemented 0EJX endpoint and the missing dimension theorem forcing relevant components to meet the hypersurface. |
| 58.22.2 | [0DXX](https://stacks.math.columbia.edu/tag/0DXX) | Lemma | A dualizing-complex criterion for full faithfulness near a punctured hypersurface | blocked | Depends on 0ELA, topological invariance 0BQB, dualizing complexes, and formal-geometry theorem 52.15.7. |
| 58.22.3 | [0BLP](https://stacks.math.columbia.edu/tag/0BLP) | Lemma | A local-cohomology finiteness criterion for full faithfulness | blocked | Mathlib has `localCohomology`, but not 0ELA or the completion and finiteness theorem 52.15.8 needed here. |
| 58.23.1 | [0DXY](https://stacks.math.columbia.edu/tag/0DXY) | Lemma | A dualizing and depth criterion for algebraizing finite étale covers from a hypersurface | blocked | Requires 0EK1, dualizing complexes, Serre `S₂`, stalk depth, and formal algebraization theorem 52.24.1. |
| 58.23.2 | [0BLV](https://stacks.math.columbia.edu/tag/0BLV) | Lemma | An `H¹` and `H²` local-cohomology criterion for algebraization equivalence | blocked | Requires 0EK1 and the unavailable local-cohomology completion and algebraization theorem 52.24.2. |
| 58.23.3 | [0BLW](https://stacks.math.columbia.edu/tag/0BLW) | Remark | The algebraization equivalence for complete normal local domains of dimension at least four | blocked | This is a substantive consequence of 0DXY and normal Noetherian implies `S₂`; neither 0DXY nor a canonical `S₂` API is available. |
| 58.24.1 | [0EK9](https://stacks.math.columbia.edu/tag/0EK9) | Lemma | Local purity upgrades neighbourhood algebraization to essential surjectivity | blocked | Depends on 0DXY, purity at maximal localizations of `A_f`, and spreading finite étale covers across finitely many missing points. |
| 58.24.2 | [0EKA](https://stacks.math.columbia.edu/tag/0EKA) | Lemma | The local-cohomology version of the local-purity extension theorem | blocked | Depends on 0BLV and the same unavailable local extension and spreading infrastructure as 0EK9. |
| 58.25.1 | [0DXZ](https://stacks.math.columbia.edu/tag/0DXZ) | Lemma | Purity descends to a hypersurface under dualizing and depth hypotheses | blocked | Formal consequence of the blocked extension theorem 0EK9 plus finite étale base-change and purity comparison. |
| 58.25.2 | [0BPC](https://stacks.math.columbia.edu/tag/0BPC) | Lemma | Purity descends to a hypersurface under local-cohomology hypotheses | blocked | Formal consequence of the blocked local-cohomology extension theorem 0EKA. |
| 58.25.3 | [0BPD](https://stacks.math.columbia.edu/tag/0BPD) | Proposition | Purity for local complete intersections of dimension at least three | blocked | Regular sequences exist in mathlib, but 0BPC, a canonical complete-intersection predicate, and the Cohen–Macaulay/depth/local-cohomology bridge do not. |
| 58.26.1 | [0EY9](https://stacks.math.columbia.edu/tag/0EY9) | Lemma | Full faithfulness along the punctured zero section of a formal power-series family | blocked | `MvPowerSeries` and its adic completeness exist, but stalk depth, `Γ(U, 𝒪_U) = A`, coherent completion, and 0EL8 are missing. |
| 58.26.2 | [0EYA](https://stacks.math.columbia.edu/tag/0EYA) | Lemma | Ramanujam–Samuel purity for finite étale covers of a formal power-series ring | blocked | Depends on 0EY6, 0EY9, flat-base-change compatibility of the reflexive extension, and depth preservation. |
| 58.26.3 | [0EYB](https://stacks.math.columbia.edu/tag/0EYB) | Lemma | Purity for a dense open in a smooth family away from depth-at-most-one fibers | blocked | Depends on 0BQF, 0EY6, 0EYA, stalk depth, smooth completion by power series, and étale-locus infrastructure. |
| 58.26.4 | [0EYC](https://stacks.math.columbia.edu/tag/0EYC) | Proposition | Ramanujam–Samuel purity for an adically formally smooth local homomorphism | blocked | Requires 0EYB, adic-topological formal smoothness, completion comparison, and Popescu's theorem; algebraic `RingHom.FormallySmooth` is not a substitute. |
| 58.27.1 | [0ELC](https://stacks.math.columbia.edu/tag/0ELC) | Proposition | Lefschetz full faithfulness for a hypersurface section under a depth-plus-dimension bound | blocked | Depends on 0EJZ/0EL8 and the missing formal-functions theorem for an ample divisor. |
| 58.27.2 | [0ELD](https://stacks.math.columbia.edu/tag/0ELD) | Proposition | Lefschetz equivalence from open neighborhoods of a hypersurface section | blocked | Depends on 0EK1 and the missing algebraization/formal-functions theorem under the stronger depth-plus-dimension bound. |
| 58.27.3 | [0ELE](https://stacks.math.columbia.edu/tag/0ELE) | Proposition | Lefschetz equivalence, and `π₁` isomorphism, assuming local purity off the hypersurface | blocked | Depends on 0ELC, 0ELD, 0BQA, local closed purity, finite-point extension of finite étale covers, and the functorial `π₁` comparison. |
| 58.28.1 | [0EA2](https://stacks.math.columbia.edu/tag/0EA2) | Lemma | A canonical-divisor condition on a surface resolution implies a rational singularity and vanishing exceptional divisor | planned | Requires surface resolutions, dualizing modules, Grothendieck duality/trace, Grauert–Riemenschneider vanishing, rational singularities, and minimal-resolution intersection theory; no existing Lean endpoint was found. |
| 58.28.2 | [0EA3](https://stacks.math.columbia.edu/tag/0EA3) | Lemma | A finite-type map from a normal surface germ to an excellent regular local base, étale off the closed germ, is étale at the germ | blocked | Depends on 0EA2, existence/spreading of minimal surface resolutions, duality and canonical modules, openness of regular/CM loci, and étale descent. |
| 58.28.3 | [0EA4](https://stacks.math.columbia.edu/tag/0EA4) | Lemma | Purity of ramification locus | blocked | Depends on 0EA3, purity of branch locus 0BMB, normalization after hypersurface section, excellence/Nagata completion, dimension induction, and quasi-finiteness criteria. |
| 58.29.1 | [0ECB](https://stacks.math.columbia.edu/tag/0ECB) | Lemma | Higher coherent cohomology of an affine étale cover of a punctured equicharacteristic regular local scheme is injective-residue-hull torsion | planned | Requires scheme cohomology and flat base change, local cohomology, completion/Cohen structure, Frobenius-flat or differential-operator arguments, and injective hulls; no matching endpoint was found. |
| 58.29.2 | [0ECC](https://stacks.math.columbia.edu/tag/0ECC) | Lemma | Vanishing of the top higher cohomology forces the étale punctured cover to be affine | blocked | Depends on 0ECB, derived cohomology/base change, the Tor spectral sequence, duality for injective hulls, and an affineness criterion from principal affine opens. |
| 58.29.3 | [0ECD](https://stacks.math.columbia.edu/tag/0ECD) | Theorem | The maximal étale locus of a finite-type map from a normal scheme to an excellent regular scheme over a field is affine | blocked | Depends on 0EA4, 0ECC, local cohomological dimension, Hartshorne–Lichtenbaum vanishing, dimension formulas, and limit-locality of affineness. |
| 58.30.1 | [0C0P](https://stacks.math.columbia.edu/tag/0C0P) | Lemma | Specialization is surjective for a flat proper family with geometrically connected fibers and geometrically reduced special fiber | blocked | Depends on the specialization construction of §58.16, homotopy exactness 0C0J, and triviality of the `π₁` of a strictly henselian local base. |
| 58.30.2 | [0C0Q](https://stacks.math.columbia.edu/tag/0C0Q) | Proposition | Specialization is an isomorphism for a smooth proper family in residue characteristic zero | blocked | Depends on 0C0P, 0C0K/0C0N, 0BTV/0BTW, 0BN7, 0A48, purity of branch locus 0BMB, normalization, and Abhyankar's lemma. |
| 58.30.3 | [0C0R](https://stacks.math.columbia.edu/tag/0C0R) | Theorem | Specialization is surjective and an isomorphism on maximal prime-to-`p` quotients in residue characteristic `p` | blocked | Depends on 0C0Q's construction, tame ramification/Abhyankar, 0BQN, a canonical maximal prime-to-`p` profinite quotient, and the corresponding finite-Galois essential-image criterion. |
| 58.31.1 | [0EYD](https://stacks.math.columbia.edu/tag/0EYD) | Lemma | Codimension-one unramifiedness/tameness is preserved by suitable base change | planned | CFT supplies field/valuation-level tame base-change ingredients, but the scheme codimension-one notions and the general local-ring comparison are not public endpoints. |
| 58.31.2 | [0H2W](https://stacks.math.columbia.edu/tag/0H2W) | Lemma | A codimension-one-unramified finite étale cover extends across a regular complement | blocked | Depends on spreading finite étale covers from local rings, the local-purity results 0BMA/0EY7, and finite gluing over all codimension-one boundary points. |
| 58.31.3 | [0EYE](https://stacks.math.columbia.edu/tag/0EYE) | Lemma | Extension across a regular effective Cartier divisor for codimension-one-unramified covers | blocked | Specializes 0H2W and additionally needs the regular-local lifting theorem from regularity of a Cartier quotient. |
| 58.31.4 | [0EYF](https://stacks.math.columbia.edu/tag/0EYF) | Example | Standard tamely ramified morphism `A[x]/(x^e-f)` | planned | Mathlib has monic-polynomial finite free and localization/étale ingredients, and CFT has field-level tame definitions; the exact finite-locally-free, localized-étale, codimension-one-tame scheme package remains to prove without creating a new tame wrapper. |
| 58.31.5 | [0EYG](https://stacks.math.columbia.edu/tag/0EYG) | Lemma | Abhyankar's lemma for a regular divisor: tame covers are étale-locally standard | blocked | Depends on 0EYD–0EYF, strict henselization and its filtered étale presentation, normalization, field-level Abhyankar/Kummer results, descent of finite presentation, and local regularity. |
| 58.31.6 | [0EYH](https://stacks.math.columbia.edu/tag/0EYH) | Lemma | The normalization of a regular-divisor tame cover is finite locally free with regular reduced boundary and standard local form | blocked | Depends on 0EYG, normalization commuting with étale base change, and the integral-closure computation for `A[x]/(x^e-f)`. |
| 58.31.7 | [0EYI](https://stacks.math.columbia.edu/tag/0EYI) | Lemma | DVR-valued lifting and split-generic-fiber criteria for the normalization to be étale along a trait | blocked | Depends on 0EYH, the valuative criterion for finite morphisms, étale localization of DVRs, and the standard Kummer local calculation. |
| 58.31.8 | [0EYJ](https://stacks.math.columbia.edu/tag/0EYJ) | Lemma | Extend prime-to-characteristic pointed Galois covers from the generic fiber of a smooth family over a Noetherian normal base | blocked | Depends on 0EYE–0EYI, 0BJH/0EYB, formal smooth neighborhoods of a section, depth/normalization base change, and spreading with a finite group action. |
| 58.31.9 | [0EZJ](https://stacks.math.columbia.edu/tag/0EZJ) | Lemma | The preceding pointed Galois-cover extension over a qcqs normal integral base | blocked | Depends on 0EYJ, 0BTV, Noetherian approximation preserving normality/geometric connectedness, and descent of the cover, action, and rational point. |
| 58.32.1 | [0G1F](https://stacks.math.columbia.edu/tag/0G1F) | Lemma | Positive-characteristic coordinate modification strictly lowers the nonfinite-generator measure `NF` | planned | Requires the unnumbered §58.32 setup/measure, Noether normalization with Frobenius-twisted coordinates, Kähler differentials, étale criteria, and preservation of the quotient surjection. |
| 58.32.2 | [0G1G](https://stacks.math.columbia.edu/tag/0G1G) | Lemma | An affine étale morphism to affine space in positive characteristic admits a finite étale structure map | blocked | Direct minimality argument from 0G1F; the missing source is that coordinate-modification lemma and its `NF` infrastructure. |
| 58.32.3 | [0G1H](https://stacks.math.columbia.edu/tag/0G1H) | Lemma | A finite étale cover of a closed subscheme of affine space embeds clopenly in the pullback of a finite étale cover of affine space | blocked | Depends on 0G1F, lifting finite étale algebras across a quotient to an étale algebra, and the open-and-closed criterion for an étale closed immersion. |
| 58.32.4 | [0G1I](https://stacks.math.columbia.edu/tag/0G1I) | Proposition | A closed immersion of connected affine `𝔽_p`-schemes induces an injective map on étale fundamental groups | blocked | Depends on 0G1H, 0BTV, the injectivity criterion 0BN7, Noetherian approximation of finite étale covers, and functorial `π₁`. |

## 4. Non-environment body claims


This ledger complements `STACKS_TAGS.md`.  It records mathematical claims
which are not represented by one of the 141 numbered Definition/Lemma/
Proposition/Theorem/Equation/Example/Remark/Situation entries.

Statuses have the same meaning as in `STACKS_TAGS.md`.

| Location | Official tag | Claim | Status | Lean owner / evidence |
|---|---|---|---|---|
| 58.2, continuity criterion | [04JI](https://stacks.math.columbia.edu/tag/04JI) | An action on a discrete space is continuous iff every point stabilizer is open; for a discrete group this is the ordinary notion of a group action. | covered | `continuousSMul_iff_stabilizer_isOpen`, `MulAction.stabilizer`, and `DiscreteContAction`; no second continuity predicate is introduced. |
| 58.3, topology on `Aut(F)` | [0BMQ](https://stacks.math.columbia.edu/tag/0BMQ) | Give each finite-fiber automorphism group the discrete topology and `Aut(F)` the induced subspace topology; all fiber actions are continuous and the topology has the expected initial universal property. | covered | `PreGaloisCategory.autEmbedding`, `autEmbedding_isClosedEmbedding`, `aut_discreteTopology`, `continuousSMul_aut_fiber`, `Topology.IsInducing.continuous_iff`, and `continuous_pi_iff`. |
| 58.3, profinite completion construction | [0BMQ](https://stacks.math.columbia.edu/tag/0BMQ) | The inverse system of open normal finite quotients is cofiltered and gives the profinite completion, with its universal property for profinite targets. | planned | `ProCGroups.Completion.IsProCCompletion` with `FiniteGroupClass.allFinite` owns the abstract universal property. The concrete all-open-normal-quotient comparison and cofinality endpoint still have to be supplied without a second completion definition. |
| 58.3, exact functors | [0BMQ](https://stacks.math.columbia.edu/tag/0BMQ) | “Exact” means preservation of finite limits and finite colimits, hence of equalizers, coequalizers, pullbacks, and pushouts. | covered | Use `PreservesFiniteLimits F` and `PreservesFiniteColimits F` directly; an `Exact` wrapper would duplicate the canonical classes. |
| 58.3, enumerated item 2 | [0BMZ](https://stacks.math.columbia.edu/tag/0BMZ) | Every object of a Galois category is a finite, possibly empty, coproduct of connected objects. | covered | `CategoryTheory.PreGaloisCategory.has_decomp_connected_components` and `has_decomp_connected_components'`. |
| 58.3, enumerated item 7 | [0BN1](https://stacks.math.columbia.edu/tag/0BN1) | For connected `X`, two morphisms `a b : X ⟶ Y` are equal if their fiber maps agree on one point of `F.obj X`. | covered | `CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected`; no duplicate theorem is needed. |
| 58.3, Galois cardinality criterion | [0BMQ](https://stacks.math.columbia.edu/tag/0BMQ) | For connected `X`, `\|Aut(X)\| ≤ \|F(X)\|`; equality characterizes Galois objects and is equivalent to transitivity of the automorphism action. | implemented | Canonical `card_aut_le_card_fiber_of_connected` and `isGalois_iff_pretransitive` supply the inequality and transitivity criterion; `EtaleFundamentalGroups.GaloisCover.Basic.isGalois_iff_card_aut_eq_card_fiber` proves the missing equality characterization. The module is verified by strict `--wfail` build. |
| 58.5, finite étale covers | [0BL6](https://stacks.math.columbia.edu/tag/0BL6) | Objects and morphisms of `FÉt_X`, including the empty finite étale cover. | covered | Canonical `AlgebraicGeometry.FiniteEtale`; no second scheme-specific cover category is introduced. |
| 58.5, geometric-point data | [0BL6](https://stacks.math.columbia.edu/tag/0BL6) | A geometric point is a morphism `Spec Ω ⟶ X`; record lying over a point and the residue-field notation. | covered | Use the raw scheme morphism used by Pi1. Existing `[IsAlgClosed Ω]` instances supply `[IsSepClosed Ω]`; no bundled geometric-point wrapper is needed. |
| 58.5, fiber as relative morphisms | [0BL6](https://stacks.math.columbia.edu/tag/0BL6) | The fiber functor `U ↦ \|U ×_X x̄\|` identifies with the set of `X`-morphisms `x̄ ⟶ U`. | covered | `AlgebraicGeometry.FiniteEtale.fiber`, `fiberPt`, and the repaired `fiberObjEquivHom` / `fiberIsoCoyoneda` in Pi1. |
| 58.7, definition in prose | [03SF](https://stacks.math.columbia.edu/tag/03SF) | A finite étale morphism is a Galois cover iff its object in `FÉt_X` is Galois. | covered | Use `CategoryTheory.PreGaloisCategory.IsGalois` itself as the definition; a scheme-specific parallel predicate would be redundant. |
| 58.7, four-way characterization | [03SF](https://stacks.math.columbia.edu/tag/03SF) | Galois cover iff connected with automorphism-cardinality equal to degree iff transitive fiber action iff simply transitive fiber action. | implemented | `EtaleFundamentalGroups.GaloisCover.Basic` proves the simply-transitive and automorphism-cardinality forms, `natCard_fiber_eq_finrank`, and the connected degree characterization; the transitive form is canonical mathlib `isGalois_iff_pretransitive`. The module is verified by strict `--wfail` build. |
| 58.7, domination | [03SF](https://stacks.math.columbia.edu/tag/03SF) | Every connected finite étale cover is dominated by a finite étale Galois cover. | covered | Apply `CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_connected` to Pi1's finite-étale Galois-category instance. |
| 58.7, normal quotients | [03SF](https://stacks.math.columbia.edu/tag/03SF) | Galois covers correspond to quotients by normal open subgroups, equivalently finite continuous quotient groups of `π₁`. | blocked | Depends on 58.6.2 and the Galois-object action equivalence. |
| 58.7, common domination | [03SF](https://stacks.math.columbia.edu/tag/03SF) | Two finite étale Galois covers admit a common Galois cover whose group embeds into the product. | implemented | `PreGaloisCategory.exists_common_galois_cover` takes the connected component of the product through a chosen fiber pair; `isGalois_of_mono_to_binaryProduct` proves it Galois and `autMapHom_prod_injective_of_mono` gives the required injection into the product. The module is verified by strict `--wfail` build. |
| 58.11, unramified in a field extension | [0BQJ](https://stacks.math.columbia.edu/tag/0BQJ) | Define when a normal integral scheme is unramified in a field extension `L/K`, and prove that this implies `L/K` is separable. | planned | Use `Scheme.Hom.normalization`, `fromNormalization`, `FormallyUnramified`, and `LocallyOfFiniteType` as owners. The scheme-level statement and separability endpoint are not yet public. |
| 58.13, henselian local setup | [0BSD](https://stacks.math.columbia.edu/tag/0BSD) | Construct `Aʰ`, `Aˢʰ`, and `Aˢᵉᵖ`, the map from a chosen residue embedding, and the trivial fundamental group of the resulting strict-henselian spectra. | blocked | General strict henselization, its fraction field, and their finite-étale comparison are not yet present in Pi1/mathlib. |
| 58.13, local decomposition and inertia | [0BSD](https://stacks.math.columbia.edu/tag/0BSD) | Define the local decomposition group `D` and inertia group `I`. | planned | The valuation case is canonical CFT: `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup`, `inertiaGroup`, `residueAction`, and `residueAction_ker`. The general normal-local ideal version remains source work. |
| 58.13, action on infinite normalization | [0BSD](https://stacks.math.columbia.edu/tag/0BSD) | Give `Xˢᵉᵖ` its right Galois action, define every `D_y` and `I_y`, and choose `K_xˢʰ ⟶ Kˢᵉᵖ`. | blocked | Requires an infinite-normalization action and the strict-henselization scheme/field bridge. |
| 58.13, roots-of-unity inverse system | [0BSD](https://stacks.math.columbia.edu/tag/0BSD) | Form the inverse system `μ_n(k)` over a multiplicatively directed set, prove functoriality and the `Aut(k)` action, and identify the `{1,n}` and ℓ-adic examples. | planned | Reuse `rootsOfUnity`, `powMonoidHom`, `restrictRootsOfUnity`, `MulEquiv.restrictRootsOfUnity`, and `ProCGroups.InverseSystems.InverseSystem`; only the concrete comparison endpoints are missing. |
| 58.16, general specialization map | [0BUP](https://stacks.math.columbia.edu/tag/0BUP) | Construct `sp_φ` for a proper morphism with geometrically connected fibers, prove the triangle with `π₁(X)`, and record dependence on `φ`. | blocked | Needs functorial `π₁` and the strict-henselian proper-comparison theorem. |
| 58.16, valuation specialization | [0BUP](https://stacks.math.columbia.edu/tag/0BUP) | Construct `sp_R` for a strictly henselian valuation ring with algebraically closed fraction field. | blocked | Specialization of the preceding unavailable construction. |
| 58.16, DVR specialization | [0BUP](https://stacks.math.columbia.edu/tag/0BUP) | Construct `sp_R` for a strictly henselian DVR and a geometric generic point. | blocked | Specialization of the same unavailable construction. |
| 58.17, restriction to a closed subscheme | [0EJW](https://stacks.math.columbia.edu/tag/0EJW) | A closed immersion `Y ⟶ X` induces `FÉt_X ⟶ FÉt_Y`. | covered | `AlgebraicGeometry.FiniteEtale.pullback`. |
| 58.17, finite locally free formal modules | [0EJW](https://stacks.math.columbia.edu/tag/0EJW) | Define when a coherent formal module `(F_n)` is finite locally free. | blocked | The coherent-formal-module foundation is absent from mathlib/Pi1. |
| 58.19, connected components under restriction | [0BLE](https://stacks.math.columbia.edu/tag/0BLE) | Full faithfulness of the restriction functor implies equality of the numbers of connected components of `U` and `U₀`. | planned | Derive from `has_decomp_connected_components` and the numbered full-faithfulness theorem; no exact endpoint currently exists. |
| 58.20, local purity criterion | [0BM7](https://stacks.math.columbia.edu/tag/0BM7) | A Noetherian local ring satisfies purity iff restriction to its punctured spectrum is essentially surjective. | planned | This is a genuine Stacks-specific definition, but its field is the canonical categorical predicate `F.EssSurj`; no replacement essential-surjectivity notion is introduced. |
| 58.22, filtered neighborhood functor | [0BLU](https://stacks.math.columbia.edu/tag/0BLU) | Construct `colim_{U₀ ⊂ U' ⊂ U} FÉt_{U'} ⟶ FÉt_{U₀}`. | blocked | The filtered diagram of open neighborhoods and its `Cat`-valued colimit are not implemented. |
| 58.29, affine maximal étale locus | [0ECA](https://stacks.math.columbia.edu/tag/0ECA) | If the maximal étale open `V ⟶ X` is affine, purity of the ramification locus follows. | blocked | Requires the affine-complement result from Divisors and the missing purity endpoint. |
| 58.30, maximal prime-to-`p` quotient | [0BUQ](https://stacks.math.columbia.edu/tag/0BUQ) | Define the maximal prime-to-`p` quotient and the notation `π₁'(X)`. | planned | Use `FiniteGroupClass.sigmaGroup {q \| q ≠ p}`, `OpenNormalSubgroupInClass`, `openNormalSubgroupInClassSystem`, `IsMaximalProCQuotient`, and `proCResidualCore`; a parallel quotient construction is forbidden. |
| 58.31, codimension-one ramification predicates | [0BSE](https://stacks.math.columbia.edu/tag/0BSE) | Define being unramified, respectively tamely ramified, at every boundary prime divisor. | planned | Field/DVR ownership is `Algebra.IsUnramifiedAt` and `KummerTheory.FiniteTamelyRamifiedExtension`; only the scheme codimension-one layer is new. |
| 58.32, polynomial-presentation data | [0G1E](https://stacks.math.columbia.edu/tag/0G1E) | Package the characteristic-`p` polynomial presentation, finite étale map `A ⟶ B`, and diagram `(C, φ, τ)`. | planned | Use `Algebra.Etale`, `Algebra.FiniteType`, `Ideal.map`, `Ideal.Quotient`, `AlgHom`, and `Function.Surjective` directly. |
| 58.32, normalization-failure invariant | [0G1E](https://stacks.math.columbia.edu/tag/0G1E) | Define the minimum `NF(C,φ,τ)` and prove `NF = 0 ↔ φ` is finite. | planned | `NF` is genuinely Stacks-specific; its implementation must use canonical `IsIntegral`, `Algebra.adjoin`, and `Module.Finite`. |

### Audit completeness

Every section 58.1–58.32 of pinned `pione.tex` was read.  On the table's
grouping convention, the ledger has 33 independent body-claim rows.  Sections
58.1, 58.4, 58.6, 58.8–58.10, 58.12, 58.14–58.15, 58.18, 58.21, and
58.23–58.28 contain no additional independent body claim beyond their numbered
entries.  A mixed-characteristic sentence in 58.29 is explicitly a conjecture
and is not presented as a theorem to formalize.

## 5. Direct external-tag inventory


This ledger is the reproducible initial inventory of external Stacks Project tags
referenced by Chapter 58, **Fundamental Groups of Schemes**. It is a dependency
classification ledger, not a claim that every referenced result must be reimplemented.
The Lean-ownership/use classification has now been checked tag by tag against mathlib,
`Pi1`, `ProCGroups`, and CFT; the 286-entry completeness boundary contains no `unknown`.

### Corpus and extraction rule

- Chapter: [`0BQ6`](https://stacks.math.columbia.edu/tag/0BQ6)
- Stacks Project revision: `ed88ff78`
- Extracted: 2026-07-29
- Official API documentation: [`/api`](https://stacks.math.columbia.edu/api)
- Pinned source: [`pione.tex`](https://raw.githubusercontent.com/stacks/stacks-project/ed88ff78/pione.tex)
- Pinned tag map: [`tags/tags`](https://raw.githubusercontent.com/stacks/stacks-project/ed88ff78/tags/tags)

Reproduction procedure:

1. Read every `\label{...}` in pinned `pione.tex`, prefix it with `pione-`, and resolve
   it through pinned `tags/tags`. This gives 176 Chapter 58-local tags, including the
   two item tags omitted from the chapter structure tree.
2. Read [`0BQ6/structure`](https://stacks.math.columbia.edu/data/tag/0BQ6/structure)
   and take its 32 section tags.
3. For every section tag `S`, fetch `https://stacks.math.columbia.edu/data/tag/S/content/full`,
   collect every `data-tag="T"`, and discard `T` when it is one of the 176 local tags.
4. Keep the source section tag on every occurrence, then group by target tag.
5. Resolve target ownership through pinned `tags/tags` and the owning chapter official
   `/data/tag/CHAPTER_TAG/structure` response.

Checks for this revision:

- Chapter 58-local tags: **176**
- section payloads: **32**
- external reference occurrences: **423**
- distinct external target tags after deduplication: **284**
- owning chapters: **28**
- targets without chapter/section metadata: **0**

> Audit boundary: a literal `\ref{...}` scan of pinned `pione.tex` gives 426 external
> occurrences and 286 distinct targets. The two raw-source-only targets are
> [`0033`](https://stacks.math.columbia.edu/tag/0033) and
> [`0EKE`](https://stacks.math.columbia.edu/tag/0EKE). The 284-row main ledger below
> follows the project official rendered `content/full` API corpus. The raw-source
> supplement records the other two, so the completeness boundary is 286 tags.

Source tags in the table are Chapter 58 **section tags**. `×n` is the number of rendered
references from that section. More precise lemma/proof ownership can be refined later
without changing the 284-target invariant.

### Chapter totals

| Chapter | Title | Unique tags | Occurrences |
|---:|---|---:|---:|
| 4 | Categories | 8 | 11 |
| 5 | Topology | 5 | 7 |
| 7 | Sites and Sheaves | 1 | 1 |
| 9 | Fields | 5 | 8 |
| 10 | Commutative Algebra | 53 | 79 |
| 15 | More on Algebra | 49 | 66 |
| 16 | Smoothing Ring Maps | 4 | 4 |
| 23 | Divided Power Algebra | 1 | 1 |
| 26 | Schemes | 2 | 2 |
| 27 | Constructions of Schemes | 1 | 1 |
| 28 | Properties of Schemes | 8 | 11 |
| 29 | Morphisms of Schemes | 28 | 34 |
| 30 | Cohomology of Schemes | 4 | 6 |
| 31 | Divisors | 6 | 8 |
| 32 | Limits of Schemes | 13 | 49 |
| 33 | Varieties | 1 | 1 |
| 35 | Descent | 11 | 24 |
| 36 | Derived Categories of Schemes | 2 | 2 |
| 37 | More on Morphisms | 22 | 31 |
| 41 | Étale Morphisms of Schemes | 11 | 16 |
| 47 | Dualizing Complexes | 7 | 10 |
| 48 | Duality for Schemes | 6 | 7 |
| 49 | Discriminants and Differents | 2 | 6 |
| 51 | Local Cohomology | 12 | 15 |
| 52 | Algebraic and Formal Geometry | 11 | 12 |
| 54 | Resolution of Surfaces | 8 | 8 |
| 59 | Étale Cohomology | 2 | 2 |
| 95 | Examples of Stacks | 1 | 1 |

### Tag ledger

| Target tag | Owning chapter / section | Referenced from Chapter 58 | Initial use class | Evidence |
|---|---|---|---|---|
| [002O](https://stacks.math.columbia.edu/tag/002O) | Ch. 4 Categories / §4.18 [Finite limits and colimits](https://stacks.math.columbia.edu/tag/04AS) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `mathlib-covered` | `hasFiniteLimits_of_hasEqualizers_and_finite_products` and `hasFiniteLimits_of_hasTerminal_and_pullbacks`; the reverse directions are the finite-shape instances supplied by `HasFiniteLimits`. |
| [002Q](https://stacks.math.columbia.edu/tag/002Q) | Ch. 4 Categories / §4.18 [Finite limits and colimits](https://stacks.math.columbia.edu/tag/04AS) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `mathlib-covered` | `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` and `hasFiniteColimits_of_hasInitial_and_pushouts`; the reverse directions are the finite-shape instances supplied by `HasFiniteColimits`. |
| [002T](https://stacks.math.columbia.edu/tag/002T) | Ch. 4 Categories / §4.16 [Connected limits](https://stacks.math.columbia.edu/tag/04AQ) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `mathlib-covered` | `Over.createsLimitsOfShapeForgetOfIsConnected` and `Over.preservesLimitsOfShape_forget_of_isConnected`. |
| [0035](https://stacks.math.columbia.edu/tag/0035) | Ch. 4 Categories / §4.23 [Exact functors](https://stacks.math.columbia.edu/tag/0033) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×2 | `mathlib-covered` | `preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts` and `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`; converse shape preservation comes from `PreservesFiniteLimits`. |
| [005F](https://stacks.math.columbia.edu/tag/005F) | Ch. 5 Topology / §5.12 [Quasi-compact spaces and maps](https://stacks.math.columbia.edu/tag/0059) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `EtaleFundamentalGroups-required` | `SchemeTheory.connectedComponent_eq_iInter_isClopen_of_prespectral` in `SchemeTheory/Topology/ConnectedComponents.lean` now supplies the exact statement under `CompactSpace`, `PrespectralSpace`, and `QuasiSeparatedSpace`, without a Hausdorff assumption. It is used in the source implementation of 0BQA; static review completed, Lean validation pending. |
| [00D3](https://stacks.math.columbia.edu/tag/00D3) | Ch. 4 Categories / §4.21 [Limits and colimits over preordered sets](https://stacks.math.columbia.edu/tag/002Z) | [58.3 / `0BMQ`](https://stacks.math.columbia.edu/tag/0BMQ) ×1 | `mathlib-covered` | Core `Preorder`, `IsDirectedOrder`, and `[stacks 00D3] Preorder.smallCategory`; no replacement directed-set wrapper is needed. |
| [00FP](https://stacks.math.columbia.edu/tag/00FP) | Ch. 10 Commutative Algebra / §10.31 [Noetherian rings](https://stacks.math.columbia.edu/tag/00FM) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `mathlib-covered` | `Module.finitePresentation_iff_finite`, `isNoetherian_submodule'`, and `Algebra.FinitePresentation.of_finiteType` give the matching finite-generation/finite-presentation result over a Noetherian base. |
| [00FV](https://stacks.math.columbia.edu/tag/00FV) | Ch. 10 Commutative Algebra / §10.34 [Hilbert Nullstellensatz](https://stacks.math.columbia.edu/tag/00FS) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `mathlib-covered` | `RingHom.finite_of_algHom_finiteType_of_isJacobsonRing` is the exact finite-over-the-base conclusion for the Jacobson finite-type situation used here. |
| [00H6](https://stacks.math.columbia.edu/tag/00H6) | Ch. 10 Commutative Algebra / §10.38 [Going down for integral over normal](https://stacks.math.columbia.edu/tag/037E) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×2 | `mathlib-covered` | `Polynomial.isIntegral_coeff_of_dvd` is tagged `[stacks 00H6]` and exactly covers the divisibility/integral-coefficient clause used by Chapter 58. |
| [00H8](https://stacks.math.columbia.edu/tag/00H8) | Ch. 10 Commutative Algebra / §10.38 [Going down for integral over normal](https://stacks.math.columbia.edu/tag/037E) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×2 | `mathlib-covered` | The `[stacks 00H8]` instance in `RingTheory/IntegralClosure/GoingDown` produces `Algebra.HasGoingDown R S` under the matching integral and integrally-closed hypotheses. |
| [00HS](https://stacks.math.columbia.edu/tag/00HS) | Ch. 10 Commutative Algebra / §10.39 [Flat modules and flat ring maps](https://stacks.math.columbia.edu/tag/00H9) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1 | `mathlib-covered` | `Algebra.HasGoingDown.of_flat` is the exact going-down theorem for flat algebras. |
| [00HT](https://stacks.math.columbia.edu/tag/00HT) | Ch. 10 Commutative Algebra / §10.39 [Flat modules and flat ring maps](https://stacks.math.columbia.edu/tag/00H9) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×2 | `mathlib-covered` | `IsLocalization.flat`, `Module.flat_iff_of_isLocalization`, and `Module.flat_of_localized_maximal` give the localization and maximal-local flatness criteria used here. |
| [00IA](https://stacks.math.columbia.edu/tag/00IA) | Ch. 10 Commutative Algebra / §10.50 [Valuation rings](https://stacks.math.columbia.edu/tag/00I8) | [58.16 / `0BUP`](https://stacks.math.columbia.edu/tag/0BUP) ×1 | `mathlib-covered` | `LocalSubring.exists_le_valuationSubring` is the matching existence theorem for a valuation subring dominating a local subring. |
| [00IC](https://stacks.math.columbia.edu/tag/00IC) | Ch. 10 Commutative Algebra / §10.50 [Valuation rings](https://stacks.math.columbia.edu/tag/00I8) | [58.16 / `0BUP`](https://stacks.math.columbia.edu/tag/0BUP) ×1 | `mathlib-covered` | `LocalSubring.mem_of_isMax_of_isIntegral` is the matching maximal-valuation-subring integrality endpoint. |
| [00KW](https://stacks.math.columbia.edu/tag/00KW) | Ch. 10 Commutative Algebra / §10.60 [Dimension](https://stacks.math.columbia.edu/tag/00KD) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1; [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1; [58.22 / `0BLU`](https://stacks.math.columbia.edu/tag/0BLU) ×1 | `mathlib-covered` | `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors` is the exact tagged principal-quotient dimension formula. |
| [00LK](https://stacks.math.columbia.edu/tag/00LK) | Ch. 10 Commutative Algebra / §10.72 [Depth](https://stacks.math.columbia.edu/tag/00LE) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | Mathlib has no depth invariant with the tag's localization/depth behavior; its regular-sequence development explicitly leaves depth as future work. |
| [00MB](https://stacks.math.columbia.edu/tag/00MB) | Ch. 10 Commutative Algebra / §10.97 [Completion for Noetherian rings](https://stacks.math.columbia.edu/tag/0BNH) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `mathlib-covered` | `AdicCompletion.map_exact` and `AdicCompletion.flat_of_isNoetherian` give exactness of completion on finite modules and flatness of the Noetherian adic completion. |
| [00NP](https://stacks.math.columbia.edu/tag/00NP) | Ch. 10 Commutative Algebra / §10.106 [Regular local rings](https://stacks.math.columbia.edu/tag/00NN) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | Mathlib's regular-local API contains the predicate and basic dimension statements, but no endpoint proving the tag's regular-local domain conclusion. |
| [00NQ](https://stacks.math.columbia.edu/tag/00NQ) | Ch. 10 Commutative Algebra / §10.106 [Regular local rings](https://stacks.math.columbia.edu/tag/00NN) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | No public endpoint identifies the quotient of a regular local ring by a regular parameter with the regular-local statement in this tag. |
| [00NU](https://stacks.math.columbia.edu/tag/00NU) | Ch. 10 Commutative Algebra / §10.106 [Regular local rings](https://stacks.math.columbia.edu/tag/00NN) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×2 | `EtaleFundamentalGroups-required` | The required lifting/regular-sequence characterization of regular local rings is absent from mathlib's current regular-local API. |
| [00NX](https://stacks.math.columbia.edu/tag/00NX) | Ch. 10 Commutative Algebra / §10.78 [Finite projective modules](https://stacks.math.columbia.edu/tag/00NV) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `mathlib-covered` | `Module.Flat.projective_of_finitePresentation` and `Module.finitePresentation_of_projective` give the matching finite-projective characterization. |
| [00ON](https://stacks.math.columbia.edu/tag/00ON) | Ch. 10 Commutative Algebra / §10.112 [Homomorphisms and dimension](https://stacks.math.columbia.edu/tag/00OG) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×3 | `mathlib-covered` | `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` is the exact height formula under going down. |
| [00PD](https://stacks.math.columbia.edu/tag/00PD) | Ch. 10 Commutative Algebra / §10.119 [Around Krull-Akizuki](https://stacks.math.columbia.edu/tag/00P7) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `mathlib-covered` | `IsDiscreteValuationRing.TFAE` packages the matching seven-way characterization of discrete valuation rings. |
| [00PH](https://stacks.math.columbia.edu/tag/00PH) | Ch. 10 Commutative Algebra / §10.119 [Around Krull-Akizuki](https://stacks.math.columbia.edu/tag/00P7) | [58.16 / `0BUP`](https://stacks.math.columbia.edu/tag/0BUP) ×1 | `EtaleFundamentalGroups-required` | There is no endpoint constructing a DVR dominating a Noetherian local domain inside the stated finitely generated field extension. |
| [00R4](https://stacks.math.columbia.edu/tag/00R4) | Ch. 10 Commutative Algebra / §10.128 [More flatness criteria](https://stacks.math.columbia.edu/tag/00R3) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | Miracle flatness in this form needs depth and Cohen–Macaulay infrastructure that mathlib does not yet expose. |
| [00U2](https://stacks.math.columbia.edu/tag/00U2) | Ch. 10 Commutative Algebra / §10.143 [Étale ring maps](https://stacks.math.columbia.edu/tag/00U0) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `mathlib-covered` | `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat` and `Algebra.Etale.codescendsAlong_faithfullyFlat` give the exact faithfully-flat descent result. |
| [00U3](https://stacks.math.columbia.edu/tag/00U3) | Ch. 10 Commutative Algebra / §10.143 [Étale ring maps](https://stacks.math.columbia.edu/tag/00U0) | [58.32 / `0G1E`](https://stacks.math.columbia.edu/tag/0G1E) ×1 | `mathlib-covered` | `Algebra.Etale.iff_exists_algEquiv_prod` is the exact classification of étale algebras over a field by finite products of finite separable extensions. |
| [00VK](https://stacks.math.columbia.edu/tag/00VK) | Ch. 7 Sites and Sheaves / §7.6 [Sites](https://stacks.math.columbia.edu/tag/00VG) | [58.2 / `04JI`](https://stacks.math.columbia.edu/tag/04JI) ×1 | `context-only` | §58.2 cites this only to compare terminology for abstract-group actions; mathlib already owns the relevant categories as `Action`, `ContAction`, and `DiscreteContAction`. |
| [01KM](https://stacks.math.columbia.edu/tag/01KM) | Ch. 26 Schemes / §26.21 [Separation axioms](https://stacks.math.columbia.edu/tag/01KH) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1 | `mathlib-covered` | `AlgebraicGeometry.isClosedImmersion_equalizer_ι_left` is the exact separated-target equalizer statement used for the two sections. |
| [01LC](https://stacks.math.columbia.edu/tag/01LC) | Ch. 26 Schemes / §26.24 [Functoriality for quasi-coherent modules](https://stacks.math.columbia.edu/tag/01LA) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | Mathlib only has the affine-morphism pushforward case; the first frontier is that a quasi-compact quasi-separated morphism pushes quasi-coherent modules to quasi-coherent modules. |
| [01LG](https://stacks.math.columbia.edu/tag/01LG) | Ch. 27 Constructions of Schemes / §27.2 [Relative glueing](https://stacks.math.columbia.edu/tag/01LG) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `mathlib-covered` | `Scheme.Cover.RelativeGluingData`, `.glued`, `.toBase`, and `.isPullback_natTrans_ι_toBase` provide the relative gluing construction and pullback squares used here. |
| [01P7](https://stacks.math.columbia.edu/tag/01P7) | Ch. 28 Properties of Schemes / §28.18 [Sections over principal opens](https://stacks.math.columbia.edu/tag/0B5K) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `mathlib-covered` | Chapter 58 uses only the structure-sheaf clause, exactly supplied by `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`; the unused quasi-coherent-module clause is not imported as a dependency. |
| [01QF](https://stacks.math.columbia.edu/tag/01QF) | Ch. 28 Properties of Schemes / §28.28 [Affine and quasi-affine schemes](https://stacks.math.columbia.edu/tag/01QD) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `mathlib-covered` | `AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen` is the exact affine-cover criterion by basic opens. |
| [01RR](https://stacks.math.columbia.edu/tag/01RR) | Ch. 29 Morphisms of Schemes / §29.50 [Rational maps](https://stacks.math.columbia.edu/tag/01RR) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `context-only` | This is the rational-maps section tag; the Chapter 58 occurrence supplies terminology/context and invokes no standalone proposition. |
| [01S4](https://stacks.math.columbia.edu/tag/01S4) | Ch. 29 Morphisms of Schemes / §29.10 [Radicial and universally injective morphisms](https://stacks.math.columbia.edu/tag/01S2) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `mathlib-covered` | `AlgebraicGeometry.tfae_universallyInjective` is the exact equivalence between universal injectivity, radiciality, and the residue-field/topological conditions. |
| [01WJ](https://stacks.math.columbia.edu/tag/01WJ) | Ch. 29 Morphisms of Schemes / §29.45 [Integral and finite morphisms](https://stacks.math.columbia.edu/tag/01WG) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1 | `mathlib-covered` | `AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` is the exact finite iff integral and locally finite type characterization. |
| [01WN](https://stacks.math.columbia.edu/tag/01WN) | Ch. 29 Morphisms of Schemes / §29.45 [Integral and finite morphisms](https://stacks.math.columbia.edu/tag/01WG) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `mathlib-covered` | `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom` is the exact finite iff proper and affine characterization. |
| [01WQ](https://stacks.math.columbia.edu/tag/01WQ) | Ch. 31 Divisors / §31.14 [Effective Cartier divisors](https://stacks.math.columbia.edu/tag/01WQ) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | There is no effective-Cartier-divisor API; the first frontier is the native closed-subscheme definition via an invertible ideal sheaf and its nowhere-dense consequence. |
| [01YV](https://stacks.math.columbia.edu/tag/01YV) | Ch. 32 Limits of Schemes / §32.2 [Directed limits of schemes with affine transition maps](https://stacks.math.columbia.edu/tag/01YV) | [58.14 / `0BTU`](https://stacks.math.columbia.edu/tag/0BTU) ×1 | `context-only` | This is the section-level citation fixing the inverse-limit construction; the finite-presentation and property-descent results actually used are separately inventoried. |
| [01Z4](https://stacks.math.columbia.edu/tag/01Z4) | Ch. 32 Limits of Schemes / §32.4 [Descending properties](https://stacks.math.columbia.edu/tag/081A) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `mathlib-covered` | `exists_preimage_eq`, `exists_map_preimage_eq_map_preimage`, and `exists_isAffineOpen_preimage_eq` in `AffineTransitionLimit` give the exact eventual-preimage statements. |
| [01Z6](https://stacks.math.columbia.edu/tag/01Z6) | Ch. 32 Limits of Schemes / §32.4 [Descending properties](https://stacks.math.columbia.edu/tag/081A) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `mathlib-covered` | `Scheme.exists_isAffine_of_isLimit` is the exact eventual-affineness result. |
| [01ZA](https://stacks.math.columbia.edu/tag/01ZA) | Ch. 32 Limits of Schemes / §32.5 [Absolute Noetherian Approximation](https://stacks.math.columbia.edu/tag/01Z1) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | No endpoint gives absolute Noetherian approximation of an arbitrary quasi-compact quasi-separated scheme; this inverse system over finite-type schemes is the first frontier. |
| [01ZM](https://stacks.math.columbia.edu/tag/01ZM) | Ch. 32 Limits of Schemes / §32.10 [Descending relative objects](https://stacks.math.columbia.edu/tag/01ZL) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×5; [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1; [58.14 / `0BTU`](https://stacks.math.columbia.edu/tag/0BTU) ×1; [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1; [58.30 / `0BUQ`](https://stacks.math.columbia.edu/tag/0BUQ) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×2 | `EtaleFundamentalGroups-required` | `AffineTransitionLimit` factors selected maps and opens, but does not descend a finitely presented relative scheme together with morphisms and eventual equality; that categorical descent theorem is the first frontier. |
| [01ZO](https://stacks.math.columbia.edu/tag/01ZO) | Ch. 32 Limits of Schemes / §32.8 [Descending properties of morphisms](https://stacks.math.columbia.edu/tag/081C) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×5; [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1; [58.14 / `0BTU`](https://stacks.math.columbia.edu/tag/0BTU) ×1; [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | No public theorem makes a descended finite-presentation morphism finite at a sufficiently large stage; this eventual-finiteness statement is the first frontier. |
| [023Q](https://stacks.math.columbia.edu/tag/023Q) | Ch. 35 Descent / §35.13 [Fpqc coverings are universal effective epimorphisms](https://stacks.math.columbia.edu/tag/023P) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1 | `mathlib-covered` | `AlgebraicGeometry.isRegularEpi_of_flat_of_surjective_of_isAffine` exactly covers the single affine faithfully-flat morphism used in §58.10. |
| [0245](https://stacks.math.columbia.edu/tag/0245) | Ch. 35 Descent / §35.37 [Descending affine morphisms](https://stacks.math.columbia.edu/tag/0244) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1 | `EtaleFundamentalGroups-required` | Mathlib has property descent but no category of affine fpqc descent data or effectivity construction; effective affine descent is the first frontier. |
| [024T](https://stacks.math.columbia.edu/tag/024T) | Ch. 41 Étale Morphisms of Schemes / §41.6 [Topological properties of unramified morphisms](https://stacks.math.columbia.edu/tag/024S) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1 | `Pi1-covered` | For the finite étale section used here, `AlgebraicGeometry.IsFiniteEtale.mono_iff` turns the split mono into an open and closed immersion exactly as required. |
| [024V](https://stacks.math.columbia.edu/tag/024V) | Ch. 41 Étale Morphisms of Schemes / §41.6 [Topological properties of unramified morphisms](https://stacks.math.columbia.edu/tag/024S) | [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×1 | `Pi1-covered` | `PreGaloisCategory.evaluation_injective_of_isConnected`, applied through Pi1's finite-étale fiber functor, gives equality of the two maps from a connected component after agreement at one geometric point. |
| [025G](https://stacks.math.columbia.edu/tag/025G) | Ch. 41 Étale Morphisms of Schemes / §41.14 [Topological properties of étale morphisms](https://stacks.math.columbia.edu/tag/025F) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `Pi1-covered` | `AlgebraicGeometry.FiniteEtale.mono_iff` is the exact use-specific endpoint: a monomorphism between finite étale covers is both an open and a closed immersion. |
| [025L](https://stacks.math.columbia.edu/tag/025L) | Ch. 41 Étale Morphisms of Schemes / §41.19 [Permanence properties](https://stacks.math.columbia.edu/tag/025L) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | The étale invariance of local dimension, normality, and regularity used in §58.21 is not packaged at scheme stalks; those three stalkwise transport results form the first frontier. |
| [02G4](https://stacks.math.columbia.edu/tag/02G4) | Ch. 29 Morphisms of Schemes / §29.36 [Unramified morphisms](https://stacks.math.columbia.edu/tag/02G3) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | Mathlib has `FormallyUnramified`, but no scheme-level unramified and G-unramified definitions matching every clause of this tag. |
| [02G7](https://stacks.math.columbia.edu/tag/02G7) | Ch. 29 Morphisms of Schemes / §29.36 [Unramified morphisms](https://stacks.math.columbia.edu/tag/02G3) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1 | `EtaleFundamentalGroups-required` | The classification of an unramified scheme over a field as a disjoint union of spectra of finite separable extensions has no endpoint. |
| [02GI](https://stacks.math.columbia.edu/tag/02GI) | Ch. 29 Morphisms of Schemes / §29.37 [Étale morphisms](https://stacks.math.columbia.edu/tag/02GH) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `mathlib-covered` | `AlgebraicGeometry.Etale` and `Algebra.IsStandardEtale` are the canonical scheme-level and affine standard-étale definitions used by this tag. |
| [02GL](https://stacks.math.columbia.edu/tag/02GL) | Ch. 29 Morphisms of Schemes / §29.37 [Étale morphisms](https://stacks.math.columbia.edu/tag/02GH) | [58.2 / `04JI`](https://stacks.math.columbia.edu/tag/04JI) ×1; [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×2; [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `EtaleFundamentalGroups-required` | `AlgebraicGeometry.Scheme.Etale.exists_iso_sigmaSpec` now classifies an arbitrary étale scheme over a field as a coproduct of spectra of finite separable field extensions. `EtaleFundamentalGroups.SchemesEtaleOverPoint.EtaleDecomposition` is verified by strict `--wfail` build. |
| [02GV](https://stacks.math.columbia.edu/tag/02GV) | Ch. 29 Morphisms of Schemes / §29.37 [Étale morphisms](https://stacks.math.columbia.edu/tag/02GH) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | There is no G-unramified predicate or the tag's equivalence; `Etale.iff_flat_and_formallyUnramified` is a different statement. |
| [02GW](https://stacks.math.columbia.edu/tag/02GW) | Ch. 29 Morphisms of Schemes / §29.37 [Étale morphisms](https://stacks.math.columbia.edu/tag/02GH) | [58.32 / `0G1E`](https://stacks.math.columbia.edu/tag/0G1E) ×1 | `mathlib-covered` | `AlgebraicGeometry.Etale.of_comp` gives the exact cancellation law: a morphism between schemes étale over a common base is étale. |
| [02IM](https://stacks.math.columbia.edu/tag/02IM) | Ch. 28 Properties of Schemes / §28.6 [Jacobson schemes](https://stacks.math.columbia.edu/tag/01P1) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | There is no theorem that the punctured spectrum of the stated Noetherian local ring is Jacobson. |
| [02JU](https://stacks.math.columbia.edu/tag/02JU) | Ch. 29 Morphisms of Schemes / §29.53 [The dimension formula](https://stacks.math.columbia.edu/tag/02JT) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | The dimension formula and its universally-catenary equality case have no scheme-level endpoint. |
| [02JY](https://stacks.math.columbia.edu/tag/02JY) | Ch. 29 Morphisms of Schemes / §29.26 [Flat morphisms](https://stacks.math.columbia.edu/tag/01U2) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `mathlib-covered` | `AlgebraicGeometry.Flat.isQuotientMap_of_surjective` is the exact submersiveness theorem for a surjective quasi-compact flat morphism. |
| [02KB](https://stacks.math.columbia.edu/tag/02KB) | Ch. 29 Morphisms of Schemes / §29.49 [Finite locally free morphisms](https://stacks.math.columbia.edu/tag/02K9) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | Mathlib has finite-projective modules but no finite-locally-free morphism class and affine equivalence matching this tag. |
| [02KH](https://stacks.math.columbia.edu/tag/02KH) | Ch. 30 Cohomology of Schemes / §30.5 [Cohomology and base change, I](https://stacks.math.columbia.edu/tag/02KE) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1; [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | No derived or sheaf-cohomology flat-base-change endpoint exists for a quasi-compact quasi-separated scheme morphism; the stated cohomology isomorphism is the first frontier. |
| [02KU](https://stacks.math.columbia.edu/tag/02KU) | Ch. 35 Descent / §35.23 [Properties of morphisms local in the fpqc topology on the target](https://stacks.math.columbia.edu/tag/02YJ) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `EtaleFundamentalGroups-required` | Mathlib has no `DescendsAlong` endpoint for `IsSeparated` along fpqc covers; exact separatedness descent is the first frontier. |
| [02LA](https://stacks.math.columbia.edu/tag/02LA) | Ch. 35 Descent / §35.23 [Properties of morphisms local in the fpqc topology on the target](https://stacks.math.columbia.edu/tag/02YJ) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×2; [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1 | `EtaleFundamentalGroups-required` | `RingHom.Finite.codescendsAlong_faithfullyFlat` does not descend the affine morphism itself, and there is no scheme-level `DescendsAlong @IsFinite`; exact fpqc descent of finiteness is the first frontier. |
| [02LK](https://stacks.math.columbia.edu/tag/02LK) | Ch. 37 More on Morphisms / §37.41 [Étale localization of quasi-finite morphisms](https://stacks.math.columbia.edu/tag/04HF) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×2 | `EtaleFundamentalGroups-required` | No theorem replaces a locally finite-type morphism near an isolated fibre point by a finite morphism after an elementary étale neighbourhood; that localization theorem is the first frontier. |
| [02LS](https://stacks.math.columbia.edu/tag/02LS) | Ch. 37 More on Morphisms / §37.44 [Applications of Zariski's Main Theorem, I](https://stacks.math.columbia.edu/tag/0F2P) | [58.18 / `0EK3`](https://stacks.math.columbia.edu/tag/0EK3) ×1 | `mathlib-covered` | `AlgebraicGeometry.IsFinite.iff_isProper_and_locallyQuasiFinite` is the exact proper plus locally-quasi-finite implication used in §58.18. |
| [02VN](https://stacks.math.columbia.edu/tag/02VN) | Ch. 35 Descent / §35.23 [Properties of morphisms local in the fpqc topology on the target](https://stacks.math.columbia.edu/tag/02YJ) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1; [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1; [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×2; [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1; [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×2 | `mathlib-covered` | Specializing `HasRingHomProperty.descendsAlong_flat` with `RingHom.Etale.codescendsAlong_faithfullyFlat` is the exact fpqc descent endpoint for étale morphisms. |
| [02W0](https://stacks.math.columbia.edu/tag/02W0) | Ch. 35 Descent / §35.35 [Fully faithfulness of the pullback functors](https://stacks.math.columbia.edu/tag/02VV) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1 | `EtaleFundamentalGroups-required` | `Over.pullback` is only known faithful for fpqc covers; the full-faithfulness theorem for pullback of descent data, needed to descend the comparison isomorphism, is absent. |
| [030C](https://stacks.math.columbia.edu/tag/030C) | Ch. 10 Commutative Algebra / §10.37 [Normal rings](https://stacks.math.columbia.edu/tag/037B) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | Mathlib's `IntegrallyClosed` development explicitly lacks normal rings, the finite-minimal-prime decomposition, and the product-of-normal-domains theorem required here. |
| [0316](https://stacks.math.columbia.edu/tag/0316) | Ch. 10 Commutative Algebra / §10.97 [Completion for Noetherian rings](https://stacks.math.columbia.edu/tag/0BNH) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×1 | `EtaleFundamentalGroups-required` | No declaration supplies `IsNoetherianRing (AdicCompletion I R)` under the tag's hypotheses. |
| [031C](https://stacks.math.columbia.edu/tag/031C) | Ch. 10 Commutative Algebra / §10.97 [Completion for Noetherian rings](https://stacks.math.columbia.edu/tag/0BNH) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×1 | `mathlib-covered` | `AdicCompletion.isAdicComplete`, `AdicCompletion.pow_smul_top_eq_ker_eval`, and `AdicCompletion.eval_surjective` give the matching completion and quotient statements. |
| [031S](https://stacks.math.columbia.edu/tag/031S) | Ch. 10 Commutative Algebra / §10.157 [Serre's criterion for normality](https://stacks.math.columbia.edu/tag/031O) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1; [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1; [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | Serre's normality criterion requires ring-level `(R₁)` and `(S₂)` predicates and their equivalence with normality, which are not present. |
| [0323](https://stacks.math.columbia.edu/tag/0323) | Ch. 10 Commutative Algebra / §10.160 [The Cohen structure theorem](https://stacks.math.columbia.edu/tag/0323) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `context-only` | Chapter 58 cites the Cohen structure theorem section only as a contextual reduction; it does not invoke a proposition from this section as an API dependency. |
| [032L](https://stacks.math.columbia.edu/tag/032L) | Ch. 10 Commutative Algebra / §10.161 [Japanese rings](https://stacks.math.columbia.edu/tag/0BI1) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `mathlib-covered` | `IsIntegralClosure.finite` is the exact finiteness theorem for integral closure in a finite separable extension over a Noetherian integrally closed domain. |
| [0335](https://stacks.math.columbia.edu/tag/0335) | Ch. 10 Commutative Algebra / §10.162 [Nagata rings](https://stacks.math.columbia.edu/tag/032E) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | Nagata rings and the finite-normalization characterization used by this tag have no mathlib predicate or theorem. |
| [0337](https://stacks.math.columbia.edu/tag/0337) | Ch. 10 Commutative Algebra / §10.163 [Ascending properties](https://stacks.math.columbia.edu/tag/0336) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1; [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×3; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | The ascending depth formula in this tag has no endpoint because the required depth API is absent. |
| [0339](https://stacks.math.columbia.edu/tag/0339) | Ch. 10 Commutative Algebra / §10.163 [Ascending properties](https://stacks.math.columbia.edu/tag/0336) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | Mathlib has no Serre `(S_k)` condition matching the tag's ascending-property statement. |
| [033C](https://stacks.math.columbia.edu/tag/033C) | Ch. 10 Commutative Algebra / §10.163 [Ascending properties](https://stacks.math.columbia.edu/tag/0336) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | The theorem that a smooth algebra over a normal ring is normal is blocked by the absence of a general normal-ring predicate and endpoint. |
| [033M](https://stacks.math.columbia.edu/tag/033M) | Ch. 28 Properties of Schemes / §28.7 [Normal schemes](https://stacks.math.columbia.edu/tag/033H) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `EtaleFundamentalGroups-required` | Normal schemes and the decomposition of a Noetherian normal scheme into finitely many normal integral components are not formalized. |
| [034F](https://stacks.math.columbia.edu/tag/034F) | Ch. 35 Descent / §35.18 [Properties of schemes local in the smooth topology](https://stacks.math.columbia.edu/tag/034D) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×2; [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1; [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `EtaleFundamentalGroups-required` | Normal schemes and smooth-local descent of normality are not available; the first frontier is the exact smooth-cover descent theorem for normality. |
| [0357](https://stacks.math.columbia.edu/tag/0357) | Ch. 28 Properties of Schemes / §28.7 [Normal schemes](https://stacks.math.columbia.edu/tag/033H) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×2; [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | The locally-finite-component decomposition of a normal scheme into normal integral open-and-closed pieces has no endpoint. |
| [035D](https://stacks.math.columbia.edu/tag/035D) | Ch. 29 Morphisms of Schemes / §29.45 [Integral and finite morphisms](https://stacks.math.columbia.edu/tag/01WG) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `mathlib-covered` | `AlgebraicGeometry.IsFinite.of_comp` and `AlgebraicGeometry.IsIntegralHom.of_comp` give the two exact cancellation clauses under separatedness. |
| [035I](https://stacks.math.columbia.edu/tag/035I) | Ch. 29 Morphisms of Schemes / §29.54 [Relative normalization](https://stacks.math.columbia.edu/tag/0BAK) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1; [58.15 / `0BUM`](https://stacks.math.columbia.edu/tag/0BUM) ×1 | `mathlib-covered` | `Scheme.Hom.normalization`, `toNormalization`, `fromNormalization`, `normalizationDesc`, `toNormalization_normalizationDesc`, `normalizationDesc_comp`, and `normalization.hom_ext` implement the relative-normalization factorization and its exact universal property. |
| [035J](https://stacks.math.columbia.edu/tag/035J) | Ch. 29 Morphisms of Schemes / §29.54 [Relative normalization](https://stacks.math.columbia.edu/tag/0BAK) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | `normalizationDesc` handles one same-base factorization, but there is no canonical functorial relative-normalization morphism for the full commutative square in this tag. |
| [035L](https://stacks.math.columbia.edu/tag/035L) | Ch. 29 Morphisms of Schemes / §29.54 [Relative normalization](https://stacks.math.columbia.edu/tag/0BAK) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | The normality and irreducible-component conclusions for relative normalization have no endpoint because normal-scheme infrastructure is absent. |
| [036W](https://stacks.math.columbia.edu/tag/036W) | Ch. 35 Descent / §35.31 [Properties of morphisms local in the étale topology on the source](https://stacks.math.columbia.edu/tag/036V) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×2 | `EtaleFundamentalGroups-required` | Étaleness is Zariski-local on the source in mathlib, but no étale-local-on-source endpoint exists; that locality theorem is the first frontier. |
| [0383](https://stacks.math.columbia.edu/tag/0383) | Ch. 29 Morphisms of Schemes / §29.24 [Open morphisms](https://stacks.math.columbia.edu/tag/01TZ) | [58.14 / `0BTU`](https://stacks.math.columbia.edu/tag/0BTU) ×1 | `EtaleFundamentalGroups-required` | `UniversallyOpen.of_flat` requires finite presentation; it does not prove that an arbitrary scheme structure morphism to a field is universally open. |
| [038B](https://stacks.math.columbia.edu/tag/038B) | Ch. 33 Varieties / §33.7 [Geometrically connected schemes](https://stacks.math.columbia.edu/tag/0361) | [58.14 / `0BTU`](https://stacks.math.columbia.edu/tag/0BTU) ×1 | `EtaleFundamentalGroups-required` | No theorem descends a Galois-stable closed subset of a base change to the original scheme; this closed-subset descent statement is the first frontier. |
| [039R](https://stacks.math.columbia.edu/tag/039R) | Ch. 41 Étale Morphisms of Schemes / §41.15 [Topological invariance of the étale topology](https://stacks.math.columbia.edu/tag/06NE) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1; [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×2 | `EtaleFundamentalGroups-required` | No equivalence of categories of étale schemes across a finite-order nilpotent thickening is exposed; topological invariance for such thickenings is the first frontier. |
| [03C4](https://stacks.math.columbia.edu/tag/03C4) | Ch. 10 Commutative Algebra / §10.83 [Descent for finite projective modules](https://stacks.math.columbia.edu/tag/058Q) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `mathlib-covered` | `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` give the matching faithful-flat descent clauses. |
| [03GG](https://stacks.math.columbia.edu/tag/03GG) | Ch. 10 Commutative Algebra / §10.147 [Integral closure and smooth base change](https://stacks.math.columbia.edu/tag/03GC) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1; [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `mathlib-covered` | `TensorProduct.toIntegralClosure_bijective_of_smooth` is the exact integral-closure/smooth-base-change comparison. |
| [03GR](https://stacks.math.columbia.edu/tag/03GR) | Ch. 29 Morphisms of Schemes / §29.54 [Relative normalization](https://stacks.math.columbia.edu/tag/0BAK) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | Finiteness of normalization over a Nagata base is absent because Nagata and normal-scheme APIs are missing. |
| [03GV](https://stacks.math.columbia.edu/tag/03GV) | Ch. 37 More on Morphisms / §37.19 [Normalization revisited](https://stacks.math.columbia.edu/tag/081J) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1; [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `mathlib-covered` | The `[Smooth g] : IsIso (f.normalizationPullback g)` instance is the exact normalization-under-smooth-base-change comparison. |
| [03GY](https://stacks.math.columbia.edu/tag/03GY) | Ch. 37 More on Morphisms / §37.53 [Stein factorization](https://stacks.math.columbia.edu/tag/03GX) | [58.15 / `0BUM`](https://stacks.math.columbia.edu/tag/0BUM) ×1 | `EtaleFundamentalGroups-required` | The native relative normalization now has its structure-sheaf pushforward isomorphism over an arbitrary base, the actual cartesian first-map square under flat base change, and the normalization comparison isomorphism for affine flat base change. The remaining Stein fibre properties are still in progress. |
| [03H2](https://stacks.math.columbia.edu/tag/03H2) | Ch. 37 More on Morphisms / §37.53 [Stein factorization](https://stacks.math.columbia.edu/tag/03GX) | [58.15 / `0BUM`](https://stacks.math.columbia.edu/tag/0BUM) ×2 | `EtaleFundamentalGroups-required` | The actual first normalization map is proper, with its structure-sheaf pushforward isomorphism over an arbitrary base. Geometric connectedness of its fibres remains open. |
| [03HV](https://stacks.math.columbia.edu/tag/03HV) | Ch. 29 Morphisms of Schemes / §29.26 [Flat morphisms](https://stacks.math.columbia.edu/tag/01U2) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1 | `EtaleFundamentalGroups-required` | The lifting-of-generalizations theorem for flat morphisms is not exposed as a scheme-level endpoint with the tag's conclusion. |
| [03PN](https://stacks.math.columbia.edu/tag/03PN) | Ch. 59 Étale Cohomology / §59.29 [Neighborhoods, stalks and points](https://stacks.math.columbia.edu/tag/03PN) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `context-only` | This occurrence only fixes geometric-point and étale-neighbourhood terminology; Pi1 represents the base point directly as a morphism from the spectrum of a separably closed field. |
| [03WS](https://stacks.math.columbia.edu/tag/03WS) | Ch. 29 Morphisms of Schemes / §29.37 [Étale morphisms](https://stacks.math.columbia.edu/tag/02GH) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `EtaleFundamentalGroups-required` | No scheme-level theorem states that an étale morphism is locally quasi-finite in the exact sense of this tag. |
| [0476](https://stacks.math.columbia.edu/tag/0476) | Ch. 29 Morphisms of Schemes / §29.37 [Étale morphisms](https://stacks.math.columbia.edu/tag/02GH) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×2 | `EtaleFundamentalGroups-required` | `etale_isStableUnderBaseChange` gives only preservation; no endpoint proves equality of the two étale loci under the tag's flat and locally-finite-presentation hypotheses. |
| [04AX](https://stacks.math.columbia.edu/tag/04AX) | Ch. 4 Categories / §4.19 [Filtered colimits](https://stacks.math.columbia.edu/tag/04AX) | [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×2 | `context-only` | Chapter 58 cites a section-level convention for filtered colimits, not a standalone proposition; mathlib uses `IsFiltered` and `colimit` directly. |
| [04D1](https://stacks.math.columbia.edu/tag/04D1) | Ch. 10 Commutative Algebra / §10.143 [Étale ring maps](https://stacks.math.columbia.edu/tag/00U0) | [58.32 / `0G1E`](https://stacks.math.columbia.edu/tag/0G1E) ×1 | `EtaleFundamentalGroups-required` | `Algebra.Etale.exists_etale_lift_of_quotient` in `SchemeTheory/FiniteEtale/Algebra/EtaleQuotientLift.lean` constructs an etale algebra over the original ring and its quotient-base-change algebra equivalence, for an arbitrary ideal. The proof lifts relations and localizes at the Jacobian. This tag asserts existence; finiteness as a module and uniqueness are not asserted. Independently source-reviewed, Lean validation pending. |
| [04DF](https://stacks.math.columbia.edu/tag/04DF) | Ch. 29 Morphisms of Schemes / §29.46 [Universal homeomorphisms](https://stacks.math.columbia.edu/tag/04DC) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `EtaleFundamentalGroups-required` | Mathlib defines integral, universally injective, and surjective morphisms, but has no universal-homeomorphism property or exact equivalence with their conjunction. |
| [04DH](https://stacks.math.columbia.edu/tag/04DH) | Ch. 41 Étale Morphisms of Schemes / §41.14 [Topological properties of étale morphisms](https://stacks.math.columbia.edu/tag/025F) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×2 | `EtaleFundamentalGroups-required` | Source implementation in SchemeTheory.Etale.IsomorphismNeighborhood: a finite etale singleton fiber with purely inseparable residue extension has an actual open isomorphism neighborhood. The proof uses the rank-one locus and the residue-field fiber point. Independently statically reviewed; Lean/Lake validation remains pending. |
| [04DZ](https://stacks.math.columbia.edu/tag/04DZ) | Ch. 59 Étale Cohomology / §59.45 [Topological invariance of the small étale site](https://stacks.math.columbia.edu/tag/04DY) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `context-only` | Chapter 58 explicitly cites this only as an alternative 'correct way' to prove topological invariance and then gives an independent proof; it is not a proof dependency. |
| [04EW](https://stacks.math.columbia.edu/tag/04EW) | Ch. 37 More on Morphisms / §37.2 [Thickenings](https://stacks.math.columbia.edu/tag/04EW) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `context-only` | This is the section-level terminology citation for thickenings; the substantive finite-order transport theorem is separately represented by `0BPG` and the general result is proved inside Chapter 58. |
| [04GF](https://stacks.math.columbia.edu/tag/04GF) | Ch. 10 Commutative Algebra / §10.153 [Henselian local rings](https://stacks.math.columbia.edu/tag/04GE) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×1 | `EtaleFundamentalGroups-required` | `HenselianLocalRing` covers henselian local rings, but mathlib has no strict-henselian predicate or the tag's combined definitions. |
| [04GG](https://stacks.math.columbia.edu/tag/04GG) | Ch. 10 Commutative Algebra / §10.153 [Henselian local rings](https://stacks.math.columbia.edu/tag/04GE) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | `HenselianLocalRing.TFAE` contains only three root-lifting formulations, not the tag's thirteen equivalent factorization and finite-algebra conditions. |
| [04GK](https://stacks.math.columbia.edu/tag/04GK) | Ch. 10 Commutative Algebra / §10.153 [Henselian local rings](https://stacks.math.columbia.edu/tag/04GE) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | There is no equivalence between finite étale algebras over a henselian local ring and over its residue field. |
| [04GQ](https://stacks.math.columbia.edu/tag/04GQ) | Ch. 10 Commutative Algebra / §10.155 [Henselization and strict henselization](https://stacks.math.columbia.edu/tag/0BSK) | [58.16 / `0BUP`](https://stacks.math.columbia.edu/tag/0BUP) ×1 | `EtaleFundamentalGroups-required` | A henselization object with the tag's local universal property is not defined in mathlib. |
| [04GS](https://stacks.math.columbia.edu/tag/04GS) | Ch. 10 Commutative Algebra / §10.155 [Henselization and strict henselization](https://stacks.math.columbia.edu/tag/0BSK) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | Strict henselization and its universal property are absent. |
| [04GU](https://stacks.math.columbia.edu/tag/04GU) | Ch. 10 Commutative Algebra / §10.155 [Henselization and strict henselization](https://stacks.math.columbia.edu/tag/0BSK) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×2; [58.16 / `0BUP`](https://stacks.math.columbia.edu/tag/0BUP) ×2 | `EtaleFundamentalGroups-required` | Functoriality and comparison maps for henselizations and strict henselizations are absent because those objects are not yet available. |
| [04HJ](https://stacks.math.columbia.edu/tag/04HJ) | Ch. 41 Étale Morphisms of Schemes / §41.17 [Étale local structure of unramified morphisms](https://stacks.math.columbia.edu/tag/04HG) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1 | `EtaleFundamentalGroups-required` | No étale-local decomposition of a finite unramified morphism into a disjoint union of closed immersions exists; that decomposition is the first frontier. |
| [04HN](https://stacks.math.columbia.edu/tag/04HN) | Ch. 41 Étale Morphisms of Schemes / §41.18 [Étale local structure of étale morphisms](https://stacks.math.columbia.edu/tag/04HK) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×2; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | No theorem trivializes a finite étale morphism as finitely many copies after an étale neighbourhood; this central local-triviality result is the first frontier. |
| [051N](https://stacks.math.columbia.edu/tag/051N) | Ch. 10 Commutative Algebra / §10.115 [Noether normalization](https://stacks.math.columbia.edu/tag/00OW) | [58.32 / `0G1E`](https://stacks.math.columbia.edu/tag/0G1E) ×1 | `EtaleFundamentalGroups-required` | Mathlib's Noether normalization construction is field-based and its coordinate transform is private; the tag's arbitrary-ring leading-coefficient theorem has no endpoint. |
| [055K](https://stacks.math.columbia.edu/tag/055K) | Ch. 37 More on Morphisms / §37.29 [Connected components meeting a section](https://stacks.math.columbia.edu/tag/055K) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `context-only` | This is the situation and notation for the fibrewise connected component meeting a section; the substantive openness theorem is separately recorded as `055R`. |
| [055R](https://stacks.math.columbia.edu/tag/055R) | Ch. 37 More on Morphisms / §37.29 [Connected components meeting a section](https://stacks.math.columbia.edu/tag/055K) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | No endpoint proves that the fibrewise connected component meeting a section is open for a flat finitely-presented morphism with geometrically reduced fibres; that openness theorem is the first frontier. |
| [0567](https://stacks.math.columbia.edu/tag/0567) | Ch. 10 Commutative Algebra / §10.157 [Serre's criterion for normality](https://stacks.math.columbia.edu/tag/031O) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×2; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | There is no theorem that a regular ring is normal in the tag's generality; general normal-ring infrastructure is missing. |
| [057G](https://stacks.math.columbia.edu/tag/057G) | Ch. 37 More on Morphisms / §37.38 [Slicing smooth morphisms](https://stacks.math.columbia.edu/tag/055S) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | There is no slicing theorem producing an étale locally closed subscheme through a smooth closed fibre point with separable residue extension; this slice is the first frontier. |
| [05B5](https://stacks.math.columbia.edu/tag/05B5) | Ch. 35 Descent / §35.14 [Descent of finiteness and smoothness properties of morphisms](https://stacks.math.columbia.edu/tag/02KJ) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×1 | `EtaleFundamentalGroups-required` | No descent theorem transfers smoothness or étaleness from a surjective flat locally-finitely-presented source over the base to the target; that two-out-of-three statement is the first frontier. |
| [05D5](https://stacks.math.columbia.edu/tag/05D5) | Ch. 10 Commutative Algebra / §10.139 [Smoothness and differentials](https://stacks.math.columbia.edu/tag/05D4) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | `Algebra.FormallySmooth.exists_kerProj_comp_eq_id` gives only a section; the finite-locally-free conormal module and completed power-series isomorphism are absent. |
| [05EC](https://stacks.math.columbia.edu/tag/05EC) | Ch. 15 More on Algebra / §15.91 [Formal glueing of module categories](https://stacks.math.columbia.edu/tag/05E5) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | The formal-gluing module category and its comparison functor are not present in mathlib. |
| [05EL](https://stacks.math.columbia.edu/tag/05EL) | Ch. 15 More on Algebra / §15.91 [Formal glueing of module categories](https://stacks.math.columbia.edu/tag/05E5) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | No endpoint proves the stated full-faithfulness/equivalence clause for formal gluing of module categories. |
| [05ER](https://stacks.math.columbia.edu/tag/05ER) | Ch. 15 More on Algebra / §15.91 [Formal glueing of module categories](https://stacks.math.columbia.edu/tag/05E5) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | The tag's finite-module formal-gluing equivalence has no matching categorical construction or theorem. |
| [05EU](https://stacks.math.columbia.edu/tag/05EU) | Ch. 15 More on Algebra / §15.91 [Formal glueing of module categories](https://stacks.math.columbia.edu/tag/05E5) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | The finite-projective/formal-gluing compatibility in this tag is absent. |
| [05K0](https://stacks.math.columbia.edu/tag/05K0) | Ch. 37 More on Morphisms / §37.43 [Zariski's Main Theorem](https://stacks.math.columbia.edu/tag/02LQ) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | Mathlib has algebraic Zariski Main Theorem, but not the scheme factorization of a separated quasi-finite morphism as a quasi-compact open immersion followed by a finite morphism. |
| [05N9](https://stacks.math.columbia.edu/tag/05N9) | Ch. 10 Commutative Algebra / §10.127 [Colimits and maps of finite presentation](https://stacks.math.columbia.edu/tag/00QL) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | `CommRingCat.preservesColimit_coyoneda_of_finitePresentation` gives Hom factorization, but not descent of a finitely presented algebra object together with its base-change isomorphism. |
| [05WS](https://stacks.math.columbia.edu/tag/05WS) | Ch. 10 Commutative Algebra / §10.156 [Henselization and quasi-finite ring maps](https://stacks.math.columbia.edu/tag/0GIN) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | Strict henselization itself and the theorem identifying its quotient by the extended ideal are absent. |
| [0662](https://stacks.math.columbia.edu/tag/0662) | Ch. 15 More on Algebra / §15.63 [Spectral sequences for Tor](https://stacks.math.columbia.edu/tag/061Y) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | Mathlib has Tor and spectral-sequence machinery, but no derived-tensor Tor spectral sequence with the hypotheses and abutment of this tag. |
| [06DI](https://stacks.math.columbia.edu/tag/06DI) | Ch. 15 More on Algebra / §15.46 [Permanence of properties under henselization](https://stacks.math.columbia.edu/tag/07QL) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1; [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×2 | `EtaleFundamentalGroups-required` | Normality under henselization and strict henselization has no endpoint; strict henselization and general normal-ring infrastructure are missing. |
| [06DM](https://stacks.math.columbia.edu/tag/06DM) | Ch. 15 More on Algebra / §15.108 [Local irreducibility](https://stacks.math.columbia.edu/tag/06DT) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×2 | `EtaleFundamentalGroups-required` | Geometric unibranchness and the minimal-prime characterization of strict henselization are not formalized. |
| [06LN](https://stacks.math.columbia.edu/tag/06LN) | Ch. 15 More on Algebra / §15.46 [Permanence of properties under henselization](https://stacks.math.columbia.edu/tag/07QL) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | The regularity equivalence for a local ring, its henselization, and its strict henselization is absent. |
| [07ED](https://stacks.math.columbia.edu/tag/07ED) | Ch. 15 More on Algebra / §15.38 [Formally smooth maps of topological rings](https://stacks.math.columbia.edu/tag/07EA) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | No theorem equates formal smoothness before and after completion for the topological rings in this tag. |
| [07GC](https://stacks.math.columbia.edu/tag/07GC) | Ch. 16 Smoothing Ring Maps / §16.12 [The main theorem](https://stacks.math.columbia.edu/tag/07GB) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | Popescu's theorem is absent; the first frontier is the filtered smooth-algebra presentation of a regular homomorphism of Noetherian rings. |
| [07NE](https://stacks.math.columbia.edu/tag/07NE) | Ch. 10 Commutative Algebra / §10.159 [Constructing flat ring maps](https://stacks.math.columbia.edu/tag/03C2) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | No endpoint constructs the finite free local algebra realizing an arbitrary finite residue-field extension with the stated properties. |
| [07NU](https://stacks.math.columbia.edu/tag/07NU) | Ch. 15 More on Algebra / §15.44 [Permanence of properties under completion](https://stacks.math.columbia.edu/tag/07NU) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `context-only` | Chapter 58 cites this section only for the surrounding permanence-under-completion discussion; the actual flatness fact is owned by the Chapter 10 completion endpoint. |
| [07NV](https://stacks.math.columbia.edu/tag/07NV) | Ch. 15 More on Algebra / §15.44 [Permanence of properties under completion](https://stacks.math.columbia.edu/tag/07NU) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | The Krull-dimension equality between a Noetherian local ring and its completion has no matching endpoint. |
| [07NW](https://stacks.math.columbia.edu/tag/07NW) | Ch. 15 More on Algebra / §15.44 [Permanence of properties under completion](https://stacks.math.columbia.edu/tag/07NU) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | The completion/depth equality is blocked by the absence of a depth invariant. |
| [07PM](https://stacks.math.columbia.edu/tag/07PM) | Ch. 15 More on Algebra / §15.50 [Formal smoothness and regularity](https://stacks.math.columbia.edu/tag/07PK) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | The equivalence between a regular local homomorphism, flatness with geometrically regular fibres, and formal smoothness is not packaged in mathlib. |
| [07PX](https://stacks.math.columbia.edu/tag/07PX) | Ch. 15 More on Algebra / §15.51 [G-rings](https://stacks.math.columbia.edu/tag/07GG) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×2 | `EtaleFundamentalGroups-required` | G-rings and geometrically regular formal fibres are not defined as the tag requires. |
| [07QR](https://stacks.math.columbia.edu/tag/07QR) | Ch. 15 More on Algebra / §15.51 [G-rings](https://stacks.math.columbia.edu/tag/07GG) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×1 | `EtaleFundamentalGroups-required` | The localization and permanence criteria for G-rings have no endpoint because the G-ring predicate is absent. |
| [07QU](https://stacks.math.columbia.edu/tag/07QU) | Ch. 15 More on Algebra / §15.53 [Excellent rings](https://stacks.math.columbia.edu/tag/07QS) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | Excellent and quasi-excellent rings are not represented by matching predicates or theorems. |
| [07QY](https://stacks.math.columbia.edu/tag/07QY) | Ch. 16 Smoothing Ring Maps / §16.13 [The approximation property for G-rings](https://stacks.math.columbia.edu/tag/07QX) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×1 | `EtaleFundamentalGroups-required` | Artin approximation over a henselian G-ring is not formalized; approximate lifting of a formal polynomial solution is the first frontier. |
| [07RB](https://stacks.math.columbia.edu/tag/07RB) | Ch. 4 Categories / §4.24 [Adjoint functors](https://stacks.math.columbia.edu/tag/0036) | [58.15 / `0BUM`](https://stacks.math.columbia.edu/tag/0BUM) ×1 | `mathlib-covered` | `Adjunction.unit_isIso_of_L_fully_faithful`, `Adjunction.fullyFaithfulLOfIsIsoUnit`, and the counit duals `counit_isIso_of_R_fully_faithful` and `fullyFaithfulROfIsIsoCounit`. |
| [07RP](https://stacks.math.columbia.edu/tag/07RP) | Ch. 32 Limits of Schemes / §32.8 [Descending properties of morphisms](https://stacks.math.columbia.edu/tag/081C) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×5; [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1; [58.14 / `0BTU`](https://stacks.math.columbia.edu/tag/0BTU) ×1; [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | No public theorem makes a descended locally-finitely-presented morphism étale at a sufficiently large inverse-system stage; eventual étaleness is the first frontier. |
| [07VB](https://stacks.math.columbia.edu/tag/07VB) | Ch. 5 Topology / §5.7 [Connected components](https://stacks.math.columbia.edu/tag/004R) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1; [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×1 | `mathlib-covered` | `[stacks 07VB] IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`, with `IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace` for finiteness. |
| [081F](https://stacks.math.columbia.edu/tag/081F) | Ch. 32 Limits of Schemes / §32.13 [Applications of Chow's lemma](https://stacks.math.columbia.edu/tag/0204) | [58.30 / `0BUQ`](https://stacks.math.columbia.edu/tag/0BUQ) ×1 | `EtaleFundamentalGroups-required` | No public theorem makes a descended finite-type morphism proper at a sufficiently large inverse-system stage; eventual properness is the first frontier. |
| [081I](https://stacks.math.columbia.edu/tag/081I) | Ch. 29 Morphisms of Schemes / §29.26 [Flat morphisms](https://stacks.math.columbia.edu/tag/01U2) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | `Scheme.Hom.image` exists, but there is no theorem that scheme-theoretic image of a quasi-compact morphism commutes with flat base change. |
| [086J](https://stacks.math.columbia.edu/tag/086J) | Ch. 4 Categories / §4.21 [Limits and colimits over preordered sets](https://stacks.math.columbia.edu/tag/002Z) | [58.3 / `0BMQ`](https://stacks.math.columbia.edu/tag/0BMQ) ×2 | `mathlib-covered` | `nonempty_sections_of_finite_cofiltered_system` and its directed-poset specialization `nonempty_sections_of_finite_inverse_system`. |
| [089W](https://stacks.math.columbia.edu/tag/089W) | Ch. 30 Cohomology of Schemes / §30.2 [Čech cohomology of quasi-coherent sheaves](https://stacks.math.columbia.edu/tag/01X8) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | Mathlib has sheaf cohomology machinery but no affine-morphism comparison `Hⁱ(X,F) ≅ Hⁱ(S,f_*F)` for quasi-coherent `F`; that comparison is the first frontier. |
| [08HR](https://stacks.math.columbia.edu/tag/08HR) | Ch. 10 Commutative Algebra / §10.154 [Filtered colimits of étale ring maps](https://stacks.math.columbia.edu/tag/0BSG) | [58.16 / `0BUP`](https://stacks.math.columbia.edu/tag/0BUP) ×1 | `EtaleFundamentalGroups-required` | The universal mapping property from an ind-étale algebra to a henselian local ring has no public declaration. |
| [08IB](https://stacks.math.columbia.edu/tag/08IB) | Ch. 36 Derived Categories of Schemes / §36.22 [Cohomology and base change, IV](https://stacks.math.columbia.edu/tag/08ET) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | No derived quasi-coherent base-change theorem identifies `Lg* Rf*` with `Rf'* Lg'*` under Tor independence; this derived comparison is the first frontier. |
| [08YE](https://stacks.math.columbia.edu/tag/08YE) | Ch. 5 Topology / §5.17 [Characterizing proper maps](https://stacks.math.columbia.edu/tag/005M) | [58.3 / `0BMQ`](https://stacks.math.columbia.edu/tag/0BMQ) ×1; [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `mathlib-covered` | `isHomeomorph_iff_continuous_bijective` has exactly `[CompactSpace X] [T2Space Y]` and concludes a continuous bijection is a homeomorphism. |
| [08Z5](https://stacks.math.columbia.edu/tag/08Z5) | Ch. 47 Dualizing Complexes / §47.7 [Injective hull of the residue field](https://stacks.math.columbia.edu/tag/08Z1) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | There is no theorem identifying injective hulls of the residue field across the stated flat local map; that injective-hull transport is the first frontier. |
| [0900](https://stacks.math.columbia.edu/tag/0900) | Ch. 5 Topology / §5.22 [Profinite spaces](https://stacks.math.columbia.edu/tag/08ZW) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `EtaleFundamentalGroups-required` | The spectral case needed by 0BQA is now supplied by `SchemeTheory.t2Space_connectedComponents_of_prespectral` together with native compactness and total disconnectedness of `ConnectedComponents`. The original space need not be Hausdorff. This is a source implementation for the required use, with static review only and Lean validation pending; no claim is made here for the tag under more general hypotheses. |
| [094L](https://stacks.math.columbia.edu/tag/094L) | Ch. 28 Properties of Schemes / §28.2 [Constructible sets](https://stacks.math.columbia.edu/tag/054B) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `mathlib-covered` | The scheme instances `T0Space`, `QuasiSober`, and `PrespectralSpace` in `AlgebraicGeometry.Properties`, together with quasi-compactness and quasi-separatedness, infer the exact `SpectralSpace` conclusion. |
| [09E3](https://stacks.math.columbia.edu/tag/09E3) | Ch. 15 More on Algebra / §15.114 [Galois extensions and ramification](https://stacks.math.columbia.edu/tag/09E3) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×2 | `context-only` | This is the owning section tag for the ramification discussion; Chapter 58's propositional dependencies are the specific lemmas separately listed below. |
| [09E8](https://stacks.math.columbia.edu/tag/09E8) | Ch. 15 More on Algebra / §15.113 [Extensions of discrete valuation rings](https://stacks.math.columbia.edu/tag/0EXQ) | [58.30 / `0BUQ`](https://stacks.math.columbia.edu/tag/0BUQ) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | `Ideal.sum_ramification_inertia` gives the numerical identity, but no theorem makes the integral closure of a henselian DVR local with the unique prime required by the tag. |
| [09E9](https://stacks.math.columbia.edu/tag/09E9) | Ch. 15 More on Algebra / §15.113 [Extensions of discrete valuation rings](https://stacks.math.columbia.edu/tag/0EXQ) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | CFT has unramified and totally ramified valued extensions, but no tame-ramification definition and equivalences matching this tag. |
| [09EB](https://stacks.math.columbia.edu/tag/09EB) | Ch. 15 More on Algebra / §15.114 [Galois extensions and ramification](https://stacks.math.columbia.edu/tag/09E3) | [58.30 / `0BUQ`](https://stacks.math.columbia.edu/tag/0BUQ) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `mathlib-covered` | `Ideal.ramificationIdxIn_eq_ramificationIdx`, `Ideal.inertiaDegIn_eq_inertiaDeg`, and `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` give the exact Galois constancy and fundamental identity. |
| [09EE](https://stacks.math.columbia.edu/tag/09EE) | Ch. 15 More on Algebra / §15.114 [Galois extensions and ramification](https://stacks.math.columbia.edu/tag/09E3) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | The wild-inertia p-group, cyclic tame quotient, and root-of-unity action package has no exact endpoint in mathlib or CFT. |
| [09EH](https://stacks.math.columbia.edu/tag/09EH) | Ch. 15 More on Algebra / §15.114 [Galois extensions and ramification](https://stacks.math.columbia.edu/tag/09E3) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×1 | `EtaleFundamentalGroups-required` | CFT's `fixedFieldOfSubgroup_forall_isUnramifiedAt_of_inertiaGroup_le` is only a field statement; the invariant integral closure and localized-étale conclusion are absent. |
| [09EV](https://stacks.math.columbia.edu/tag/09EV) | Ch. 15 More on Algebra / §15.116 [Abhyankar's lemma and tame ramification](https://stacks.math.columbia.edu/tag/0EXT) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×2 | `EtaleFundamentalGroups-required` | No endpoint constructs the ramified root-of-uniformizer extension and proves all DVR, degree, and ramification properties stated here. |
| [09H1](https://stacks.math.columbia.edu/tag/09H1) | Ch. 9 Fields / §9.12 [Separable algebraic extensions](https://stacks.math.columbia.edu/tag/09GZ) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×2 | `mathlib-covered` | Exact tagged declarations: `[stacks 09H1] Polynomial.Separable`, `_root_.IsSeparable`, and `Algebra.IsSeparable`. |
| [09IJ](https://stacks.math.columbia.edu/tag/09IJ) | Ch. 37 More on Morphisms / §37.65 [Reduced fibre theorem](https://stacks.math.columbia.edu/tag/09IJ) | [58.30 / `0BUQ`](https://stacks.math.columbia.edu/tag/0BUQ) ×1 | `EtaleFundamentalGroups-required` | The alteration-style generic smoothing theorem over a Nagata Dedekind ring has no endpoint; constructing the finite extension and normalized smooth base change is the first frontier. |
| [09PY](https://stacks.math.columbia.edu/tag/09PY) | Ch. 23 Divided Power Algebra / §23.8 [Local complete intersection rings](https://stacks.math.columbia.edu/tag/09PY) | [58.25 / `0BPB`](https://stacks.math.columbia.edu/tag/0BPB) ×1 | `EtaleFundamentalGroups-required` | No complete-intersection invariance theorem compares kernels of different regular-local presentations of a complete Noetherian local ring; that presentation-independence is the first frontier. |
| [09XI](https://stacks.math.columbia.edu/tag/09XI) | Ch. 15 More on Algebra / §15.11 [Henselian pairs](https://stacks.math.columbia.edu/tag/09XD) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | Mathlib defines general henselian pairs through `HenselianRing R I`. `JacobsonIntegral`, `JacobsonRigidity`, and `JacobsonConservativity` supply the radical, uniqueness, and finite-isomorphism detection steps. `Normalization.QuotientFiniteFactor` constructs the actual integral-closure quotient factor and localization for quasi-finite finite-type algebras. `HenselianCyclicIdempotent` lifts quotient idempotents with cyclic components using the native axiom and a determinant-trick annihilator. `IntegralLocalizationIdempotentModel` supplies finite integral models preserving quotient idempotence and localization. `HenselianEtaleSection.bijective_comp_quotient_of_henselian` now gives unique etale-section lifting, and `HenselianIdempotents.bijective_idempotents_quotient_of_henselian` gives the integral-algebra idempotent bijection via finite models, coprime polynomial factorization, and Jacobson rigidity. These are the forward implications needed by 09ZL, not a completed proof of every converse in 09XI. No upstairs henselian assumption is substituted; source review only. |
| [09ZL](https://stacks.math.columbia.edu/tag/09ZL) | Ch. 15 More on Algebra / §15.13 [Lifting and henselian pairs](https://stacks.math.columbia.edu/tag/0D49) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1; [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×2 | `EtaleFundamentalGroups-required` | Full source implementation: `CommAlgCat.FiniteEtale.baseChange_isEquivalence_of_henselian` in `SchemeTheory/FiniteEtale/Algebra/HenselianBaseChange.lean`. `JacobsonBaseChange` proves faithfulness. `HenselianFullness` constructs lifts of residual maps through a lifted tensor-graph idempotent, with no Henselian assumption on the target algebra. `HenselianQuotientLift` constructs finite etale object lifts from 04D1, the integral-closure finite factor, integral idempotent lifting, and the actual localization comparison. `IdempotentFactorReduction` identifies the special fiber with the prescribed algebra. The canonical tensor-product functor is an equivalence under the native general `HenselianRing R I` hypothesis. Independently reviewed and integrated; source-only validation, no Lean/Lake execution or heartbeat measurement. |
| [09ZT](https://stacks.math.columbia.edu/tag/09ZT) | Ch. 30 Cohomology of Schemes / §30.28 [Grothendieck's algebraization theorem](https://stacks.math.columbia.edu/tag/0898) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×2 | `EtaleFundamentalGroups-required` | Grothendieck existence for a compatible tower of finite morphisms over a complete Noetherian base is absent; algebraizing the tower is the first frontier. |
| [09ZW](https://stacks.math.columbia.edu/tag/09ZW) | Ch. 37 More on Morphisms / §37.3 [Morphisms of thickenings](https://stacks.math.columbia.edu/tag/0CF2) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×2 | `EtaleFundamentalGroups-required` | There is no scheme-thickening transport package for closed immersions, finite, proper, monomorphism, and unramified properties; the finite and étale clauses used in §58.9 are the first frontier. |
| [0A04](https://stacks.math.columbia.edu/tag/0A04) | Ch. 15 More on Algebra / §15.12 [Henselization of pairs](https://stacks.math.columbia.edu/tag/0EM7) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×2 | `EtaleFundamentalGroups-required` | Henselization of pairs and its commutation with filtered colimits are absent. |
| [0A0P](https://stacks.math.columbia.edu/tag/0A0P) | Ch. 32 Limits of Schemes / §32.13 [Applications of Chow's lemma](https://stacks.math.columbia.edu/tag/0204) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×2 | `EtaleFundamentalGroups-required` | No absolute approximation theorem presents a proper morphism over a quasi-compact quasi-separated base as an inverse limit of proper finite-type morphisms over `ℤ`; that presentation is the first frontier. |
| [0A1W](https://stacks.math.columbia.edu/tag/0A1W) | Ch. 16 Smoothing Ring Maps / §16.13 [The approximation property for G-rings](https://stacks.math.columbia.edu/tag/07QX) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×1 | `EtaleFundamentalGroups-required` | Henselization objects are absent, so the algebraicity of elements of a henselization inside the completion used in §58.9 has no endpoint. |
| [0A43](https://stacks.math.columbia.edu/tag/0A43) | Ch. 37 More on Morphisms / §37.12 [Smoothness over a Noetherian base](https://stacks.math.columbia.edu/tag/02HW) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×2; [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×1 | `EtaleFundamentalGroups-required` | No formal-neighbourhood criterion lifts smoothness or étaleness from every infinitesimal thickening to a neighbourhood of the closed fibre; that criterion is the first frontier. |
| [0A80](https://stacks.math.columbia.edu/tag/0A80) | Ch. 47 Dualizing Complexes / §47.17 [Dualizing complexes and dimension functions](https://stacks.math.columbia.edu/tag/0A7W) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | Dualizing complexes and the theorem that their Noetherian rings are finite-dimensional and universally catenary are absent; that implication is the first frontier. |
| [0AA3](https://stacks.math.columbia.edu/tag/0AA3) | Ch. 48 Duality for Schemes / §48.17 [Properties of upper shriek functors](https://stacks.math.columbia.edu/tag/0ATZ) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | The exceptional pullback `f^!` and preservation of dualizing complexes under finite-type separated morphisms are not formalized; this duality endpoint is the first frontier. |
| [0AB1](https://stacks.math.columbia.edu/tag/0AB1) | Ch. 29 Morphisms of Schemes / §29.55 [Normalization](https://stacks.math.columbia.edu/tag/035E) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1 | `EtaleFundamentalGroups-required` | Relative normalization exists, but mathlib has no normal-scheme predicate or theorem making an integral birational map to a normal integral scheme an isomorphism. |
| [0AFS](https://stacks.math.columbia.edu/tag/0AFS) | Ch. 10 Commutative Algebra / §10.110 [Regular rings and global dimension](https://stacks.math.columbia.edu/tag/065U) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | The equivalence between regularity, finite global dimension, and regular localizations is not present in the required generality. |
| [0AGY](https://stacks.math.columbia.edu/tag/0AGY) | Ch. 15 More on Algebra / §15.45 [Permanence of properties under étale maps](https://stacks.math.columbia.edu/tag/0AGY) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `context-only` | This is a section-level permanence citation; Chapter 58 does not use it as a standalone proposition beyond the separately inventoried étale results. |
| [0AH3](https://stacks.math.columbia.edu/tag/0AH3) | Ch. 15 More on Algebra / §15.51 [G-rings](https://stacks.math.columbia.edu/tag/07GG) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×1 | `EtaleFundamentalGroups-required` | The theorem that henselization of a G-ring is again a G-ring is blocked by missing G-ring and henselization objects. |
| [0AH5](https://stacks.math.columbia.edu/tag/0AH5) | Ch. 16 Smoothing Ring Maps / §16.14 [Approximation for henselian pairs](https://stacks.math.columbia.edu/tag/0AH4) | [58.9 / `0BQC`](https://stacks.math.columbia.edu/tag/0BQC) ×1 | `EtaleFundamentalGroups-required` | General Artin approximation for Noetherian henselian pairs under the three stated hypotheses is absent; approximate algebraization of formal solutions is the first frontier. |
| [0AH6](https://stacks.math.columbia.edu/tag/0AH6) | Ch. 29 Morphisms of Schemes / §29.42 [Proper morphisms](https://stacks.math.columbia.edu/tag/01W0) | [58.18 / `0EK3`](https://stacks.math.columbia.edu/tag/0EK3) ×1 | `EtaleFundamentalGroups-required` | `Scheme.Hom.image` and properness exist separately, but no endpoint proves properness of the scheme-theoretic image and surjectivity onto it under these hypotheses. |
| [0ALI](https://stacks.math.columbia.edu/tag/0ALI) | Ch. 15 More on Algebra / §15.11 [Henselian pairs](https://stacks.math.columbia.edu/tag/09XD) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `EtaleFundamentalGroups-required` | The Henselian assertion is source-implemented by `HenselianRing.of_le_nilradical` in `SchemeTheory/RingTheory/HenselianNilIdeal.lean`, for arbitrary nil ideals. Together with 09ZL this supplies the finite-etale equivalence needed for Chapter 58. `FiniteEtale.AffineThickening` gives canonical scheme pullback equivalences for nil quotients and arbitrary affine-target surjective closed immersions. The full 0ALI equivalence for all etale algebras (without module finiteness) is not claimed by these sources. Independent static review only; no Lean/Lake validation. |
| [0ALJ](https://stacks.math.columbia.edu/tag/0ALJ) | Ch. 15 More on Algebra / §15.11 [Henselian pairs](https://stacks.math.columbia.edu/tag/09XD) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×2 | `mathlib-covered` | `HenselianRing.of_isAdicComplete` and the `IsAdicComplete`-to-henselian instance give the exact completeness-implies-henselian result. |
| [0ALZ](https://stacks.math.columbia.edu/tag/0ALZ) | Ch. 47 Dualizing Complexes / §47.9 [Local cohomology](https://stacks.math.columbia.edu/tag/0952) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1; [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `EtaleFundamentalGroups-required` | Local cohomology is defined, but there is no derived tensor base-change isomorphism for cohomology with support; that functorial comparison is the first frontier. |
| [0AP2](https://stacks.math.columbia.edu/tag/0AP2) | Ch. 15 More on Algebra / §15.45 [Permanence of properties under étale maps](https://stacks.math.columbia.edu/tag/0AGY) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | `IsDedekindDomain.of_formallyUnramified` treats a finite domain algebra; it does not give the tag's product decomposition and local-DVR conclusion for an arbitrary étale algebra. |
| [0AP3](https://stacks.math.columbia.edu/tag/0AP3) | Ch. 15 More on Algebra / §15.46 [Permanence of properties under henselization](https://stacks.math.columbia.edu/tag/07QL) | [58.16 / `0BUP`](https://stacks.math.columbia.edu/tag/0BUP) ×1 | `EtaleFundamentalGroups-required` | The DVR properties of henselization and strict henselization cannot be stated with current APIs because those objects are absent. |
| [0AUK](https://stacks.math.columbia.edu/tag/0AUK) | Ch. 10 Commutative Algebra / §10.72 [Depth](https://stacks.math.columbia.edu/tag/00LE) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×2; [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×2 | `EtaleFundamentalGroups-required` | The semilocal finite-extension depth comparison is blocked by the absence of a depth API. |
| [0AVB](https://stacks.math.columbia.edu/tag/0AVB) | Ch. 15 More on Algebra / §15.24 [Reflexive modules](https://stacks.math.columbia.edu/tag/0AUY) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `EtaleFundamentalGroups-required` | The reflexive iff torsion-free plus `(S₂)` criterion and intersection characterization have no endpoint. |
| [0AVM](https://stacks.math.columbia.edu/tag/0AVM) | Ch. 31 Divisors / §31.2 [Associated points](https://stacks.math.columbia.edu/tag/02OI) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×2 | `EtaleFundamentalGroups-required` | Scheme-level depth and associated-point APIs are missing; the stalkwise-isomorphism criterion for coherent sheaves is the first frontier. |
| [0AVZ](https://stacks.math.columbia.edu/tag/0AVZ) | Ch. 47 Dualizing Complexes / §47.11 [Depth](https://stacks.math.columbia.edu/tag/0AVY) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1; [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1; [58.25 / `0BPB`](https://stacks.math.columbia.edu/tag/0BPB) ×1 | `EtaleFundamentalGroups-required` | There is no theorem identifying depth with the first nonzero Ext and local-cohomology degrees; the vanishing consequence used in §58.19 is the first frontier. |
| [0AW6](https://stacks.math.columbia.edu/tag/0AW6) | Ch. 15 More on Algebra / §15.111 [Formally catenary rings](https://stacks.math.columbia.edu/tag/0AW1) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | Universal catenarity and formal catenarity are not packaged in the equivalence stated by the tag. |
| [0AWE](https://stacks.math.columbia.edu/tag/0AWE) | Ch. 47 Dualizing Complexes / §47.17 [Dualizing complexes and dimension functions](https://stacks.math.columbia.edu/tag/0A7W) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | Dualizing modules and their support and `S₂` properties are absent; the depth-two canonical-module result used in purity is the first frontier. |
| [0AWG](https://stacks.math.columbia.edu/tag/0AWG) | Ch. 48 Duality for Schemes / §48.7 [Right adjoint of pushforward and trace maps](https://stacks.math.columbia.edu/tag/0AWG) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | The scheme duality trace transformation and its base-change compatibility are not present; constructing the trace map used in §58.28 is the first frontier. |
| [0AWT](https://stacks.math.columbia.edu/tag/0AWT) | Ch. 48 Duality for Schemes / §48.23 [Cohen-Macaulay schemes](https://stacks.math.columbia.edu/tag/0AWQ) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | There is no dualizing-complex characterization or openness theorem for the Cohen-Macaulay locus; that locus theorem is the first frontier. |
| [0AXD](https://stacks.math.columbia.edu/tag/0AXD) | Ch. 54 Resolution of Surfaces / §54.7 [Vanishing](https://stacks.math.columbia.edu/tag/0AX7) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | Grauert-Riemenschneider vanishing for a normal surface modification is absent; the `R¹f_* ω_X = 0` endpoint is the first frontier. |
| [0AXE](https://stacks.math.columbia.edu/tag/0AXE) | Ch. 54 Resolution of Surfaces / §54.8 [Boundedness](https://stacks.math.columbia.edu/tag/0AXE) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `context-only` | This is the section-level discussion of rational singularities; the two concrete results Chapter 58 invokes are separately recorded as `0AXF` and `0B4Q`. |
| [0AXF](https://stacks.math.columbia.edu/tag/0AXF) | Ch. 54 Resolution of Surfaces / §54.8 [Boundedness](https://stacks.math.columbia.edu/tag/0AXE) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | No short exact sequence compares `H¹` across two normal surface modifications or controls the support of `R¹g_*𝒪`; that comparison is the first frontier. |
| [0AXP](https://stacks.math.columbia.edu/tag/0AXP) | Ch. 29 Morphisms of Schemes / §29.54 [Relative normalization](https://stacks.math.columbia.edu/tag/0BAK) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1 | `EtaleFundamentalGroups-required` | No theorem sends generic points of irreducible components of a relative normalization to images of generic component points of the source. |
| [0B4Q](https://stacks.math.columbia.edu/tag/0B4Q) | Ch. 54 Resolution of Surfaces / §54.8 [Boundedness](https://stacks.math.columbia.edu/tag/0AXE) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | Rational singularities are not defined and the theorem that a two-dimensional Nagata regular local ring has one is absent; this implication is the first frontier. |
| [0B4R](https://stacks.math.columbia.edu/tag/0B4R) | Ch. 54 Resolution of Surfaces / §54.7 [Vanishing](https://stacks.math.columbia.edu/tag/0AX7) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | Dualizing modules for two-dimensional normal schemes and their normalization under a chosen base dualizing complex are not available; this construction is the first frontier. |
| [0B64](https://stacks.math.columbia.edu/tag/0B64) | Ch. 54 Resolution of Surfaces / §54.9 [Rational singularities](https://stacks.math.columbia.edu/tag/0B4V) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | The canonical-module formulas and vanishing for the blowup of a two-dimensional local ring are absent; the surjectivity `f*ω_A → ω_X` used in §58.28 is the first frontier. |
| [0BAK](https://stacks.math.columbia.edu/tag/0BAK) | Ch. 29 Morphisms of Schemes / §29.54 [Relative normalization](https://stacks.math.columbia.edu/tag/0BAK) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `context-only` | This is the relative-normalization section tag; the actual construction and universal-property dependency is separately represented by `035I`. |
| [0BAL](https://stacks.math.columbia.edu/tag/0BAL) | Ch. 35 Descent / §35.16 [Properties of schemes local in the fppf topology](https://stacks.math.columbia.edu/tag/034B) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1; [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | There is no fppf-local theorem for local finiteness of irreducible components of quasi-compact opens; that component-finiteness descent is the first frontier. |
| [0BCU](https://stacks.math.columbia.edu/tag/0BCU) | Ch. 31 Divisors / §31.17 [Complements of affine opens](https://stacks.math.columbia.edu/tag/0BCQ) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | No dimension theorem controls local rings at generic points of the complement of an affine open; the codimension-at-most-one statement is the first frontier. |
| [0BG9](https://stacks.math.columbia.edu/tag/0BG9) | Ch. 54 Resolution of Surfaces / §54.11 [Base change to the completion](https://stacks.math.columbia.edu/tag/0BG4) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | No theorem proves finiteness of normalization and compatibility with completion under normality away from the closed fibre; that completion comparison is the first frontier. |
| [0BGP](https://stacks.math.columbia.edu/tag/0BGP) | Ch. 54 Resolution of Surfaces / §54.14 [Resolution](https://stacks.math.columbia.edu/tag/0BGJ) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | Lipman's equivalence between alterations, resolutions, normalized blowups, and completed normality for two-dimensional schemes is absent; resolution existence is the first frontier. |
| [0BIR](https://stacks.math.columbia.edu/tag/0BIR) | Ch. 15 More on Algebra / §15.52 [Properties of formal fibres](https://stacks.math.columbia.edu/tag/0BIR) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `context-only` | This is the section heading for properties of formal fibres; the Chapter 58 proof cites specific G-ring and completion results separately. |
| [0BJF](https://stacks.math.columbia.edu/tag/0BJF) | Ch. 49 Discriminants and Differents / §49.3 [Discriminant of a finite locally free morphism](https://stacks.math.columbia.edu/tag/0BVH) | [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×2; [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×2 | `EtaleFundamentalGroups-required` | There is no scheme discriminant for finite locally free morphisms or theorem that its empty locus is equivalent to étaleness; that discriminant criterion is the first frontier. |
| [0BJM](https://stacks.math.columbia.edu/tag/0BJM) | Ch. 47 Dualizing Complexes / §47.23 [Formal fibres](https://stacks.math.columbia.edu/tag/0BJM) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | The formal-fibre permanence package for Gorenstein rings is absent; the flat-completion transport of the `S₂` condition used in §58.19 is the first frontier. |
| [0BK0](https://stacks.math.columbia.edu/tag/0BK0) | Ch. 51 Local Cohomology / §51.8 [Finiteness of pushforwards, I](https://stacks.math.columbia.edu/tag/0BL8) | [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | No coherent extension and local-cohomology exact sequence for a coherent sheaf on an affine punctured open exists; that finite-module realization is the first frontier. |
| [0BKG](https://stacks.math.columbia.edu/tag/0BKG) | Ch. 15 More on Algebra / §15.95 [Derived completion for a principal ideal](https://stacks.math.columbia.edu/tag/0BKF) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `context-only` | The occurrence is explicitly a comparison with the derived-completion construction, not an invoked theorem in the Chapter 58 argument. |
| [0BL5](https://stacks.math.columbia.edu/tag/0BL5) | Ch. 37 More on Morphisms / §37.68 [Relative morphisms](https://stacks.math.columbia.edu/tag/0BL0) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `EtaleFundamentalGroups-required` | No scheme represents the relative morphism functor from a finite locally free source to a separated locally quasi-finite target; this representability theorem is the first frontier. |
| [0BLR](https://stacks.math.columbia.edu/tag/0BLR) | Ch. 51 Local Cohomology / §51.3 [Hartshorne's connectedness lemma](https://stacks.math.columbia.edu/tag/0FIV) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1; [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×3 | `EtaleFundamentalGroups-required` | Depth and henselization infrastructure are missing, so connectedness of punctured spectra of a depth-at-least-two local ring and its henselizations has no endpoint. |
| [0BLY](https://stacks.math.columbia.edu/tag/0BLY) | Ch. 95 Examples of Stacks / §95.6 [Finite étale covers](https://stacks.math.columbia.edu/tag/0BLY) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1 | `context-only` | Chapter 58 only notes the global fppf-stack structure of finite étale covers; none of the following arguments uses stack descent, and Pi1 owns the fibre category directly. |
| [0BM4](https://stacks.math.columbia.edu/tag/0BM4) | Ch. 15 More on Algebra / §15.24 [Reflexive modules](https://stacks.math.columbia.edu/tag/0AUY) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1 | `EtaleFundamentalGroups-required` | No theorem proves that the integral closure module in the stated finite separable extension is reflexive. |
| [0BMC](https://stacks.math.columbia.edu/tag/0BMC) | Ch. 5 Topology / §5.30 [Topological groups, rings, modules](https://stacks.math.columbia.edu/tag/0B1Y) | [58.3 / `0BMQ`](https://stacks.math.columbia.edu/tag/0BMQ) ×1 | `context-only` | This example supplies the topology convention in §58.3; the finite-set use is implemented directly by `PreGaloisCategory.autEmbedding`, `autEmbedding_isClosedEmbedding`, and `continuousSMul_aut_fiber`. |
| [0BMI](https://stacks.math.columbia.edu/tag/0BMI) | Ch. 9 Fields / §9.22 [Infinite Galois theory](https://stacks.math.columbia.edu/tag/0BMI) | [58.2 / `04JI`](https://stacks.math.columbia.edu/tag/04JI) ×1 | `context-only` | The section citation only fixes the canonical topology; mathlib owns it as `krullTopology` and packages the Galois group as `InfiniteGalois.profiniteGalGrp`. |
| [0BML](https://stacks.math.columbia.edu/tag/0BML) | Ch. 9 Fields / §9.22 [Infinite Galois theory](https://stacks.math.columbia.edu/tag/0BMI) | [58.2 / `04JI`](https://stacks.math.columbia.edu/tag/04JI) ×1; [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×2 | `mathlib-covered` | `InfiniteGalois.IntermediateFieldEquivClosedSubgroup`, `InfiniteGalois.isOpen_iff_finite`, and `InfiniteGalois.normal_iff_isGalois` exactly give the three correspondence clauses. |
| [0BMM](https://stacks.math.columbia.edu/tag/0BMM) | Ch. 9 Fields / §9.22 [Infinite Galois theory](https://stacks.math.columbia.edu/tag/0BMI) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1 | `EtaleFundamentalGroups-required` | `IntermediateField.restrictNormalHom_ker`, `AlgEquiv.restrictNormalHom_surjective`, and `InfiniteGalois.restrictNormalHom_continuous` are ingredients, but no public declaration packages the stated short exact sequence of profinite groups; continuity of the left `restrictScalarsHom` map is also absent. |
| [0BMN](https://stacks.math.columbia.edu/tag/0BMN) | Ch. 35 Descent / §35.13 [Fpqc coverings are universal effective epimorphisms](https://stacks.math.columbia.edu/tag/023P) | [58.5 / `0BL6`](https://stacks.math.columbia.edu/tag/0BL6) ×1; [58.5.3 / `0BNA`](https://stacks.math.columbia.edu/tag/0BNA) ×1 | `EtaleFundamentalGroups-implemented` | `AlgebraicGeometry.Scheme.isColimit_cofork_of_fpqc_local` is the exact scheme-level statement: coequalizer universal properties on every fpqc-cover member and every pairwise overlap descend to the original cofork. The proof uses the existing subcanonical fpqc topology, its induced effective-epimorphic families, and pullback stability; strict build and the standard-axiom audit pass. |
| [0BPA](https://stacks.math.columbia.edu/tag/0BPA) | Ch. 32 Limits of Schemes / §32.20 [Glueing in closed fibres](https://stacks.math.columbia.edu/tag/0E8P) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1; [58.24 / `0EK8`](https://stacks.math.columbia.edu/tag/0EK8) ×1; [58.27 / `0ELB`](https://stacks.math.columbia.edu/tag/0ELB) ×1; [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | The categorical gluing equivalence for finitely presented schemes over an open complement and punctured local spectrum is absent; that equivalence is the first frontier. |
| [0BPG](https://stacks.math.columbia.edu/tag/0BPG) | Ch. 37 More on Morphisms / §37.3 [Morphisms of thickenings](https://stacks.math.columbia.edu/tag/0CF2) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `EtaleFundamentalGroups-required` | No transport theorem carries finiteness, properness, monomorphism, immersion, and unramifiedness across a cartesian morphism of thickenings; the finite and étale clauses are the first frontier. |
| [0BQ3](https://stacks.math.columbia.edu/tag/0BQ3) | Ch. 28 Properties of Schemes / §28.16 [Local irreducibility](https://stacks.math.columbia.edu/tag/0BQ1) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×2 | `EtaleFundamentalGroups-required` | No theorem states that a normal scheme is geometrically unibranch; both scheme-normal and geometrically-unibranch APIs are missing. |
| [0BQ4](https://stacks.math.columbia.edu/tag/0BQ4) | Ch. 28 Properties of Schemes / §28.16 [Local irreducibility](https://stacks.math.columbia.edu/tag/0BQ1) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×1 | `EtaleFundamentalGroups-required` | The equivalence between geometric unibranchness and connected punctured strict henselizations is absent. |
| [0BQ5](https://stacks.math.columbia.edu/tag/0BQ5) | Ch. 32 Limits of Schemes / §32.20 [Glueing in closed fibres](https://stacks.math.columbia.edu/tag/0E8P) | [58.10 / `0BQD`](https://stacks.math.columbia.edu/tag/0BQD) ×3; [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×2 | `EtaleFundamentalGroups-required` | No colimit gluing equivalence near a point for finitely presented schemes is available; this open-neighbourhood algebraization theorem is the first frontier. |
| [0BRD](https://stacks.math.columbia.edu/tag/0BRD) | Ch. 10 Commutative Algebra / §10.46 [Universal homeomorphisms](https://stacks.math.columbia.edu/tag/0BR5) | [58.14 / `0BTU`](https://stacks.math.columbia.edu/tag/0BTU) ×1 | `EtaleFundamentalGroups-required` | Mathlib has scheme-level universally-injective criteria, but no exact ring theorem packaging integrality, spectrum bijectivity, purely inseparable residue extensions, and all base changes. |
| [0BRE](https://stacks.math.columbia.edu/tag/0BRE) | Ch. 15 More on Algebra / §15.112 [Group actions and integral closure](https://stacks.math.columbia.edu/tag/0BRE) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×1 | `context-only` | This is the section-level introduction to group actions and integral closure; all used propositions from it occur as separate tags. |
| [0BRH](https://stacks.math.columbia.edu/tag/0BRH) | Ch. 15 More on Algebra / §15.112 [Group actions and integral closure](https://stacks.math.columbia.edu/tag/0BRE) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×2 | `EtaleFundamentalGroups-required` | The invariant-ring base-change isomorphism and its universal-homeomorphism conclusion are not provided by the generic `Algebra.IsInvariant` API. |
| [0BRI](https://stacks.math.columbia.edu/tag/0BRI) | Ch. 15 More on Algebra / §15.112 [Group actions and integral closure](https://stacks.math.columbia.edu/tag/0BRE) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×2 | `mathlib-covered` | `Algebra.IsInvariant.exists_smul_of_under_eq` is the exact finite-group transitivity-on-primes result. |
| [0BRJ](https://stacks.math.columbia.edu/tag/0BRJ) | Ch. 15 More on Algebra / §15.112 [Group actions and integral closure](https://stacks.math.columbia.edu/tag/0BRE) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×1 | `mathlib-covered` | `Ideal.Quotient.stabilizerHom_surjective`, `Ideal.IsFractionRing.normal`, and `Algebra.IsInvariant.isIntegral` give the stated residue-field normality and stabilizer surjectivity. |
| [0BRK](https://stacks.math.columbia.edu/tag/0BRK) | Ch. 15 More on Algebra / §15.112 [Group actions and integral closure](https://stacks.math.columbia.edu/tag/0BRE) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×2 | `EtaleFundamentalGroups-required` | The profinite variants of transitivity and stabilizer surjectivity exist, but no exact arbitrary-Galois integral-closure specialization supplies all hypotheses and conclusions of this tag. |
| [0BRM](https://stacks.math.columbia.edu/tag/0BRM) | Ch. 15 More on Algebra / §15.116 [Abhyankar's lemma and tame ramification](https://stacks.math.columbia.edu/tag/0EXT) | [58.30 / `0BUQ`](https://stacks.math.columbia.edu/tag/0BUQ) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | Abhyankar's lemma in the stated tame-ramification form has no endpoint. |
| [0BSJ](https://stacks.math.columbia.edu/tag/0BSJ) | Ch. 10 Commutative Algebra / §10.154 [Filtered colimits of étale ring maps](https://stacks.math.columbia.edu/tag/0BSG) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×1 | `mathlib-covered` | `CategoryTheory.ObjectProperty.ind_ind`, specialized to `Algebra.Etale R`, is exactly the idempotence of filtered colimits because étale algebras are finitely presentable. |
| [0BSL](https://stacks.math.columbia.edu/tag/0BSL) | Ch. 10 Commutative Algebra / §10.155 [Henselization and strict henselization](https://stacks.math.columbia.edu/tag/0BSK) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | The filtered-colimit presentation of a strict henselization is essential to the Chapter 58 use, and no strict-henselization object or presentation exists. |
| [0BSR](https://stacks.math.columbia.edu/tag/0BSR) | Ch. 37 More on Morphisms / §37.42 [Étale localization of integral morphisms](https://stacks.math.columbia.edu/tag/0BUH) | [58.12 / `0BSN`](https://stacks.math.columbia.edu/tag/0BSN) ×1; [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | `Inertia.HenselianIntegralFiber` now supplies actual unique idempotents and local factors over a Henselian local base for arbitrary integral algebras with finite closed fiber. A strictly Henselian consumer supplies purely inseparable residue extensions. Descent of this splitting and the prescribed finite residue data to an actual étale neighborhood remains unfinished; full external tag is not claimed. |
| [0BSX](https://stacks.math.columbia.edu/tag/0BSX) | Ch. 15 More on Algebra / §15.112 [Group actions and integral closure](https://stacks.math.columbia.edu/tag/0BRE) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | Restriction maps on decomposition and inertia groups in an arbitrary tower, with the stated surjectivity, are not packaged. |
| [0BTL](https://stacks.math.columbia.edu/tag/0BTL) | Ch. 41 Étale Morphisms of Schemes / §41.20 [Descending étale morphisms](https://stacks.math.columbia.edu/tag/0BTH) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `EtaleFundamentalGroups-required` | The universal-homeomorphism case needed for 0BQN now has source implementations: actual relative-map descent into arbitrary etale targets, Hom bijectivity for separated etale targets, and full faithfulness of the canonical finite-etale pullback. The full general descent-data statement for the three classes of surjective maps is not claimed. Typechecking remains pending. |
| [0BTP](https://stacks.math.columbia.edu/tag/0BTP) | Ch. 41 Étale Morphisms of Schemes / §41.20 [Descending étale morphisms](https://stacks.math.columbia.edu/tag/0BTH) | [58.8 / `0BTT`](https://stacks.math.columbia.edu/tag/0BTT) ×1 | `EtaleFundamentalGroups-required` | Effective object descent remains missing. Integral Henselian ascent and actual finite-etale models over finite subalgebras of integral extensions now have source proofs; the latter reduces the affine universal-homeomorphism case to finite base maps. FaithfullyFlatAlgebra now constructs the actual invariant algebra from a native coaction and proves its scalar-extension comparison is an isomorphism; the constructed algebra is finite etale when the original algebra is. Tensor-form overlap isomorphisms with diagonal and triple-cocycle equations now produce native coactions. The local-cover construction and the transport from scheme overlaps to that tensor form still remain. These ingredients do not yet establish the required integral descent equivalence. |
| [0BU2](https://stacks.math.columbia.edu/tag/0BU2) | Ch. 9 Fields / §9.22 [Infinite Galois theory](https://stacks.math.columbia.edu/tag/0BMI) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `mathlib-covered` | `FiniteGaloisIntermediateField.adjoin`, `finGaloisGroupFunctor`, `InfiniteGalois.continuousMulEquivToLimit`, `InfiniteGalois.restrictNormalHom_continuous`, and `AlgEquiv.restrictNormalHom_surjective` cover the directed finite-Galois system, profinite inverse limit, and projections. |
| [0BU7](https://stacks.math.columbia.edu/tag/0BU7) | Ch. 15 More on Algebra / §15.114 [Galois extensions and ramification](https://stacks.math.columbia.edu/tag/09E3) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×2 | `EtaleFundamentalGroups-required` | The finite-tower surjections and commuting diagrams for wild inertia, inertia, and decomposition groups have no exact endpoint. |
| [0BU8](https://stacks.math.columbia.edu/tag/0BU8) | Ch. 15 More on Algebra / §15.114 [Galois extensions and ramification](https://stacks.math.columbia.edu/tag/09E3) | [58.13 / `0BSD`](https://stacks.math.columbia.edu/tag/0BSD) ×1 | `EtaleFundamentalGroups-required` | CFT has a tame-inertia character range statement, but not the scaled character and tower-compatibility formula of this tag. |
| [0BVH](https://stacks.math.columbia.edu/tag/0BVH) | Ch. 49 Discriminants and Differents / §49.3 [Discriminant of a finite locally free morphism](https://stacks.math.columbia.edu/tag/0BVH) | [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×1; [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `context-only` | This is the discriminant section citation introducing notation; the actual étale-discriminant criterion is separately represented by `0BJF`. |
| [0C0C](https://stacks.math.columbia.edu/tag/0C0C) | Ch. 32 Limits of Schemes / §32.8 [Descending properties of morphisms](https://stacks.math.columbia.edu/tag/081C) | [58.30 / `0BUQ`](https://stacks.math.columbia.edu/tag/0BUQ) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | No public theorem makes a descended locally-finitely-presented morphism smooth at a sufficiently large inverse-system stage; eventual smoothness is the first frontier. |
| [0C0E](https://stacks.math.columbia.edu/tag/0C0E) | Ch. 37 More on Morphisms / §37.26 [Reduced fibres](https://stacks.math.columbia.edu/tag/0574) | [58.30 / `0BUQ`](https://stacks.math.columbia.edu/tag/0BUQ) ×1 | `EtaleFundamentalGroups-required` | There is no openness theorem for the geometrically reduced fibre locus of a flat proper finitely-presented morphism; that locus result is the first frontier. |
| [0D2H](https://stacks.math.columbia.edu/tag/0D2H) | Ch. 15 More on Algebra / §15.6 [Fibre products of rings, II](https://stacks.math.columbia.edu/tag/0D2G) | [58.18 / `0EK3`](https://stacks.math.columbia.edu/tag/0EK3) ×1 | `EtaleFundamentalGroups-required` | No theorem states finite generation of the glued module over the fibre-product ring under the tag's hypotheses. |
| [0DWR](https://stacks.math.columbia.edu/tag/0DWR) | Ch. 51 Local Cohomology / §51.2 [Generalities](https://stacks.math.columbia.edu/tag/0DWQ) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | No module realization and local-cohomology exact sequence exists for a quasi-coherent sheaf on an affine open complement; this basic comparison is the first frontier. |
| [0DX7](https://stacks.math.columbia.edu/tag/0DX7) | Ch. 51 Local Cohomology / §51.4 [Cohomological dimension](https://stacks.math.columbia.edu/tag/0DX6) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | Local cohomology is defined, but its cohomological-dimension characterization and the open-complement cohomology vanishing equivalence are absent. |
| [0DXB](https://stacks.math.columbia.edu/tag/0DXB) | Ch. 51 Local Cohomology / §51.4 [Cohomological dimension](https://stacks.math.columbia.edu/tag/0DX6) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | No localization formula computes cohomological dimension as the maximum over prime localizations; that formula is the first frontier. |
| [0DXC](https://stacks.math.columbia.edu/tag/0DXC) | Ch. 51 Local Cohomology / §51.4 [Cohomological dimension](https://stacks.math.columbia.edu/tag/0DX6) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | No dimension bound gives local-cohomology vanishing above the support dimension of a finite module; that vanishing theorem is the first frontier. |
| [0E25](https://stacks.math.columbia.edu/tag/0E25) | Ch. 37 More on Morphisms / §37.67 [Pushouts in the category of schemes, II](https://stacks.math.columbia.edu/tag/0ECH) | [58.18 / `0EK3`](https://stacks.math.columbia.edu/tag/0EK3) ×2 | `EtaleFundamentalGroups-required` | Mathlib has gluing and ordinary colimits, but no Ferrand-style scheme pushout with the stated fibre-square, integrality, closed-immersion, and structure-sheaf formula. |
| [0E9I](https://stacks.math.columbia.edu/tag/0E9I) | Ch. 31 Divisors / §31.5 [Weakly associated points](https://stacks.math.columbia.edu/tag/056K) | [58.20 / `0BM7`](https://stacks.math.columbia.edu/tag/0BM7) ×1; [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | Depth and local-cohomology infrastructure is missing, so extension across a depth-at-least-two complement and the global-section isomorphism have no endpoint. |
| [0E9K](https://stacks.math.columbia.edu/tag/0E9K) | Ch. 37 More on Morphisms / §37.62 [Local complete intersection morphisms](https://stacks.math.columbia.edu/tag/068E) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | Local complete-intersection morphisms are not available at scheme level; the theorem that a finite-type map between regular schemes is lci is the first frontier. |
| [0E9V](https://stacks.math.columbia.edu/tag/0E9V) | Ch. 48 Duality for Schemes / §48.21 [Dimension functions](https://stacks.math.columbia.edu/tag/0BV4) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | Exceptional pullback, dimension functions, and `S₂` coherent sheaves are absent; the lower cohomological bound and `S₂` conclusion for `f^!𝒪` are the first frontier. |
| [0E9Z](https://stacks.math.columbia.edu/tag/0E9Z) | Ch. 48 Duality for Schemes / §48.29 [The fundamental class of an lci morphism](https://stacks.math.columbia.edu/tag/0E9X) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×2 | `EtaleFundamentalGroups-required` | There is no fundamental-class map from top exterior differentials to the relative dualizing sheaf or criterion identifying its isomorphism locus with the smooth locus. |
| [0EA0](https://stacks.math.columbia.edu/tag/0EA0) | Ch. 48 Duality for Schemes / §48.29 [The fundamental class of an lci morphism](https://stacks.math.columbia.edu/tag/0E9X) | [58.28 / `0EA1`](https://stacks.math.columbia.edu/tag/0EA1) ×1 | `EtaleFundamentalGroups-required` | The lci fundamental-class construction under the stated Cohen-Macaulay and Koszul hypotheses is absent; its isomorphism over the smooth locus is the first frontier. |
| [0EB7](https://stacks.math.columbia.edu/tag/0EB7) | Ch. 51 Local Cohomology / §51.16 [Hartshorne-Lichtenbaum vanishing](https://stacks.math.columbia.edu/tag/0EB0) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | Hartshorne-Lichtenbaum local-cohomology vanishing for excellent normal local rings is absent; the cohomological-dimension bound used in §58.29 is the first frontier. |
| [0EBI](https://stacks.math.columbia.edu/tag/0EBI) | Ch. 31 Divisors / §31.13 [Reflexive modules](https://stacks.math.columbia.edu/tag/0AVT) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | Scheme-level coherent reflexive sheaves, depth, and `S₂` are not integrated; the reflexive-sheaf characterization is the first frontier. |
| [0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) | Ch. 31 Divisors / §31.13 [Reflexive modules](https://stacks.math.columbia.edu/tag/0AVT) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1 | `EtaleFundamentalGroups-required` | No equivalence of coherent reflexive sheaves across an open complement of depth at least two exists; that restriction and pushforward equivalence is the first frontier. |
| [0EBS](https://stacks.math.columbia.edu/tag/0EBS) | Ch. 41 Étale Morphisms of Schemes / §41.14 [Topological properties of étale morphisms](https://stacks.math.columbia.edu/tag/025F) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | No scheme relative-Frobenius construction exists, hence the theorem that relative Frobenius is an isomorphism for an étale morphism in characteristic `p` is absent. |
| [0EBT](https://stacks.math.columbia.edu/tag/0EBT) | Ch. 47 Dualizing Complexes / §47.21 [Gorenstein rings](https://stacks.math.columbia.edu/tag/0DW6) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | Injective hulls and the Gorenstein Tor concentration theorem are not available in this generality; the `Tor_d(E,k) = k` calculation is the first frontier. |
| [0EC0](https://stacks.math.columbia.edu/tag/0EC0) | Ch. 51 Local Cohomology / §51.17 [Frobenius action](https://stacks.math.columbia.edu/tag/0EBU) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | Kunz's theorem is absent; the equivalence between Noetherian regularity in characteristic `p` and flatness of Frobenius is the first frontier. |
| [0EC2](https://stacks.math.columbia.edu/tag/0EC2) | Ch. 51 Local Cohomology / §51.18 [Structure of certain modules](https://stacks.math.columbia.edu/tag/0EC1) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | There is no structure theorem for power-series torsion modules with commuting Leibniz operators; decomposition into injective hulls is the first frontier. |
| [0EC3](https://stacks.math.columbia.edu/tag/0EC3) | Ch. 51 Local Cohomology / §51.18 [Structure of certain modules](https://stacks.math.columbia.edu/tag/0EC1) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | There is no Frobenius-stable torsion-module structure theorem over a regular local ring; decomposition into copies of the residue-field injective hull is the first frontier. |
| [0EC7](https://stacks.math.columbia.edu/tag/0EC7) | Ch. 51 Local Cohomology / §51.19 [Additional structure on local cohomology](https://stacks.math.columbia.edu/tag/0EC4) | [58.29 / `0ECA`](https://stacks.math.columbia.edu/tag/0ECA) ×1 | `EtaleFundamentalGroups-required` | No canonical derivation action on cohomology of a quasi-compact quasi-separated étale scheme is defined; constructing these Leibniz operators is the first frontier. |
| [0ECI](https://stacks.math.columbia.edu/tag/0ECI) | Ch. 37 More on Morphisms / §37.67 [Pushouts in the category of schemes, II](https://stacks.math.columbia.edu/tag/0ECH) | [58.18 / `0EK3`](https://stacks.math.columbia.edu/tag/0EK3) ×1 | `context-only` | This tag only packages the standing hypotheses for the pushout situation; the pushout and finite-étale gluing results are separately represented by `0E25` and `0ECL`. |
| [0ECL](https://stacks.math.columbia.edu/tag/0ECL) | Ch. 37 More on Morphisms / §37.67 [Pushouts in the category of schemes, II](https://stacks.math.columbia.edu/tag/0ECH) | [58.18 / `0EK3`](https://stacks.math.columbia.edu/tag/0EK3) ×1 | `EtaleFundamentalGroups-required` | No equivalence glues flat or étale separated locally-quasi-finite schemes across the Ferrand pushout; that categorical equivalence is the first frontier. |
| [0EHN](https://stacks.math.columbia.edu/tag/0EHN) | Ch. 30 Cohomology of Schemes / §30.23 [Coherent formal modules](https://stacks.math.columbia.edu/tag/0EHN) | [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×1 | `EtaleFundamentalGroups-required` | The category of coherent formal modules and its equivalence with finite modules over an adic completion are absent; this category is the first frontier for §58.17. |
| [0EHW](https://stacks.math.columbia.edu/tag/0EHW) | Ch. 51 Local Cohomology / §51.11 [Finiteness of local cohomology, II](https://stacks.math.columbia.edu/tag/0BJQ) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | No depth and dimension comparison exists between a finite module and its adic completion under a dualizing-complex hypothesis; that equality is the first frontier. |
| [0EK2](https://stacks.math.columbia.edu/tag/0EK2) | Ch. 52 Algebraic and Formal Geometry / §52.15 [The completion functor](https://stacks.math.columbia.edu/tag/0EKN) | [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×1 | `EtaleFundamentalGroups-required` | The completion functor on coherent sheaves and its full-faithfulness criterion for finite locally free objects over shrinking neighbourhoods are absent. |
| [0EKP](https://stacks.math.columbia.edu/tag/0EKP) | Ch. 52 Algebraic and Formal Geometry / §52.15 [The completion functor](https://stacks.math.columbia.edu/tag/0EKN) | [58.17 / `0EJW`](https://stacks.math.columbia.edu/tag/0EJW) ×1; [58.26 / `0EY8`](https://stacks.math.columbia.edu/tag/0EY8) ×1 | `EtaleFundamentalGroups-required` | No implication chain connects section-completion isomorphisms, ample twists, finite locally free modules, and full faithfulness of coherent completion; that chain is the first frontier. |
| [0EKS](https://stacks.math.columbia.edu/tag/0EKS) | Ch. 52 Algebraic and Formal Geometry / §52.15 [The completion functor](https://stacks.math.columbia.edu/tag/0EKN) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | No theorem derives full faithfulness of coherent completion on finite locally free objects from annihilation of `H¹` and `H²` local cohomology. |
| [0EKT](https://stacks.math.columbia.edu/tag/0EKT) | Ch. 52 Algebraic and Formal Geometry / §52.15 [The completion functor](https://stacks.math.columbia.edu/tag/0EKN) | [58.19 / `0BLE`](https://stacks.math.columbia.edu/tag/0BLE) ×1 | `EtaleFundamentalGroups-required` | No dualizing-complex and depth criterion proves full faithfulness of coherent completion on finite locally free objects; this criterion is the first frontier. |
| [0EKU](https://stacks.math.columbia.edu/tag/0EKU) | Ch. 52 Algebraic and Formal Geometry / §52.15 [The completion functor](https://stacks.math.columbia.edu/tag/0EKN) | [58.22 / `0BLU`](https://stacks.math.columbia.edu/tag/0BLU) ×1 | `EtaleFundamentalGroups-required` | No completion theorem combines associated primes, cohomological dimension, and shrinking neighbourhoods to obtain full faithfulness on vector bundles. |
| [0EKV](https://stacks.math.columbia.edu/tag/0EKV) | Ch. 52 Algebraic and Formal Geometry / §52.15 [The completion functor](https://stacks.math.columbia.edu/tag/0EKN) | [58.22 / `0BLU`](https://stacks.math.columbia.edu/tag/0BLU) ×1 | `EtaleFundamentalGroups-required` | No principal-completion theorem derives full faithfulness on vector bundles from a nonzerodivisor and finite `H¹`; this criterion is the first frontier. |
| [0EKY](https://stacks.math.columbia.edu/tag/0EKY) | Ch. 52 Algebraic and Formal Geometry / §52.24 [Application to the completion functor](https://stacks.math.columbia.edu/tag/0EKX) | [58.23 / `0EK7`](https://stacks.math.columbia.edu/tag/0EK7) ×1 | `EtaleFundamentalGroups-required` | No algebraization equivalence for finite locally free coherent formal modules under the stated `S₂` or depth hypotheses exists. |
| [0EKZ](https://stacks.math.columbia.edu/tag/0EKZ) | Ch. 52 Algebraic and Formal Geometry / §52.24 [Application to the completion functor](https://stacks.math.columbia.edu/tag/0EKX) | [58.23 / `0EK7`](https://stacks.math.columbia.edu/tag/0EK7) ×1 | `EtaleFundamentalGroups-required` | No algebraization equivalence for vector bundles follows from finiteness of `H¹` and `H²` on the principal closed fibre; that equivalence is the first frontier. |
| [0EL1](https://stacks.math.columbia.edu/tag/0EL1) | Ch. 52 Algebraic and Formal Geometry / §52.28 [Application to Lefschetz theorems](https://stacks.math.columbia.edu/tag/0EL0) | [58.27 / `0ELB`](https://stacks.math.columbia.edu/tag/0ELB) ×1 | `EtaleFundamentalGroups-required` | No formal-functions comparison identifies cohomology on an open scheme with the inverse limit over infinitesimal neighbourhoods under the stated depth bound. |
| [0EL2](https://stacks.math.columbia.edu/tag/0EL2) | Ch. 52 Algebraic and Formal Geometry / §52.28 [Application to Lefschetz theorems](https://stacks.math.columbia.edu/tag/0EL0) | [58.27 / `0ELB`](https://stacks.math.columbia.edu/tag/0ELB) ×1 | `EtaleFundamentalGroups-required` | No Lefschetz-style global-section comparison with infinitesimal neighbourhoods of an ample divisor exists under the stated depth condition. |
| [0EL7](https://stacks.math.columbia.edu/tag/0EL7) | Ch. 52 Algebraic and Formal Geometry / §52.28 [Application to Lefschetz theorems](https://stacks.math.columbia.edu/tag/0EL0) | [58.27 / `0ELB`](https://stacks.math.columbia.edu/tag/0ELB) ×1 | `EtaleFundamentalGroups-required` | No equivalence algebraizes vector bundles from the formal completion along an ample divisor under the depth-plus-dimension bound; that completion equivalence is the first frontier. |
| [0EXW](https://stacks.math.columbia.edu/tag/0EXW) | Ch. 15 More on Algebra / §15.116 [Abhyankar's lemma and tame ramification](https://stacks.math.columbia.edu/tag/0EXT) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | The characterization of tame ramification in the indicated DVR tower is absent from CFT and mathlib. |
| [0EXY](https://stacks.math.columbia.edu/tag/0EXY) | Ch. 15 More on Algebra / §15.116 [Abhyankar's lemma and tame ramification](https://stacks.math.columbia.edu/tag/0EXT) | [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×1 | `EtaleFundamentalGroups-required` | The tame-ramification base-change and descent statement has no matching endpoint. |
| [0EY3](https://stacks.math.columbia.edu/tag/0EY3) | Ch. 32 Limits of Schemes / §32.20 [Glueing in closed fibres](https://stacks.math.columbia.edu/tag/0E8P) | [58.21 / `0BJE`](https://stacks.math.columbia.edu/tag/0BJE) ×1; [58.31 / `0BSE`](https://stacks.math.columbia.edu/tag/0BSE) ×2 | `EtaleFundamentalGroups-required` | No theorem extends separated, proper, finite, or étale properties from the two pieces of the local gluing equivalence after shrinking the ambient open. |
| [0G1C](https://stacks.math.columbia.edu/tag/0G1C) | Ch. 10 Commutative Algebra / §10.151 [Unramified ring maps](https://stacks.math.columbia.edu/tag/00US) | [58.32 / `0G1E`](https://stacks.math.columbia.edu/tag/0G1E) ×1 | `EtaleFundamentalGroups-required` | The local dimension and differential-generator characterization of étale maps in this tag has no matching endpoint. |
| [0G7Y](https://stacks.math.columbia.edu/tag/0G7Y) | Ch. 36 Derived Categories of Schemes / §36.32 [Applications](https://stacks.math.columbia.edu/tag/0BDM) | [58.15 / `0BUM`](https://stacks.math.columbia.edu/tag/0BUM) ×1 | `EtaleFundamentalGroups-required` | No derived splitting of `Rf_*𝒪_X` into a finite étale algebra and a positive-amplitude perfect summand exists for proper flat families with geometrically reduced fibre. |
| [0GS9](https://stacks.math.columbia.edu/tag/0GS9) | Ch. 37 More on Morphisms / §37.37 [Unramified and étale morphisms](https://stacks.math.columbia.edu/tag/0GS7) | [58.11 / `0BQJ`](https://stacks.math.columbia.edu/tag/0BQJ) ×1 | `EtaleFundamentalGroups-required` | No theorem upgrades a connected unramified morphism over an integral geometrically-unibranch base to étale and irreducible under a dominating-component hypothesis. |

### Raw-source-only supplement

These literal references occur in pinned `pione.tex` but are absent from the rendered
`content/full` payloads. They are part of the final classification gate.

| Tag | Owning chapter / section | Chapter 58 source | Lean classification | Evidence |
|---|---|---|---|---|
| [0033](https://stacks.math.columbia.edu/tag/0033) | Ch. 4 Categories / §4.23 [Exact functors](https://stacks.math.columbia.edu/tag/0033) | [58.3 / `0BMQ`](https://stacks.math.columbia.edu/tag/0BMQ), footnote in Definition 58.3.6 | `context-only` | The raw footnote only fixes the term exact functor; native ownership is `PreservesFiniteLimits` together with `PreservesFiniteColimits`. |
| [0EKE](https://stacks.math.columbia.edu/tag/0EKE) | Ch. 29 Morphisms of Schemes / Lemma 29.43.18 | [58.27 / `0ELB`](https://stacks.math.columbia.edu/tag/0ELB), footnote in Proposition 58.27.3 | `EtaleFundamentalGroups-required` | Mathlib has projective spectra, but no relative-ampleness endpoint proving that the nonvanishing locus of a section over a universally closed base is affine. |

### Classification gate

All 286 entries are classified: 55 `mathlib-covered`, 3 `Pi1-covered`,
1 `EtaleFundamentalGroups-implemented`, 204 `EtaleFundamentalGroups-required`, and
23 `context-only`; there are no
`ProCGroups-covered` or `CFT-covered` entries. A `covered` result names the exact public
Lean declaration and must not transitively depend on a `sorry` or `proof_wanted`.
Only `EtaleFundamentalGroups-required` dependencies actually used by the first unresolved
Chapter 58 frontier should become source-producing work.

## 6. Historical handoff (2026-07-30; non-authoritative)


### 1. Goal

Complete Stacks Project Chapter 58, **Fundamental Groups of Schemes** (Tag
`0BQ6`), in `EtaleFundamentalGroups`.

- Import the existing `Pi1` library without redefining it.
- Change `Pi1` only when an actual error or placeholder must be repaired.
- Reuse canonical mathlib/Pi1 definitions and public theorems.
- Do not add parallel definitions, theorem-valued assumptions, unnecessary
  wrappers, or proof escapes (`sorry`, `admit`, `axiom`, unsafe shortcuts,
  disabling warnings, etc.).
- Completion means all numbered tags, unnumbered body claims, and required
  external dependencies are implemented or matched exactly, all ledgers have
  no unresolved entries, and the complete public library passes strict builds
  and audits.

This goal is **not complete** and must remain active.

### 2. Authoritative paths

- Workspace: `/home/nyama/work`
- Project:
  `/home/nyama/work/Lean4/EtaleFundamentalGroups`
- Public facade:
  `/home/nyama/work/Lean4/Progress（import禁止）(指示があるまで変更禁止)/EtaleFundamentalGroups.lean`
- Existing imported library:
  `/home/nyama/work/Lean4/Progress（import禁止）(指示があるまで変更禁止)/Pi1`
- Plan and ledgers:
  - `EtaleFundamentalGroups/PLAN.md`
  - `EtaleFundamentalGroups/STACKS_TAGS.md`
  - `EtaleFundamentalGroups/BODY_CLAIMS.md`
  - `EtaleFundamentalGroups/EXTERNAL_TAGS.md`

The historical snapshots `20260730-101037` and `20260730-100324` were removed
during the 2026-08-05 capacity cleanup and are not recovery sources. In
particular, do not reconstruct the failed `ForgetFiniteCoproducts.lean`
experiment formerly present in `20260730-100324`: its central
`infer_instance` is mathematically inapplicable.

### 3. Verified stopping state

The public source tree is green.

- All **31 current Chapter58 source modules plus the facade** were explicitly
  requested in one strict build.
- Result: `Build completed successfully (3455 jobs)`.
- Warning/error count: 0.
- The newly added public results have only the standard axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- Proof-escape scans are clean.
- The one pre-existing, justified body-backed `noncomputable opaque` in
  `SchemesEtaleOverPoint/Equivalence.lean` is intentional; do not replace it
  merely to remove the word `opaque`.
- No git operation and no `.lake` deletion was performed.

The failed finite-coproduct scratch module was removed before the final build,
so there is no unimported broken `.lean` file at this stopping point.

### 4. Mathematical progress

#### Abstract Galois-category part

Mathlib already owns the canonical definitions:

- `CategoryTheory.PreGaloisCategory`
- `CategoryTheory.PreGaloisCategory.FiberFunctor`
- `CategoryTheory.GaloisCategory`
- `CategoryTheory.PreGaloisCategory.functorToContAction`

Pi1 proves that finite étale covers of a connected scheme form a Galois
category and defines the étale fundamental group as the automorphism group of
the geometric fiber functor. Chapter58 does not redefine any of these objects.

The numbered results in §58.3 and §58.4 are complete through:

- 0BMU, 0BMV, 0BN5
- 0BN6, 0BS8, 0BS9, 0BN7, 0BTS

§58.5 currently has:

- 58.5.1 / 0BN8: covered by Pi1
- 58.5.2 / 0BN9: covered by Pi1
- 58.5.3 / 0BNA: partially implemented, described below
- 58.5.4 / 0BL7: researched but not implemented
- 58.5.5 / 0BNB: covered by Pi1

#### Current ledger counts

`STACKS_TAGS.md` has 141 rows:

- `implemented`: 10
- `covered`: 16
- `non-propositional`: 5
- `planned`: 24
- `blocked`: 86

Thus there are 136 propositional/formal targets, 26 complete and 110 pending.

`BODY_CLAIMS.md` has 33 claims:

- complete: 14 (`covered` 11 + `implemented` 3)
- pending: 19 (`planned` 10 + `blocked` 9)

`EXTERNAL_TAGS.md` has the exact 286-tag boundary:

- `mathlib-covered`: 55
- `Pi1-covered`: 3
- `context-only`: 23
- `EtaleFundamentalGroups-implemented`: 1
- `EtaleFundamentalGroups-required`: 204

### 5. Current frontier: 58.5.3 / Tag 0BNA

For

\[
F_2:\mathrm{FÉt}_X\to\mathrm{Sch}/X,\qquad
F_1:\mathrm{FÉt}_X\to\mathrm{Sch},
\]

use the canonical functors directly:

- `F₂ = AlgebraicGeometry.FiniteEtale.forget X`
- `F₁ = FiniteEtale.forget X ⋙ CategoryTheory.Over.forget X`

Do not define `F₁` or `F₂` wrappers.

#### Finished: limit preservation

File:

`SchemeTheory/FiniteEtale/Forget/FiniteLimits.lean`

Public instances:

- `FiniteEtale.forgetPreservesFiniteLimits`
- `FiniteEtale.forgetCompOverForgetPreservesPullbacks`
- `FiniteEtale.forgetCompOverForgetPreservesEqualizers`

They use the existing `MorphismProperty.Over` finite-limit instance and
connected-limit preservation of `Over.forget`. There are no extra assumptions
or replacement definitions.

#### Finished external dependency: Descent 35.13.8 / Tag 0BMN

File:

`SchemeTheory/Descent/FpqcLocalCoequalizer.lean`

Public theorem:

`AlgebraicGeometry.Scheme.isColimit_cofork_of_fpqc_local`

It is tagged `@[stacks 0BMN]` and formalizes the official statement exactly:

- an fpqc family over `Z`;
- the pulled-back cofork is a coequalizer over every cover member;
- it is a coequalizer over every pairwise overlap;
- therefore the original cofork is a coequalizer.

The proof uses the subcanonical fpqc topology, effective-epimorphic families,
pullback stability, descent on overlaps, and no additional hypothesis.

Checks:

- strict target build: 2650/2650
- facade build after import: 3456 jobs
- warning/error: 0
- standard three axioms only

#### Finished: finite coproduct preservation

File:

`SchemeTheory/FiniteEtale/Forget/FiniteCoproducts.lean`

Public instances:

- `FiniteEtale.forgetPreservesFiniteCoproducts`
- `FiniteEtale.forgetCompOverForgetPreservesFiniteCoproducts`

The proof establishes closure under the initial object and binary coproduct,
creates the corresponding colimits through
`MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed`, and combines
them with `PreservesFiniteCoproducts.of_preserves_binary_and_initial`. It does
not use the invalid generic `LimitsOver` route requiring source-locality of
finiteness. The strict target build completed in 2939 jobs and the integrated
facade build completed in 3455 jobs, both with warning/error count 0.

#### Remaining part B: coequalizer preservation

Create:

`EtaleFundamentalGroups/FiniteEtale/ForgetCoequalizers.lean`

For an arbitrary
`WalkingParallelPair ⥤ FiniteEtale X`, take its existing Pi1 colimit cofork,
map it to schemes, and apply
`Scheme.isColimit_cofork_of_fpqc_local`.

The local proof must identify the finite étale diagram with

\[
\coprod_{j\in J} U \rightrightarrows
\coprod_{i\in I} U \longrightarrow
\coprod_{t\in\operatorname{Coeq}(a,b)} U.
\]

Relevant existing Pi1 APIs:

- `Algebra.exists_isFiniteSplit`
- `AlgHom.exists_cover_eq_compRight''₂`
- `AlgHom.equalizerCompRightEquiv`
- `AlgHom.tensorEqualizerEquiv`
- `Algebra.FiniteEtale.equalizer_fun`

No theorem-valued “local coequalizer” assumption may be added.

After obtaining coequalizer preservation for `F₁`, use canonical reflection
through `Over.forget X` to obtain it for `F₂`. Then use
`preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts` for
both functors. At that point Tag 0BNA may be changed from `planned` to
`implemented`.

### 6. Next numbered frontier: 58.5.4 / Tag 0BL7

The canonical endpoint should use mathlib's `Functor.RepresentableBy`, not a
new relative-Hom functor or Hom type. For finite étale `U,V/X`, the intended
shape is:

```lean
∃ W : FiniteEtale X,
  Nonempty
    (((tensorRight ((FiniteEtale.forget X).obj U)).op ⋙
        yoneda.obj ((FiniteEtale.forget X).obj V)).RepresentableBy
      ((FiniteEtale.forget X).obj W))
```

This natural representability statement already includes compatibility with
arbitrary base change.

Minimal dependency order found by the read-only audit:

1. Tag 05Y6: affine relative Hom for a finite free affine source.
2. Tag 0BL3: extend to a finite locally free source and affine target.
3. Tag 04HN: étale-local trivialization of finite étale morphisms.
4. Tag 02LA: fpqc descent of finiteness.
5. Use the existing mathlib fpqc descent of `Etale`.
6. Publish the `RepresentableBy` result for 0BL7.

The general relative-Hom theorem 0BL5 and separatedness descent 02KU are not
needed on this shorter finite-étale route because the target is itself finite,
hence affine. A Galois-category-only proof is also insufficient: Pi1's
Galois-category instance assumes the base scheme is connected, while 0BL7 is
for an arbitrary scheme.

### 7. Safe restart procedure

1. Read `/home/nyama/work/AGENTS.md` and this handoff.
2. Do not back up before ordinary source edits. Follow the bounded policy in
   `/home/nyama/work/AGENTS.md`.
3. Work only in the Chapter58 project unless an actual Pi1 error/placeholder is
   proved necessary.
4. Implement the finite-étale local split coequalizer proof.
5. Do not import a new module into `EtaleFundamentalGroups.lean` until its individual
   `--wfail` build and audits pass.
6. After integration, explicitly build every source module plus the facade,
   not only the facade target.
7. Update all three ledgers and `PLAN.md`, then invoke the backup script at
   most once at task completion. Record either `CREATED` or `SKIPPED`; do not
   retry a skipped backup in the same task.

Use the full Lake path if a non-login WSL shell cannot find `lake`:

```text
/home/nyama/.elan/bin/lake
```

Do not run git operations, delete `.lake`, restore an old snapshot over the
current tree, or introduce a substitute definition merely to make a target
compile.
