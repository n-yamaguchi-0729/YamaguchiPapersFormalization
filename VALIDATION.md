# 初回配布時の検証

日付: 2026-10-11 (Asia/Tokyo)。分割元コミット: `1b2c6f3b3ff64e9c762296e5d41b7dd35ff0b0ef`。

- 収録したライブラリの Lean ソースは分割元とバイト一致。新しい全体入口 `Lean4/All.lean` だけを配布範囲に合わせて生成。
- 全 8,220 モジュールについて、全ソース到達、Lake glob、欠落 import、循環、逆依存の静的検査に合格。
- 以下は分割元の同じ固定 toolchain / mathlib / linter 設定で行った通常の増分ビルド。依存深さの浅い順に各ライブラリの完了を待った。
- 各配布物の新しい `Lean4/All.lean` を、その検証済み依存成果物を使って Lean で型検査した。
- クリーン checkout の GitHub Actions 実行および独立証明検査の結果ではない。private 作成時の自動ジョブはスキップし、手動実行はまだ行っていない。

| ライブラリ | 結果 |
|---|---|
| ProCGroups.All | `lake --wfail build +ProCGroups.All` 成功、警告・エラーなし。 |
| ValuedFieldTheory.All | `lake --wfail build +ValuedFieldTheory.All` 成功、警告・エラーなし。 |
| GaloisCohomology.All | `lake --wfail build +GaloisCohomology.All` 成功、警告・エラーなし。 |
| SchemeTheory.All | `lake --wfail build +SchemeTheory.All` 成功、警告・エラーなし。 |
| ClassFieldTheory.All | `lake --wfail build +ClassFieldTheory.All` 成功、警告・エラーなし。 |
| AlgebraicCurves.All | `lake --wfail build +AlgebraicCurves.All` 成功、警告・エラーなし。 |
| EtaleFundamentalGroups.All | `lake --wfail build +EtaleFundamentalGroups.All` 成功、警告・エラーなし。 |
| EtaleCohomology.All | `lake --wfail build +EtaleCohomology.All` 成功、警告・エラーなし。 |
| Yamaguchi26AbfaithfulGalois.All | `lake --wfail build +Yamaguchi26AbfaithfulGalois.All` 成功、警告・エラーなし。 |
| Yamaguchi26SolvableCoverings.All | `lake --wfail build +Yamaguchi26SolvableCoverings.All` 成功、警告・エラーなし。 |

静的検査はマクロ展開・全宣言の公理依存を検査するものではありません。通常ビルドと数学的範囲の確認を、ソース上の語句検査のみで代用していません。
