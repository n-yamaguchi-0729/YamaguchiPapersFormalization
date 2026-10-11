# 第三者由来のコードと帰属

ライセンスは [Apache License 2.0](LICENSE) です。各 Lean ファイルの元の著作権・Authors・出典表示を保持しています。独自作成部分の著作権者は [Naganori Yamaguchi](https://github.com/n-yamaguchi-0729)、著者表示は Naganori Yamaguchi (assisted by OpenAI Codex) です。

- **pi1**: Christian Merten の [chrisflav/pi1](https://github.com/chrisflav/pi1) 由来25ファイルを、SchemeTheory と EtaleFundamentalGroups に取り込み、修正・再配置しています。[個別の対応表](PI1_ATTRIBUTION.md) を参照してください。比較 revision と正確なコピー元コミットは区別し、権利者が未確認の箇所を推測で確定していません。
- **Anthropic Fermat's Last Theorem**: [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem)、比較 revision `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`。Copyright 2026 Anthropic, PBC。曲線・Jacobian・スキームのコードを取り込み、配置、import、Lean/mathlib API、証明を適応しています。各ファイルの改変元 URL と未解決の対応も保持しています。
- **FLT のさらに上流**: [ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT)、[flt-regular](https://github.com/leanprover-community/flt-regular)、[mathlib](https://github.com/leanprover-community/mathlib4) からの帰属は、保存した上流 NOTICE と ATTRIBUTION を参照してください。そこにある “this repository” や件数は上流リポジトリの説明であり、この配布物の件数ではありません。
- **mathlib と Lean**: 数学・言語処理系の基礎を利用しています。外部依存を vendoring せず、正確な revision と upstream URL を `lake-manifest.json` に保持しています。
- **CI の参考と再利用**: [ProCGroups の静的インベントリ](https://github.com/n-yamaguchi-0729/ProCGroups/blob/main/.github/verification/generate_manifest.py) と、分割元 lean4-math-library の段階ビルド・診断分類・キャッシュ容量検査を利用しています。新しい配布範囲と private 手動実行に合わせて設定を変更しました。

## 保存した FLT の原表示

- SchemeTheory: [NOTICE](Lean4/SchemeTheory/ANTHROPIC_FLT_NOTICE)、[ATTRIBUTION](Lean4/SchemeTheory/ANTHROPIC_FLT_ATTRIBUTION.md)、[取り込み元](Lean4/SchemeTheory/ANTHROPIC_FLT_SOURCE.md)
- AlgebraicCurves: [NOTICE](Lean4/AlgebraicCurves/ANTHROPIC_FLT_NOTICE)、[ATTRIBUTION](Lean4/AlgebraicCurves/ANTHROPIC_FLT_ATTRIBUTION.md)、[取り込み元](Lean4/AlgebraicCurves/ANTHROPIC_FLT_SOURCE.md)
