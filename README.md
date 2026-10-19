# YamaguchiPapersFormalization (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Developed within [NYLL](https://github.com/n-yamaguchi-0729/NYLL), this Lean library formalizes Naganori Yamaguchi’s
papers on ab-faithfulness of absolute Galois groups and extension of solvable
coverings across horizontal divisors. The [mathematical guide](https://n-yamaguchi-0729.github.io/NYLL/libraries/research-papers/) explains the selected arithmetic
and geometric results, while the sections below relate them to the papers
and identify the parts that remain unfinished.

## Scope

Naganori Yamaguchi, [*Ab-faithfulness of absolute Galois groups in number theory*](https://arxiv.org/abs/2610.05634).

Ab-faithfulness concerns the faithful conjugation action of finite quotients on
the abelianizations of open normal subgroups. The library develops its
group-theoretic criteria and arithmetic applications.

Naganori Yamaguchi, [*Extension of solvable coverings across horizontal divisors over the integers*](https://arxiv.org/abs/2610.02948).

For a connected locally Noetherian scheme `X` and a horizontal effective
Cartier divisor `D`, the library studies the map of étale fundamental
groups induced by `X ∖ Supp(D) → X`.

## Main results

### Ab-faithfulness of absolute Galois groups

| Result | Mathematical content |
| --- | --- |
| [Theorem 4.2](Nyll/Yamaguchi26AbfaithfulGalois/Theorem4Dot2HigherLocalFields.lean) | Ab-faithfulness of the absolute Galois group of a higher local field of positive dimension. |
| [Toral fields](Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot7FieldSlimExamples.lean#L52); [Finitely generated fields](Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot7FieldSlimExamples.lean#L88); [Sub-p-adic fields](Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot7FieldSlimExamples.lean#L68); [Higher local fields](Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot7FieldSlimExamples.lean#L114) | For every m ≥ 2, slimness is proved directly for infinite fields finitely generated over their prime field, fields embedding into a finitely generated extension of Q_p, and positive-dimensional higher local fields. The separate toral application assumes characteristic zero, toral Kummer-faithfulness and ab-faithfulness. Slimness means every open subgroup has trivial centralizer in the ambient quotient. |

### Extension of solvable coverings

| Result | Mathematical content |
| --- | --- |
| [Theorem 2.5 / Theorem A](Nyll/Yamaguchi26SolvableCoverings/Theorem2Dot5PerfectKernel.lean) | Under boundary condition `(†)`, the kernel is topologically perfect and the inclusion induces an isomorphism on maximal prosolvable quotients. |
| [Corollary 2.6](Nyll/Yamaguchi26SolvableCoverings/Theorem2Dot6ResidualExtension.lean) | A continuous matrix representation over a complete Noetherian local ring with finite residue field extends across the divisor exactly when its residual representation does; the extension is unique. |

## Incomplete results

**Ab-faithfulness of absolute Galois groups**

The numbered development in Sections 1–6 is included except for Example 2.2
and Lemma 6.8. Proposition 5.2 is proved under its split embedding-problem
hypothesis; the general Hilbertian-field application still requires Ikeda's
theorem. These applications and the PAC-field counterexample of Lemma 6.8
are outside the current formalization.

**Extension of solvable coverings**

Example 1.4 is limited to `Spec ℤ`: the affine
and projective spaces, moduli-space and plane-complement examples, and
Corollary 2.7 on hyperplane arrangements are not yet included.

## Public API

Use [leanprover/lean4:v4.35.0-rc2](lean-toolchain) and the Mathlib revision pinned in
[lake-manifest.json](lake-manifest.json). Add this dependency to your project’s
lakefile.toml:

```toml
[[require]]
name = "Nyll"
git = "https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization.git"
rev = "main"
```

Run `lake update Nyll`, then commit your generated lake-manifest.json to retain
the resolved revisions. Import the library in a Lean file:

```lean
import Nyll.Yamaguchi26AbfaithfulGalois.All
import Nyll.Yamaguchi26SolvableCoverings.All
```

The standalone distributions share the package name Nyll. Choose one distribution;
for several libraries together, use [NYLL](https://github.com/n-yamaguchi-0729/NYLL).

To build a checkout of this repository, run from its root:

```sh
lake exe cache get
lake --wfail build
```

## Authorship

All original code in this library is written by OpenAI Codex.

[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) sets the mathematical
goals and scope, directs development, and maintains the library.
Naganori Yamaguchi is also the author of the papers formalized here.

## License and acknowledgements

<!-- nyll-publication:credits:begin -->
Apache License 2.0. See [LICENSE](LICENSE).

Included adaptations from [pi1](https://github.com/chrisflav/pi1) and [Anthropic’s Fermat’s Last Theorem project](https://github.com/anthropics/fermats-last-theorem) retain their source-specific copyrights and authors.
The included-file inventories and preserved upstream notices are in [NOTICE](NOTICE).
<!-- nyll-publication:credits:end -->
