# YamaguchiPapersFormalization (Lean 4.35.0-rc2)

[![Lean](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/YamaguchiPapersFormalization/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

A Lean 4 library formalizing Naganori Yamaguchi's papers.

This library is extracted from [NYLL](https://github.com/n-yamaguchi-0729/NYLL).
Bundled dependencies use the same `Nyll` imports as the complete library.

## Scope

Naganori Yamaguchi, [*Ab-faithfulness of absolute Galois groups in number theory*](https://arxiv.org/abs/2610.05634).

Ab-faithfulness concerns the faithful conjugation action of finite quotients on
the abelianizations of open normal subgroups. The library develops its
group-theoretic criteria and arithmetic applications.

Naganori Yamaguchi, [*Extension of solvable coverings across horizontal divisors over the integers*](https://arxiv.org/abs/2610.02948).

For a connected locally Noetherian scheme `X` and a horizontal effective
Cartier divisor `D`, the library studies the actual map of étale fundamental
groups induced by `X ∖ Supp(D) → X`.

The collection also includes an ongoing formalization of
[*On branched coverings of the projective line over the integers*](https://arxiv.org/abs/2608.15057v1),
using the numbering of arXiv v1. It develops arithmetic intersection calculations
for rational sections and concrete quadratic covers of their complements.

## Main results

### Ab-faithfulness of absolute Galois groups

| Result | Mathematical content |
| --- | --- |
| [Theorem 3.6](Nyll/Yamaguchi26AbfaithfulGalois/Theorem3Dot6MixedCharacteristic.lean) | The absolute Galois group of a mixed-characteristic discretely valued field is `p`-ab-faithful, where `p` is the residue characteristic. Completeness is not required. |
| [Theorem 4.2](Nyll/Yamaguchi26AbfaithfulGalois/Theorem4Dot2HigherLocalFields.lean) | Ab-faithfulness of the absolute Galois group of a higher local field of positive dimension. |
| [Theorem 6.4](Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot4RelativeCriterion.lean) and [Corollary 6.5](Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot5GroupCriterion.lean) | Center-freeness and slimness criteria for finite-step solvable quotients, using ab-faithfulness and orientations satisfying formal Hilbert 90. |
| [Corollary 6.6](Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot6AbsoluteCenter.lean) | Applications to absolute Galois groups, with the cyclotomic and positive-characteristic hypotheses stated in the paper. |
| [Example 6.7(1)–(3)](Nyll/Yamaguchi26AbfaithfulGalois/Theorem6Dot7FieldSlimExamples.lean) | Applications to torally Kummer-faithful ab-faithful fields of characteristic zero, sub-`p`-adic fields, and higher local fields. |

### Extension of solvable coverings

| Result | Mathematical content |
| --- | --- |
| [Lemma 1.1](Nyll/Yamaguchi26SolvableCoverings/Theorem1Dot1BoundaryQuotient.lean) and [Lemma 1.2](Nyll/Yamaguchi26SolvableCoverings/Theorem1Dot2InertiaControl.lean) | Surjectivity and normal generation of the kernel by boundary inertia, together with prime-to-residue-characteristic restrictions on finite inertia images. |
| [Proposition 1.3](Nyll/Yamaguchi26SolvableCoverings/Theorem1Dot3BoundaryInvariance.lean) | Invariance of the full étale fundamental group under the paper's boundary hypotheses for every prime. |
| [Example 1.4: Spec ℤ](Nyll/Yamaguchi26SolvableCoverings/Theorem1Dot4FundamentalGroupIntegers.lean) | Triviality of the étale fundamental group of `Spec ℤ`, using Minkowski's discriminant bound. |
| [Theorem 2.5 / Theorem A](Nyll/Yamaguchi26SolvableCoverings/Theorem2Dot5PerfectKernel.lean) | Under boundary condition `(†)`, the kernel is topologically perfect and the inclusion induces an isomorphism on maximal prosolvable quotients. |
| [Corollary 2.6](Nyll/Yamaguchi26SolvableCoverings/Theorem2Dot6ResidualExtension.lean) | A continuous matrix representation over a complete Noetherian local ring with finite residue field extends across the divisor exactly when its residual representation does; the extension is unique. |

The formalization includes numbered results 2.1–2.6 and the supporting boundary and
finite-étale stability results.

The shared group theory also contains the center-freeness criterion of
Proposition 2.5 in [*Center-freeness of finite-step solvable groups arising from anabelian geometry*](https://arxiv.org/abs/2601.07112),
in [SlimnessAndTorsion.lean](Nyll/ProCGroups/FiniteStepSolvableQuotients/SlimnessAndTorsion.lean).

### Branched coverings of the projective line over the integers

| Result | Mathematical content |
| --- | --- |
| [Lemma 2.3: intersection calculations](Nyll/ShimizuYamaguchi26BranchedCoverings/Theorem2Dot3IntersectionMultiplicity.lean) | Local intersection multiplicities for rational sections, with supporting normal-crossing constructions. |
| [Lemma 2.4](Nyll/ShimizuYamaguchi26BranchedCoverings/Theorem2Dot4DyadicCollision.lean) | The dyadic collision calculation for primitive section coordinates. |
| [Proposition 2.5: quadratic quotient](Nyll/ShimizuYamaguchi26BranchedCoverings/Theorem2Dot5QuadraticQuotient.lean) | A connected quadratic cover supplies a quotient of the actual etale fundamental group under the stated determinant conditions. |
| [Corollary 2.7: at least seven sections](Nyll/ShimizuYamaguchi26BranchedCoverings/Theorem2Dot7LargeBoundaryQuotient.lean) | The complement of at least seven rational sections has a continuous quotient onto the cyclic group of order two, at every geometric point of the constructed open. |

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

**Branched coverings of the projective line over the integers**

The full finite-divisor normal-crossing criterion and its comparison over `Z_p`,
the remaining geometric hypotheses of the paper statements, and the main quotient
criteria are not yet included. The results above cover the stated calculations
and constructions, not the entire paper.

## Public API

```lean
import Nyll.Yamaguchi26AbfaithfulGalois.All
import Nyll.Yamaguchi26SolvableCoverings.All
import Nyll.ShimizuYamaguchi26BranchedCoverings.All
```

Selected results:

```lean
import Nyll.Yamaguchi26AbfaithfulGalois.Theorem3Dot6MixedCharacteristic
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot5PerfectKernel
```

## Build

The toolchain and dependencies are pinned in [`lean-toolchain`](lean-toolchain)
and [`lakefile.toml`](lakefile.toml).

```console
lake exe cache get
lake --wfail build
```

[CI](.github/workflows/lean.yml) checks imports and builds the libraries
with warnings treated as errors.

## Authorship

All original code in this library is written by OpenAI Codex.

[Naganori Yamaguchi](https://github.com/n-yamaguchi-0729) sets the mathematical
goals and scope, directs development, and maintains the library.
Naganori Yamaguchi is also the author of the papers formalized here.

## License and acknowledgements

Apache License 2.0. See [LICENSE](LICENSE).
Supporting code includes adaptations from [pi1](https://github.com/chrisflav/pi1)
and [Anthropic FLT](https://github.com/anthropics/fermats-last-theorem); see [NOTICE](NOTICE).
