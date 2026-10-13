# pi1 attribution for this extract

Upstream: [chrisflav/pi1](https://github.com/chrisflav/pi1); Apache-2.0.
Comparison revision: `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`. [Upstream license](LICENSE).
The exact commit historically copied into NYLL remains unverified; the
comparison revision is not asserted to be the original import revision.
Missing upstream copyright notices do not establish a copyright holder.
The entries below retain the current source headers and distinguish local
NYLL extensions from adapted upstream ports. Only included files are listed.

## [Nyll/EtaleFundamentalGroups/GeometricFiber/FundamentalGroup.lean](../GeometricFiber/FundamentalGroup.lean)

Role: `nyll_extension`.

Nyll completions of upstream Point.lean placeholders and dependent fiber-action/fundamental-group repairs; existing IsSepClosed and IsSepClosure assumptions preserved.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/FundamentalGroup/Point.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Point.lean)

## [Nyll/EtaleFundamentalGroups/Pi1/FiniteEtale/GaloisCategory.lean](FiniteEtale/GaloisCategory.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/FundamentalGroup/Galois.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Galois.lean)

## [Nyll/EtaleFundamentalGroups/Pi1/GaloisCategories/FundamentalGroup.lean](GaloisCategories/FundamentalGroup.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright or Authors header. Its copyright holder
requires review. The Authors line above is retained from the previous NYLL
integration and is not a verbatim attribution from the cited upstream file.
```

- [Upstream `Pi1/Mathlib/CategoryTheory/Galois/IsFundamentalGroup.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/CategoryTheory/Galois/IsFundamentalGroup.lean)

## [Nyll/EtaleFundamentalGroups/Pi1/GeometricFiber/FieldPoints.lean](GeometricFiber/FieldPoints.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/FundamentalGroup/Point.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Point.lean)

## [Nyll/SchemeTheory/Descent/EqualizerScalars.lean](../../SchemeTheory/Descent/EqualizerScalars.lean)

Role: `nyll_extension`.

Nyll forward-map computation AlgHom.equalizerRestrictScalars_apply, split from the scalar-restriction comparison.

```text
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
```

- [Upstream `Pi1/Mathlib/RingTheory/Flat/Equalizer.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Flat/Equalizer.lean)

## [Nyll/SchemeTheory/FiniteEtale/Algebra/EtaleSplitting.lean](../../SchemeTheory/FiniteEtale/Algebra/EtaleSplitting.lean)

Role: `nyll_extension`.

Nyll etale-neighbourhood refinement Algebra.exists_etale_isFiniteSplit, stronger than the referenced upstream splitting construction.

```text
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
```

- [Upstream `Pi1/RingTheory/KerTensor.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/KerTensor.lean)

## [Nyll/SchemeTheory/Pi1/Affine/Over.lean](../../SchemeTheory/Pi1/Affine/Over.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/FundamentalGroup/AffineColimits.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/AffineColimits.lean)

## [Nyll/SchemeTheory/Pi1/Affine/Property.lean](../../SchemeTheory/Pi1/Affine/Property.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/FundamentalGroup/AffineAnd.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/AffineAnd.lean)

## [Nyll/SchemeTheory/Pi1/Descent/EqualizerScalars.lean](../../SchemeTheory/Pi1/Descent/EqualizerScalars.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Flat/Equalizer.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/RingTheory/Flat/Equalizer.lean
```

- [Upstream `Pi1/Mathlib/RingTheory/Flat/Equalizer.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Flat/Equalizer.lean)

## [Nyll/SchemeTheory/Pi1/Descent/FlatEqualizer.lean](../../SchemeTheory/Pi1/Descent/FlatEqualizer.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Flat/Equalizer.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/RingTheory/Flat/Equalizer.lean
```

- [Upstream `Pi1/Mathlib/RingTheory/Flat/Equalizer.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Flat/Equalizer.lean)

## [Nyll/SchemeTheory/Pi1/Etale/RingHom.lean](../../SchemeTheory/Pi1/Etale/RingHom.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Etale.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/RingTheory/RingHom/Etale.lean
```

- [Upstream `Pi1/Mathlib/RingTheory/RingHom/Etale.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Etale.lean)

## [Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Basic.lean](../../SchemeTheory/Pi1/FiniteEtale/Algebra/Basic.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Basic.lean
```

- [Upstream `Pi1/RingTheory/FiniteEtale/Basic.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Basic.lean)

## [Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Descent.lean](../../SchemeTheory/Pi1/FiniteEtale/Algebra/Descent.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Descent.lean
```

- [Upstream `Pi1/RingTheory/FiniteEtale/Descent.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Descent.lean)

## [Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Equalizer.lean](../../SchemeTheory/Pi1/FiniteEtale/Algebra/Equalizer.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated. Removed IsIdempotentElem.eq_one_of_isUnit proof; two uses now call canonical iff .mp directly. Zero branch uses canonical sub_eq_self.mp.

```text
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Equalizer.lean
```

- [Upstream `Pi1/RingTheory/FiniteEtale/Equalizer.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Equalizer.lean)

## [Nyll/SchemeTheory/Pi1/FiniteEtale/Algebra/Splitting.lean](../../SchemeTheory/Pi1/FiniteEtale/Algebra/Splitting.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/KerTensor.lean
```

- [Upstream `Pi1/RingTheory/KerTensor.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/KerTensor.lean)

## [Nyll/SchemeTheory/Pi1/FiniteEtale/Basic.lean](../../SchemeTheory/Pi1/FiniteEtale/Basic.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/FundamentalGroup/FiniteEtale.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/FiniteEtale.lean)

## [Nyll/SchemeTheory/Pi1/FiniteEtale/Geometry.lean](../../SchemeTheory/Pi1/FiniteEtale/Geometry.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/FundamentalGroup/Galois.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Galois.lean)

## [Nyll/SchemeTheory/Pi1/Morphisms/Finite.lean](../../SchemeTheory/Pi1/Morphisms/Finite.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean)

## [Nyll/SchemeTheory/Pi1/Morphisms/Flat.lean](../../SchemeTheory/Pi1/Morphisms/Flat.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean
```

- [Upstream `Pi1/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean)

## [Nyll/SchemeTheory/Pi1/Morphisms/Smooth.lean](../../SchemeTheory/Pi1/Morphisms/Smooth.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated. Removed Smooth.ofLocalizationSpan wrapper; canonical PropertyIsLocal owner imported directly.

```text
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
```

- [Upstream `Pi1/Mathlib/RingTheory/RingHom/Smooth.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Smooth.lean)

## [Nyll/SchemeTheory/Pi1/RingTheory/QuotientProducts.lean](../../SchemeTheory/Pi1/RingTheory/QuotientProducts.lean)

Role: `adapted_upstream_port`.

Maintained adaptation: namespace/declaration ownership retained, paths/imports and Lean/mathlib APIs updated.

```text
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Ideal/Quotient/Operations.lean
```

- [Upstream `Pi1/Mathlib/RingTheory/Ideal/Quotient/Operations.lean`](https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Ideal/Quotient/Operations.lean)
