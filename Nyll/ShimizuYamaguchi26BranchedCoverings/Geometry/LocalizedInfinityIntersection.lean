/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityIntersection
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# The localized intersection with infinity

For a local coefficient ring `R`, the infinity chart point over its closed
point has prime ideal `(maximalIdeal R, X)` in `R[X]`. Localizing at this
actual ideal and quotienting by the two section equations `(X, v-u*X)` gives
the same algebra as quotienting before localization. The reason is proved
concretely: `X` vanishes in the intersection, so every polynomial outside
the point ideal maps to its unit constant coefficient.

Over a DVR, the length over this localized chart ring is therefore the
additive valuation of `v`. This supplies the localization comparison in
the infinity-chart calculation of Lemma 2.3 of Ryoji Shimizu and
Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The projective chart/stalk identification and normalization as the integer
`p`-adic valuation are developed in `ProjectiveInfinityIntersection`. The
comparison with global section ideals and normal crossings is separate.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

universe u

variable {R : Type u} [CommRing R]

/-- In the intersection algebra, every polynomial equals its constant coefficient. -/
theorem infinityIntersection_polynomial_eq_constantCoeff (u v : R) (f : R[X]) :
    algebraMap R[X] (InfinityIntersectionAlgebra u v) f =
      algebraMap R (InfinityIntersectionAlgebra u v) (Polynomial.constantCoeff f) := by
  have hX : algebraMap R[X] (InfinityIntersectionAlgebra u v) Polynomial.X = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl rfl))
  calc
    _ = algebraMap R[X] (InfinityIntersectionAlgebra u v)
        (Polynomial.X * f.divX + Polynomial.C (f.coeff 0)) :=
      congrArg (algebraMap R[X] (InfinityIntersectionAlgebra u v))
        (Polynomial.X_mul_divX_add f).symm
    _ = algebraMap R[X] (InfinityIntersectionAlgebra u v)
        (Polynomial.C (f.coeff 0)) := by
      rw [map_add, map_mul, hX, zero_mul, zero_add]
    _ = algebraMap R (InfinityIntersectionAlgebra u v) (Polynomial.constantCoeff f) :=
      (IsScalarTower.algebraMap_apply R R[X] (InfinityIntersectionAlgebra u v) (f.coeff 0)).symm

section LocalRing

variable [IsLocalRing R]

/-- The infinity chart closed point above the closed point of the coefficient ring. -/
def infinityChartClosedPointIdeal (R : Type u) [CommRing R] [IsLocalRing R] : Ideal R[X] :=
  (IsLocalRing.maximalIdeal R).comap Polynomial.constantCoeff

/-- This concrete chart point is closed. -/
instance infinityChartClosedPointIdeal_isMaximal :
    (infinityChartClosedPointIdeal R).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective Polynomial.constantCoeff Polynomial.constantCoeff_surjective

/-- The evaluation description is exactly the coordinate ideal `(maximalIdeal R, X)`. -/
theorem infinityChartClosedPointIdeal_eq :
    infinityChartClosedPointIdeal R =
      (IsLocalRing.maximalIdeal R).map Polynomial.C ⊔ Ideal.span {Polynomial.X} := by
  have hcomp : Polynomial.constantCoeff.comp Polynomial.C = RingHom.id R := by
    ext r
    exact Polynomial.coeff_C_zero
  have h := Ideal.comap_map_of_surjective Polynomial.constantCoeff
    Polynomial.constantCoeff_surjective ((IsLocalRing.maximalIdeal R).map Polynomial.C)
  rw [Ideal.map_map, hcomp, Ideal.map_id] at h
  change (IsLocalRing.maximalIdeal R).comap Polynomial.constantCoeff = _
  rw [← Polynomial.ker_constantCoeff, RingHom.ker_eq_comap_bot]
  exact h

/-- The actual local ring of the polynomial chart at the infinity section point. -/
abbrev InfinityChartLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :=
  Localization.AtPrime (infinityChartClosedPointIdeal R)

/-- The two section equations in the localized chart ring. -/
abbrev LocalizedInfinityIntersectionAlgebra (u v : R) :=
  InfinityChartLocalRing R ⧸ (infinityIntersectionIdeal u v).map
    (algebraMap R[X] (InfinityChartLocalRing R))

private theorem infinityIntersection_denominators_are_units (u v : R) :
    Algebra.algebraMapSubmonoid (InfinityIntersectionAlgebra u v)
        (infinityChartClosedPointIdeal R).primeCompl ≤
      IsUnit.submonoid (InfinityIntersectionAlgebra u v) := by
  rintro z ⟨f, hf, rfl⟩
  change IsUnit (algebraMap R[X] (InfinityIntersectionAlgebra u v) f)
  rw [infinityIntersection_polynomial_eq_constantCoeff]
  have hf0 : Polynomial.constantCoeff f ∉ IsLocalRing.maximalIdeal R := hf
  exact (IsLocalRing.notMem_maximalIdeal.mp hf0).map
    (algebraMap R (InfinityIntersectionAlgebra u v))

/-- Localizing the actual intersection quotient does not change it.
Every inverted polynomial has a unit constant coefficient in the quotient. -/
def localizedInfinityIntersectionEquiv (u v : R) :
    LocalizedInfinityIntersectionAlgebra u v ≃ₐ[R[X]] InfinityIntersectionAlgebra u v := by
  let M : Submonoid (InfinityIntersectionAlgebra u v) :=
    Algebra.algebraMapSubmonoid (InfinityIntersectionAlgebra u v)
      (infinityChartClosedPointIdeal R).primeCompl
  have : IsLocalization M (InfinityIntersectionAlgebra u v) :=
    IsLocalization.of_le_isUnit (infinityIntersection_denominators_are_units u v)
  exact (IsLocalization.algEquiv M (LocalizedInfinityIntersectionAlgebra u v)
    (InfinityIntersectionAlgebra u v)).restrictScalars R[X]

/-- The scheme of the localized intersection is the spectrum of the denominator quotient. -/
def localizedInfinityIntersectionIso (u v : R) :
    Spec (CommRingCat.of (LocalizedInfinityIntersectionAlgebra u v)) ≅
      Spec (CommRingCat.of (R ⧸ Ideal.span {v})) :=
  (Scheme.Spec.mapIso
    (localizedInfinityIntersectionEquiv u v).toRingEquiv.toCommRingCatIso.op).symm ≪≫
      infinityIntersectionIso u v

/-- The chart polynomial ring already surjects onto the localized intersection. -/
theorem localizedInfinityIntersection_algebraMap_surjective (u v : R) :
    Function.Surjective (algebraMap R[X] (LocalizedInfinityIntersectionAlgebra u v)) := by
  intro q
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective ((localizedInfinityIntersectionEquiv u v) q)
  refine ⟨f, ?_⟩
  apply (localizedInfinityIntersectionEquiv u v).injective
  rw [(localizedInfinityIntersectionEquiv u v).commutes]
  exact hf

/-- The length over the actual localized chart equals the affine intersection length. -/
theorem localizedInfinityIntersection_length_eq (u v : R) :
    Module.length (InfinityChartLocalRing R) (LocalizedInfinityIntersectionAlgebra u v) =
      Module.length R[X] (InfinityIntersectionAlgebra u v) := by
  calc
    _ = Module.length (LocalizedInfinityIntersectionAlgebra u v)
        (LocalizedInfinityIntersectionAlgebra u v) :=
      Module.length_eq_of_surjective (S := InfinityChartLocalRing R)
        (R := LocalizedInfinityIntersectionAlgebra u v)
        (M := LocalizedInfinityIntersectionAlgebra u v) Ideal.Quotient.mk_surjective
    _ = Module.length R[X] (LocalizedInfinityIntersectionAlgebra u v) :=
      (Module.length_eq_of_surjective (S := R[X])
        (R := LocalizedInfinityIntersectionAlgebra u v)
        (M := LocalizedInfinityIntersectionAlgebra u v)
        (localizedInfinityIntersection_algebraMap_surjective u v)).symm
    _ = Module.length R[X] (InfinityIntersectionAlgebra u v) :=
      (localizedInfinityIntersectionEquiv u v).toLinearEquiv.length_eq

end LocalRing

/-- The localized infinity-chart intersection multiplicity over a DVR is the valuation of `v`. -/
theorem localizedInfinityIntersection_length [IsDomain R] [IsDiscreteValuationRing R] (u v : R) :
    Module.length (InfinityChartLocalRing R) (LocalizedInfinityIntersectionAlgebra u v) =
      IsDiscreteValuationRing.addVal R v := by
  rw [localizedInfinityIntersection_length_eq, infinityIntersection_length]

end ShimizuYamaguchi26BranchedCoverings
