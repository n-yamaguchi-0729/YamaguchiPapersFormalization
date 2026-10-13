/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.QuadraticCover
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.QuadraticConnected
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.QuadraticScheme
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.EtaleFundamentalGroups.GaloisCovers.DoubleCoverQuotient
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Nyll.SchemeTheory.Normalization.Normal
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Proposition 2.5: the quadratic quotient construction

The determinant-obstruction declaration is
`exists_surjective_cyclicTwo_of_four_dvd_pairDeterminant`.

The connected quadratic cover constructed from an odd numerator and a
nonzero denominator divisible by four gives a continuous quotient of order
two of the fundamental group of `Spec ℤ[t, 1/(v*t-u)]`, at every geometric
point. The degree condition is obtained from the actual free coordinate
algebra, via the rank of the affine scheme morphism.

This supplies the affine quotient construction in Proposition 2.5 of Ryoji
Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The actual standard-chart comparison transports this quotient to every open
subscheme of the projective complement of `T₁ = 0` and `v*T₀-u*T₁ = 0`.
The explicit integral change of coordinates also gives the quotient for any
two primitive equations with nonzero determinant divisible by four. The shared
finite-boundary endpoint restricts this quotient to the original finite complement.
`Geometry.DyadicNormalCrossingsQuotient` supplies the integral strict-normal-crossing
obstruction; comparison with normal crossings after p-adic base change is separate.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The explicit dyadic affine complement has a continuous cyclic quotient
of order two. The finite etale cover and its degree are constructed from the
arithmetic hypotheses, rather than supplied as inputs. -/
theorem exists_surjective_cyclicTwo_twoSectionCoordinateRing
    (u v : ℤ) (hu : Odd u) (hv : (4 : ℤ) ∣ v) (hv0 : v ≠ 0)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ Spec (.of (TwoSectionCoordinateRing u v))) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  obtain ⟨ε, _, hcover⟩ := exists_connected_finite_etale_quadratic_cover u v hu hv hv0
  let R : Type := TwoSectionCoordinateRing u v
  let B : Type := TwoSectionQuadraticAlgebra u v ε
  let π : Spec (.of B) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  obtain ⟨_, hconnected, hfinite, hetale, _, hfree, hdegree⟩ := hcover
  have : IsDomain R := Localization.Away.isDomain (boundaryPolynomial_ne_zero u v hv0)
  have : ConnectedSpace (Spec (.of R)) := inferInstance
  have : IsFiniteEtale π := { toIsFinite := hfinite, toEtale := hetale }
  have : Module.Free R B := hfree
  have : Module.Finite R B := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R B))).mp hfinite)
  let Y : FiniteEtale (Spec (.of R)) := FiniteEtale.mk π
  have : ConnectedSpace Y.left := hconnected
  apply FiniteEtale.exists_surjective_cyclicTwo_of_connected_doubleCover ξ Y
  change π.finrank (ξ (IsLocalRing.closedPoint Ω)) = 2
  exact (Scheme.Hom.finrank_SpecMap_algebraMap R B (ξ (IsLocalRing.closedPoint Ω))).trans
    ((congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := B))
      (ξ (IsLocalRing.closedPoint Ω))).trans hdegree)

/-- Removing further closed subsets preserves the constructed quotient of
order two. The source is any open subscheme of the actual affine complement;
its geometric point supplies nonemptiness. This is the restriction step
needed when the original divisor has additional components. -/
theorem exists_surjective_cyclicTwo_of_openImmersion_twoSectionCoordinateRing
    (u v : ℤ) (hu : Odd u) (hv : (4 : ℤ) ∣ v) (hv0 : v ≠ 0)
    {U : Scheme.{0}} (j : U ⟶ Spec (.of (TwoSectionCoordinateRing u v)))
    [IsOpenImmersion j] {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ U) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  have : IsDomain (TwoSectionCoordinateRing u v) :=
    Localization.Away.isDomain (boundaryPolynomial_ne_zero u v hv0)
  have : Nonempty U := ⟨ξ (IsLocalRing.closedPoint Ω)⟩
  obtain ⟨φ, hφ⟩ := exists_surjective_cyclicTwo_twoSectionCoordinateRing
    u v hu hv hv0 (ξ ≫ j)
  exact ⟨φ.comp (FiniteEtale.fundamentalGroupHom j ξ),
    hφ.comp (FiniteEtale.fundamentalGroupHom_surjective_of_isOpenImmersion j ξ)⟩

/-- Every open contained in the two-section projective complement has a
continuous quotient of order two. The map into the affine localization is
constructed from the actual open inclusion and standard-chart isomorphism;
no comparison map or quotient is supplied as an assumption. -/
theorem exists_surjective_cyclicTwo_of_le_twoSectionComplement
    (u v : ℤ) (hu : Odd u) (hv : (4 : ℤ) ∣ v) (hv0 : v ≠ 0)
    (U : (ProjectiveLine ℤ).Opens) (hU : U ≤ twoSectionComplement u v)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U.toScheme) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  let j : U.toScheme ⟶ Spec (.of (TwoSectionCoordinateRing u v)) :=
    (ProjectiveLine ℤ).homOfLE hU ≫ (twoSectionComplementIso u v).hom
  have : IsOpenImmersion j := inferInstance
  exact exists_surjective_cyclicTwo_of_openImmersion_twoSectionCoordinateRing
    u v hu hv hv0 j ξ

/-- Two primitive integral equations with nonzero determinant divisible by
four give a continuous cyclic quotient of order two on every open inside
their common complement. The odd normalized numerator, coordinate change,
and quadratic cover are all constructed from the original primitive pairs.

This is the determinant-obstruction case of Proposition 2.5. Comparing this
condition with failure of normal crossings is a separate geometric step. -/
theorem exists_surjective_cyclicTwo_of_four_dvd_pairDeterminant
    (u v u' v' : ℤ) (huv : IsCoprime u v) (huv' : IsCoprime u' v')
    (hfour : (4 : ℤ) ∣ coordinateDeterminant u v u' v')
    (hne : coordinateDeterminant u v u' v' ≠ 0)
    (U : (ProjectiveLine ℤ).Opens) (hU : U ≤ integralPairComplement u v u' v')
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U.toScheme) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  obtain ⟨a, b, hab⟩ := huv
  have hprimitive := isCoprime_normalizedCoordinates u v a b u' v' hab huv'
  have hodd : Odd (-(a * u' + b * v')) := by
    apply Int.not_even_iff_odd.mp
    intro heven
    have htwo : (2 : ℤ) ∣ coordinateDeterminant u v u' v' :=
      dvd_trans (by norm_num : (2 : ℤ) ∣ 4) hfour
    have hunit : IsUnit (2 : ℤ) :=
      hprimitive.isUnit_of_dvd' (even_iff_two_dvd.mp heven) htwo
    norm_num [Int.isUnit_iff] at hunit
  let j : U.toScheme ⟶ Spec (.of (TwoSectionCoordinateRing
      (-(a * u' + b * v')) (coordinateDeterminant u v u' v'))) :=
    (ProjectiveLine ℤ).homOfLE hU ≫ (integralPairComplementIso u v a b u' v' hab).hom
  have : IsOpenImmersion j := inferInstance
  exact exists_surjective_cyclicTwo_of_openImmersion_twoSectionCoordinateRing
    (-(a * u' + b * v')) (coordinateDeterminant u v u' v') hodd hfour hne j ξ

/-- A pair in the original finite boundary whose determinant is divisible by four
supplies a quadratic quotient on its actual common complement. This shared
restriction step is used both by the normal-crossing obstruction and the
large-boundary argument. -/
theorem exists_surjective_cyclicTwo_of_four_dvd_delta_in_boundary
    (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (a b : Projectivization ℚ (ℚ × ℚ)) (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hfour : (4 : ℤ) ∣ rationalPointDelta a b)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶
      (A.inf fun c => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (rationalPointNumerator c)
          (rationalPointDenominator c))).toScheme) :
    ∃ φ : π₁ᵉᵗ(ξ) →ₜ* Multiplicative (ZMod 2), Function.Surjective φ := by
  let O : Projectivization ℚ (ℚ × ℚ) → (ProjectiveLine ℤ).Opens := fun c =>
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      (linearSectionEquation (rationalPointNumerator c) (rationalPointDenominator c))
  have hU : A.inf O ≤ integralPairComplement
      (rationalPointNumerator a) (rationalPointDenominator a)
      (rationalPointNumerator b) (rationalPointDenominator b) :=
    le_inf (Finset.inf_le ha) (Finset.inf_le hb)
  exact exists_surjective_cyclicTwo_of_four_dvd_pairDeterminant
    (rationalPointNumerator a) (rationalPointDenominator a)
    (rationalPointNumerator b) (rationalPointDenominator b)
    (rationalPointCoordinates_isCoprime a) (rationalPointCoordinates_isCoprime b)
    ((rationalPointDelta_dvd_iff 4 a b).mp hfour)
    (rationalPoint_coordinateDeterminant_ne_zero a b hab) (A.inf O) hU ξ

end ShimizuYamaguchi26BranchedCoverings
