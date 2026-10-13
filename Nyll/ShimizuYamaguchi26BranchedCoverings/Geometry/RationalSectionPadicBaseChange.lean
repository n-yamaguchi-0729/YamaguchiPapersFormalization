/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.CartierEtale
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionFamily
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RingHom.Flat

/-!
# Rational-section divisors over the p-adic integers

The actual finite rational-section divisor over the integers pulls back to an
effective Cartier divisor on the projective line over `ℤ_[p]`. Here `ℤ_[p]`
is Mathlib's ring of p-adic integers, not the localization of `ℤ` at `(p)`.

The coefficient morphism is affine and flat: it is a base change of
`Spec ℤ_[p] ⟶ Spec ℤ`, and the characteristic-zero domain `ℤ_[p]` is a
torsion-free, hence flat, integer module. The projective-space pullback theorem
is reused from `SchemeTheory.ProjectiveSpace.BaseChange`, with its retained
Anthropic FLT provenance. This file does not assert preservation of reducedness
under arbitrary flat pullback or the normal-crossing equivalence of Lemma 2.3.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem padicProjectiveMap_properties (p : ℕ) [Fact p.Prime] :
    Flat (ProjSpace.map ℤ ℤ_[p] 1) ∧ IsAffineHom (ProjSpace.map ℤ ℤ_[p] 1) := by
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℤ_[p]))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr
      (inferInstanceAs (Module.Flat ℤ ℤ_[p])))
  have haffine : IsAffineHom
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℤ_[p]))) := inferInstance
  have hbase := (ProjSpace.isPullback_map ℤ ℤ_[p] 1).flip
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) hbase hflat,
    MorphismProperty.of_isPullback (P := @IsAffineHom) hbase haffine⟩

/-- The actual finite rational-section divisor after extension of coefficients
from the integers to the p-adic integers. The affine flatness needed for Cartier
pullback is proved from the coefficient map. -/
def rationalSectionPadicDivisor (p : ℕ) [Fact p.Prime]
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    Scheme.EffectiveCartierDivisor (ProjectiveLine ℤ_[p]) := by
  have hmap := padicProjectiveMap_properties p
  have : Flat (ProjSpace.map ℤ ℤ_[p] 1) := hmap.1
  have : IsAffineHom (ProjSpace.map ℤ ℤ_[p] 1) := hmap.2
  exact (rationalSectionDivisor A).comap (ProjSpace.map ℤ ℤ_[p] 1)

/-- The constructed p-adic divisor has exactly the pullback of the actual
finite product of the rational-section kernel ideals. -/
theorem rationalSectionPadicDivisor_ideal (p : ℕ) [Fact p.Prime]
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (rationalSectionPadicDivisor p A : (ProjectiveLine ℤ_[p]).IdealSheafData) =
      (∏ a ∈ A, (rationalSection a).ker).comap (ProjSpace.map ℤ ℤ_[p] 1) :=
  rfl

/-- The support of the p-adic divisor is the inverse image of the integral
finite rational-section support under the actual projective coefficient map. -/
theorem rationalSectionPadicDivisor_support (p : ℕ) [Fact p.Prime]
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (rationalSectionPadicDivisor p A).support =
      (rationalSectionDivisor A).support.preimage (ProjSpace.map ℤ ℤ_[p] 1).continuous := by
  change ((rationalSectionPadicDivisor p A :
    (ProjectiveLine ℤ_[p]).IdealSheafData)).support = _
  rw [rationalSectionPadicDivisor_ideal]
  exact Scheme.IdealSheafData.support_comap _ _

end ShimizuYamaguchi26BranchedCoverings
