/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.DyadicCollision
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.QuadraticCover
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.QuadraticConnected
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.Topology.Connected.Basic

/-!
# The connected quadratic cover of the affine localization

Taking spectra of the explicit quadratic algebra gives a finite etale,
surjective morphism with integral, connected source. Its coordinate algebra
is free of rank two. The parameter restrictions are precisely the arithmetic
conditions reached in Proposition 2.5 after moving one section to infinity.

The comparison of this affine localization with the complement of two
sections in the projective line, and the resulting quotient of the etale
fundamental group, remain separate geometric steps.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
Proposition 2.5.
-/

noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

/-- The concrete dyadic quadratic cover is connected, finite etale, surjective,
and free of rank two over the stated affine localization. -/
theorem exists_connected_finite_etale_quadratic_cover (u v : ℤ)
    (hu : Odd u) (hv : (4 : ℤ) ∣ v) (hv0 : v ≠ 0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      let R : Type := TwoSectionCoordinateRing u v
      let B : Type := TwoSectionQuadraticAlgebra u v ε
      let π : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) :=
        Spec.map (CommRingCat.ofHom (algebraMap R B))
      IsIntegral (Spec (CommRingCat.of B)) ∧ ConnectedSpace (Spec (CommRingCat.of B)) ∧
        IsFinite π ∧ Etale π ∧ Surjective π ∧ Module.Free R B ∧ Module.finrank R B = 2 := by
  obtain ⟨ε, hε, hεu⟩ := exists_sign_four_dvd_one_add u hu
  refine ⟨ε, hε, ?_⟩
  let R : Type := TwoSectionCoordinateRing u v
  let B : Type := TwoSectionQuadraticAlgebra u v ε
  let c : ℤ[X] := quadraticConstantTerm u v ε
  let cR : R := algebraMap ℤ[X] R c
  let : IsDomain R := Localization.Away.isDomain (boundaryPolynomial_ne_zero u v hv0)
  let : IsDomain B := twoSectionQuadraticAlgebra_isDomain u v ε hε hεu hv hv0
  let : Module.Finite R B := (quadraticPolynomial_monic cR).finite_adjoinRoot
  let : Module.Free R B := (quadraticPolynomial_monic cR).free_adjoinRoot
  have hunit : IsUnit (1 - 4 * cR) :=
    quadraticConstantTerm_discriminant_isUnit u v ε hε hεu hv
  have hetale : Algebra.Etale R B := quadraticPolynomial_etale cR hunit
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, inferInstance,
    quadraticPolynomial_finrank cR⟩
  · exact (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap R B))).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hetale)
  · exact ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := B)⟩

end ShimizuYamaguchi26BranchedCoverings
