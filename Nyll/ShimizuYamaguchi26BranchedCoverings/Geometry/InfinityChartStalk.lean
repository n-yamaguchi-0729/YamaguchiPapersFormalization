/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.LocalizedInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# The actual projective stalk at the infinity chart point

Swapping the homogeneous coordinates turns the standard affine chart into
the chart `T₀ ≠ 0`. At the prime `(maximalIdeal R, X)`, the open immersion
identifies the stalk of the projective line with the prime localization of
`R[X]`. Polynomial germs are constructed from the actual structure-sheaf
germ on `Spec R[X]` and the inverse chart stalk map. The stalk isomorphism
sends these germs to the usual localization map.

This identifies the ring in the infinity-chart intersection calculation
with an actual projective local ring, as needed for Lemma 2.3 of Ryoji
Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The affine chart at infinity, with coordinate `T₁ / T₀`. -/
def infinityChartEmbedding (R : Type u) [CommRing R] :
    Spec (CommRingCat.of R[X]) ⟶ ProjectiveLine R :=
  standardChartEmbedding R ≫ (projectiveCoordinateSwap R).hom

instance (R : Type u) [CommRing R] : IsOpenImmersion (infinityChartEmbedding R) := by
  unfold infinityChartEmbedding
  infer_instance

/-- The infinity chart is the actual open `T₀ ≠ 0` in the projective line. -/
theorem infinityChartEmbedding_opensRange (R : Type u) [CommRing R] :
    (infinityChartEmbedding R).opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (MvPolynomial.X (0 : Fin 2)) := by
  have hswap : (projectiveCoordinateSwap R).hom = (projectiveCoordinateSwap R).inv := rfl
  calc
    (infinityChartEmbedding R).opensRange =
        (projectiveCoordinateSwap R).hom ''ᵁ (standardChartEmbedding R).opensRange :=
      Scheme.Hom.opensRange_comp (standardChartEmbedding R) (projectiveCoordinateSwap R).hom
    _ = (projectiveCoordinateSwap R).hom ⁻¹ᵁ infinityComplement R := by
      rw [standardChartEmbedding_opensRange]
      simpa only [hswap] using
        (Scheme.Hom.inv_image (projectiveCoordinateSwap R) (infinityComplement R))
    _ = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (linearSectionEquation (0 : R) 1) :=
      integralCoordinateChange_preimage_infinity (0 : R) 1 0 1
        (by rw [zero_mul, one_mul, zero_add])
    _ = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (MvPolynomial.X (0 : Fin 2)) := by
      rw [linearSectionEquation, map_one, map_zero, one_mul, zero_mul, sub_zero]

/-- The original integral section equation restricts to `v-u*w` on the infinity chart. -/
theorem infinityChartEmbedding_preimage_linearSection (u v : ℤ) :
    infinityChartEmbedding ℤ ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
          (linearSectionEquation u v) =
      PrimeSpectrum.basicOpen (Polynomial.C v - Polynomial.C u * Polynomial.X) := by
  have hswap : (projectiveCoordinateSwap ℤ).hom = (projectiveCoordinateSwap ℤ).inv := rfl
  rw [infinityChartEmbedding, Scheme.Hom.comp_preimage, hswap,
    projectiveCoordinateSwap, integralCoordinateChange_inv_preimage_linearSection,
    standardChartEmbedding_preimage_linearSection]
  apply congrArg PrimeSpectrum.basicOpen
  simp only [coordinateDeterminant, zero_mul, one_mul, zero_add, zero_sub, map_neg]
  ring

/-- Vanishing of the homogeneous section equation is vanishing of its actual chart polynomial. -/
theorem infinityChartEmbedding_linearSection_mem_iff
    (u v : ℤ) (q : PrimeSpectrum ℤ[X]) :
    linearSectionEquation u v ∈ (infinityChartEmbedding ℤ q).asHomogeneousIdeal ↔
      Polynomial.C v - Polynomial.C u * Polynomial.X ∈ q.asIdeal := by
  classical
  apply not_iff_not.mp
  change q ∈ infinityChartEmbedding ℤ ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation u v) ↔
    q ∈ PrimeSpectrum.basicOpen (Polynomial.C v - Polynomial.C u * Polynomial.X)
  exact Iff.of_eq (congrArg
    (fun U : (Spec (CommRingCat.of ℤ[X])).Opens => q ∈ U)
    (infinityChartEmbedding_preimage_linearSection u v))

/-- The prime of the infinity chart above the closed point of the local base. -/
def infinityChartClosedPoint (R : Type u) [CommRing R] [IsLocalRing R] :
    PrimeSpectrum R[X] :=
  ⟨infinityChartClosedPointIdeal R, inferInstance⟩

/-- The corresponding actual point of the projective line. -/
def projectiveInfinityPoint (R : Type u) [CommRing R] [IsLocalRing R] :
    ProjectiveLine R :=
  infinityChartEmbedding R (infinityChartClosedPoint R)

/-- At any prime of the infinity chart, the actual projective stalk is the
localization of the polynomial ring at that prime. -/
def infinityChartStalkEquiv (R : Type u) [CommRing R]
    (q : Spec (CommRingCat.of R[X])) :
    let : q.asIdeal.IsPrime := q.isPrime
    (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) ≃+*
      Localization.AtPrime q.asIdeal := by
  intro hprime
  let e : (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) ≅
      (Spec (CommRingCat.of R[X])).presheaf.stalk q :=
    asIso ((infinityChartEmbedding R).stalkMap q)
  exact (e ≪≫ Spec.stalkIso (CommRingCat.of R[X]) q).commRingCatIsoToRingEquiv

/-- A polynomial gives a germ at any point of the infinity chart, using the
actual structure-sheaf germ and the inverse stalk map of the open immersion. -/
def infinityChartGermAt (R : Type u) [CommRing R]
    (q : Spec (CommRingCat.of R[X])) :
    R[X] →+* (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) := by
  let e : (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) ≅
      (Spec (CommRingCat.of R[X])).presheaf.stalk q :=
    asIso ((infinityChartEmbedding R).stalkMap q)
  exact ((Scheme.ΓSpecIso (CommRingCat.of R[X])).inv ≫
    (Spec (CommRingCat.of R[X])).presheaf.germ ⊤ q trivial ≫ e.inv).hom

/-- The actual chart germ becomes the localization map at the chosen prime. -/
theorem infinityChartStalkEquiv_germAt (R : Type u) [CommRing R]
    (q : Spec (CommRingCat.of R[X])) (f : R[X]) :
    let : q.asIdeal.IsPrime := q.isPrime
    infinityChartStalkEquiv R q (infinityChartGermAt R q f) =
      algebraMap R[X] (Localization.AtPrime q.asIdeal) f := by
  intro hprime
  let e : (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) ≅
      (Spec (CommRingCat.of R[X])).presheaf.stalk q :=
    asIso ((infinityChartEmbedding R).stalkMap q)
  let g : CommRingCat.of R[X] ⟶ (Spec (CommRingCat.of R[X])).presheaf.stalk q :=
    (Scheme.ΓSpecIso (CommRingCat.of R[X])).inv ≫
      (Spec (CommRingCat.of R[X])).presheaf.germ ⊤ q trivial
  have hcancel : e.hom (e.inv (g f)) = g f := CommRingCat.hom_inv_apply e (g f)
  have hspec : (Spec.stalkIso (CommRingCat.of R[X]) q).hom (g f) =
      algebraMap R[X] (Localization.AtPrime q.asIdeal) f := by
    have hbase : CommRingCat.ofHom (algebraMap R[X] (Localization.AtPrime q.asIdeal)) ≫
        (Spec.stalkIso (CommRingCat.of R[X]) q).inv = g :=
      Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R[X]) q
    have hmap : g ≫ (Spec.stalkIso (CommRingCat.of R[X]) q).hom =
        CommRingCat.ofHom (algebraMap R[X] (Localization.AtPrime q.asIdeal)) := by
      rw [← hbase, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom] using
      (ConcreteCategory.congr_hom hmap f)
  exact (congrArg (Spec.stalkIso (CommRingCat.of R[X]) q).hom hcancel).trans hspec

/-- The projective stalk is the localization at the concrete infinity chart prime. -/
def projectiveInfinityStalkEquiv (R : Type u) [CommRing R] [IsLocalRing R] :
    (ProjectiveLine R).presheaf.stalk (projectiveInfinityPoint R) ≃+*
      InfinityChartLocalRing R :=
  infinityChartStalkEquiv R (infinityChartClosedPoint R)

/-- A polynomial defines a projective local germ at the point above the
closed point of the local base through the actual affine structure sheaf. -/
def infinityChartGerm (R : Type u) [CommRing R] [IsLocalRing R] :
    R[X] →+* (ProjectiveLine R).presheaf.stalk (projectiveInfinityPoint R) :=
  infinityChartGermAt R (infinityChartClosedPoint R)

/-- The actual chart germ becomes the standard polynomial localization map. -/
theorem projectiveInfinityStalkEquiv_germ (R : Type u) [CommRing R] [IsLocalRing R]
    (f : R[X]) :
    projectiveInfinityStalkEquiv R (infinityChartGerm R f) =
      algebraMap R[X] (InfinityChartLocalRing R) f :=
  infinityChartStalkEquiv_germAt R (infinityChartClosedPoint R) f

end ShimizuYamaguchi26BranchedCoverings
