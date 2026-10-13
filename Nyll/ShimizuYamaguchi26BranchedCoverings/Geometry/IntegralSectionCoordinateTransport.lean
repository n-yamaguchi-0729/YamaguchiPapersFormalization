/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionIdeal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Set.Image
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Closure
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Sets.Closeds

/-!
# Transporting actual section ideals by the integral coordinate change

Pullback by the inverse of a scheme isomorphism agrees with pushforward
by the isomorphism. Applied to reduced vanishing ideal sheaves, this
identifies pullback with the vanishing ideal of the inverse image.

The explicit integral coordinate change therefore sends the actual kernel
ideal of a second primitive section to that of the section with coordinates
`(-(a*u' + b*v'), u*v' - v*u')`. The first section becomes the actual
section at infinity. The only auxiliary data are Bezout coefficients for
these primitive pairs, supplied by `isCoprime_normalizedCoordinates`.
No comparison of section ideals is assumed.

These identities supply the coordinate transport in Lemma 2.3 of Ryoji
Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem comap_inv_eq_map_hom {X Y : Scheme} (e : X ≅ Y)
    (I : X.IdealSheafData) : I.comap e.inv = I.map e.hom := by
  apply le_antisymm
  · apply Scheme.IdealSheafData.le_map_iff_comap_le.mpr
    simpa only [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
      Scheme.IdealSheafData.comap_id] using (le_refl I)
  · have h : ((I.map e.hom).comap e.hom).comap e.inv ≤ I.comap e.inv :=
      Scheme.IdealSheafData.comap_mono e.inv
        (Scheme.IdealSheafData.comap_map_le I e.hom)
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id] at h
    exact h

private theorem comap_inv_vanishingIdeal {X Y : Scheme} (e : X ≅ Y)
    (Z : TopologicalSpace.Closeds X) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap e.inv =
      Scheme.IdealSheafData.vanishingIdeal (Z.preimage e.inv.continuous) := by
  rw [comap_inv_eq_map_hom, Scheme.IdealSheafData.map_vanishingIdeal]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply SetLike.coe_injective
  change closure (e.hom '' (Z : Set X)) = e.inv ⁻¹' (Z : Set X)
  have hImage : e.hom '' (Z : Set X) = e.inv ⁻¹' (Z : Set X) :=
    (Scheme.homeoOfIso e).image_eq_preimage_symm _
  rw [hImage, (Z.isClosed.preimage e.inv.continuous).closure_eq]

/-- The actual ideal of the second section transforms to the ideal of its
explicit normalized primitive coordinates. The supplied Bezout identity
can be obtained from `isCoprime_normalizedCoordinates`. -/
theorem integralSection_ker_comap_coordinateChange_inv
    (u v a b u' v' c d c' d' : ℤ)
    (hab : a * u + b * v = 1) (hcd : c * u' + d * v' = 1)
    (hcd' : c' * (-(a * u' + b * v')) +
      d' * coordinateDeterminant u v u' v' = 1) :
    (integralSection u' v' c d hcd).ker.comap
        (integralCoordinateChange u v a b hab).inv =
      (integralSection (-(a * u' + b * v'))
        (coordinateDeterminant u v u' v') c' d' hcd').ker := by
  rw [integralSection_ker_eq_vanishingIdeal,
    integralSection_ker_eq_vanishingIdeal, comap_inv_vanishingIdeal]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply SetLike.coe_injective
  change (integralCoordinateChange u v a b hab).inv ⁻¹'
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation u' v'} =
    ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      {linearSectionEquation (-(a * u' + b * v')) (coordinateDeterminant u v u' v')}
  have hopen : (integralCoordinateChange u v a b hab).inv ⁻¹'
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation u' v') : Set (ProjectiveLine ℤ))ᶜ =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (-(a * u' + b * v'))
          (coordinateDeterminant u v u' v')) : Set (ProjectiveLine ℤ))ᶜ :=
    congrArg (fun U : (ProjectiveLine ℤ).Opens => (U : Set (ProjectiveLine ℤ))ᶜ)
      (integralCoordinateChange_inv_preimage_linearSection u v a b u' v' hab)
  have hsource :
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation u' v') : Set (ProjectiveLine ℤ))ᶜ =
      (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation u' v'} : Set (ProjectiveLine ℤ)) :=
    compl_eq_comm.mp (ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (linearSectionEquation u' v')).symm
  have htarget :
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (-(a * u' + b * v'))
          (coordinateDeterminant u v u' v')) : Set (ProjectiveLine ℤ))ᶜ =
      (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation (-(a * u' + b * v'))
          (coordinateDeterminant u v u' v')} : Set (ProjectiveLine ℤ)) :=
    compl_eq_comm.mp (ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      (linearSectionEquation (-(a * u' + b * v'))
        (coordinateDeterminant u v u' v'))).symm
  exact (congrArg (fun Z : Set (ProjectiveLine ℤ) =>
    (integralCoordinateChange u v a b hab).inv ⁻¹' Z) hsource.symm).trans
      (hopen.trans htarget)

/-- Pulling back the first section's actual ideal gives the actual section
at infinity, including its scheme structure. -/
theorem integralSection_ker_comap_coordinateChange_inv_self
    (u v a b : ℤ) (hab : a * u + b * v = 1) :
    (integralSection u v a b hab).ker.comap
        (integralCoordinateChange u v a b hab).inv =
      (integralSection 1 0 1 0 (by decide)).ker := by
  rw [integralSection_ker_eq_vanishingIdeal,
    integralSection_ker_eq_vanishingIdeal, comap_inv_vanishingIdeal]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply SetLike.coe_injective
  change (integralCoordinateChange u v a b hab).inv ⁻¹'
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation u v} =
    ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      {linearSectionEquation (1 : ℤ) 0}
  have hinfinity : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      (linearSectionEquation (1 : ℤ) 0) = infinityComplement ℤ := by
    ext x
    change (linearSectionEquation (1 : ℤ) 0 ∉ x.asHomogeneousIdeal.toIdeal) ↔
      MvPolynomial.X (1 : Fin 2) ∉ x.asHomogeneousIdeal.toIdeal
    simp only [linearSectionEquation, map_zero, map_one, zero_mul, one_mul,
      zero_sub, x.asHomogeneousIdeal.toIdeal.neg_mem_iff]
  have hopen : (integralCoordinateChange u v a b hab).inv ⁻¹'
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation u v) : Set (ProjectiveLine ℤ))ᶜ =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (1 : ℤ) 0) : Set (ProjectiveLine ℤ))ᶜ :=
    congrArg (fun U : (ProjectiveLine ℤ).Opens => (U : Set (ProjectiveLine ℤ))ᶜ)
      ((integralCoordinateChange_inv_preimage_firstSection u v a b hab).trans
        hinfinity.symm)
  have hsource :
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation u v) : Set (ProjectiveLine ℤ))ᶜ =
      (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation u v} : Set (ProjectiveLine ℤ)) :=
    compl_eq_comm.mp (ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (linearSectionEquation u v)).symm
  have htarget :
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (1 : ℤ) 0) : Set (ProjectiveLine ℤ))ᶜ =
      (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        {linearSectionEquation (1 : ℤ) 0} : Set (ProjectiveLine ℤ)) :=
    compl_eq_comm.mp (ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      (linearSectionEquation (1 : ℤ) 0)).symm
  exact (congrArg (fun Z : Set (ProjectiveLine ℤ) =>
    (integralCoordinateChange u v a b hab).inv ⁻¹' Z) hsource.symm).trans
      (hopen.trans htarget)

/-- Pullback of the actual pair product by the coordinate change normalizing
its second section. This identity is shared by both directions of the
normal-crossings criterion. -/
theorem integralSectionPair_ker_comap_coordinateChange_inv
    (u v c d u' v' c' d' A B : ℤ)
    (hcd : c * u + d * v = 1) (hcd' : c' * u' + d' * v' = 1)
    (hAB : A * (-(c' * u + d' * v)) +
      B * coordinateDeterminant u' v' u v = 1) :
    ((integralSection u v c d hcd).ker *
      (integralSection u' v' c' d' hcd').ker).comap
        (integralCoordinateChange u' v' c' d' hcd').inv =
      (integralSection 1 0 1 0 (by decide)).ker *
        (integralSection (-(c' * u + d' * v))
          (coordinateDeterminant u' v' u v) A B hAB).ker := by
  rw [Scheme.IdealSheafData.comap_mul,
    integralSection_ker_comap_coordinateChange_inv
      u' v' c' d' u v c d A B hcd' hcd hAB,
    integralSection_ker_comap_coordinateChange_inv_self u' v' c' d' hcd',
    mul_comm]

end ShimizuYamaguchi26BranchedCoverings
