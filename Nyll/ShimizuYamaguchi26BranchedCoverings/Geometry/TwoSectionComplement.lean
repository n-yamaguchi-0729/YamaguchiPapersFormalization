/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.QuadraticCover
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The complement of two linear equations in the integral projective line

The homogeneous equation `v * T₀ - u * T₁` restricts on the chart `T₁ ≠ 0`
to `v * t - u`. Consequently the complement of its zero set and the section
at infinity is isomorphic, as a scheme, to `Spec ℤ[t, 1 / (v * t - u)]`.
The comparison is constructed from open immersions with the same image.

For primitive `(u,v)`, the first equation is the rational section considered
in Proposition 2.5 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The scheme comparison proved here applies without the primitivity assumption;
identifying the closed subscheme with the corresponding section is a separate
assertion. `IntegralCoordinateChange` extends this comparison to pairs of
equations with arbitrary primitive first coordinates.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous linear equation of the section with coordinates `(u,v)`. -/
def linearSectionEquation {R : Type u} [CommRing R] (u v : R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.C v * MvPolynomial.X 0 - MvPolynomial.C u * MvPolynomial.X 1

/-- The section equation is homogeneous of degree one. -/
theorem linearSectionEquation_mem_one {R : Type u} [CommRing R] (u v : R) :
    linearSectionEquation u v ∈ MvPolynomial.homogeneousSubmodule (Fin 2) R 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
    ((MvPolynomial.isHomogeneous_C_mul_X v (0 : Fin 2)).sub
      (MvPolynomial.isHomogeneous_C_mul_X u (1 : Fin 2)))

/-- Dividing the section equation by `T₁` gives its affine linear expression. -/
theorem linearSectionEquation_dehomogenize {R : Type u} [CommRing R] (u v : R) :
    Away.isLocalizationElem (ProjSpace.X_mem_one R 1 (1 : Fin 2))
      (linearSectionEquation_mem_one u v) =
        algebraMap R (StandardChartRing R) v * ProjSpace.ratio R 1 1 0 -
          algebraMap R (StandardChartRing R) u := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
    ProjSpace.val_algebraMap, ProjSpace.val_algebraMap]
  simp only [Away.isLocalizationElem, Away.val_mk, ProjSpace.ratio, pow_one]
  simp only [Localization.mk_eq_mk']
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp only [linearSectionEquation, map_sub, map_mul]
  rw [sub_mul, mul_assoc, IsLocalization.mk'_spec]

/-- The chart isomorphism sends `v*t-u` to the actual homogeneous localization element. -/
theorem standardChartEquiv_linearSectionEquation {R : Type u} [CommRing R] (u v : R) :
    standardChartEquiv R (Polynomial.C v * Polynomial.X - Polynomial.C u) =
      Away.isLocalizationElem (ProjSpace.X_mem_one R 1 (1 : Fin 2))
        (linearSectionEquation_mem_one u v) := by
  rw [map_sub, map_mul, standardChartEquiv_X, ← Polynomial.algebraMap_eq,
    (standardChartEquiv R).commutes v, (standardChartEquiv R).commutes u]
  exact (linearSectionEquation_dehomogenize u v).symm

/-- The nonvanishing open of the homogeneous section equation pulls back to `D(v*t-u)`. -/
theorem standardChartEmbedding_preimage_linearSection {R : Type u} [CommRing R] (u v : R) :
    standardChartEmbedding R ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (linearSectionEquation u v) =
      PrimeSpectrum.basicOpen (Polynomial.C v * Polynomial.X - Polynomial.C u) := by
  unfold standardChartEmbedding
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (ProjSpace.X_mem_one R 1 1) one_pos (linearSectionEquation_mem_one u v) one_pos]
  change Spec.map (CommRingCat.ofHom (standardChartEquiv R).symm.toRingHom) ⁻¹ᵁ
      PrimeSpectrum.basicOpen
        (Away.isLocalizationElem (ProjSpace.X_mem_one R 1 (1 : Fin 2))
          (linearSectionEquation_mem_one u v)) = _
  rw [SpecMap_preimage_basicOpen]
  apply congrArg PrimeSpectrum.basicOpen
  change (standardChartEquiv R).symm
    (Away.isLocalizationElem (ProjSpace.X_mem_one R 1 (1 : Fin 2))
      (linearSectionEquation_mem_one u v)) = _
  rw [← standardChartEquiv_linearSectionEquation u v, AlgEquiv.symm_apply_apply]

/-- The open complement of `T₁ = 0` and `v*T₀-u*T₁ = 0` in `ℙ¹_ℤ`. -/
def twoSectionComplement (u v : ℤ) : (ProjectiveLine ℤ).Opens :=
  infinityComplement ℤ ⊓
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (linearSectionEquation u v)

/-- The affine localization embeds into the projective line by its standard coordinate chart. -/
def twoSectionComplementEmbedding (u v : ℤ) :
    Spec (CommRingCat.of (TwoSectionCoordinateRing u v)) ⟶ ProjectiveLine ℤ :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ[X] (TwoSectionCoordinateRing u v))) ≫
    standardChartEmbedding ℤ

instance (u v : ℤ) : IsOpenImmersion (twoSectionComplementEmbedding u v) := by
  unfold twoSectionComplementEmbedding
  infer_instance

/-- The affine localization has exactly the required two-equation complement as its image. -/
theorem twoSectionComplementEmbedding_opensRange (u v : ℤ) :
    (twoSectionComplementEmbedding u v).opensRange = twoSectionComplement u v := by
  unfold twoSectionComplementEmbedding twoSectionComplement
  rw [Scheme.Hom.opensRange_comp,
    Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of ℤ[X]) (boundaryPolynomial u v)]
  change standardChartEmbedding ℤ ''ᵁ
      PrimeSpectrum.basicOpen (Polynomial.C v * Polynomial.X - Polynomial.C u) = _
  rw [← standardChartEmbedding_preimage_linearSection u v,
    Scheme.Hom.image_preimage_eq_opensRange_inf, standardChartEmbedding_opensRange]

/-- The actual projective complement is the spectrum of `ℤ[t, 1/(v*t-u)]`. -/
def twoSectionComplementIso (u v : ℤ) :
    (twoSectionComplement u v).toScheme ≅ Spec (CommRingCat.of (TwoSectionCoordinateRing u v)) :=
  IsOpenImmersion.isoOfRangeEq (twoSectionComplement u v).ι
    (twoSectionComplementEmbedding u v) (by
      rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange,
        twoSectionComplementEmbedding_opensRange])

/-- The affine comparison commutes with the maps to the projective line. -/
theorem twoSectionComplementIso_hom_comp_embedding (u v : ℤ) :
    (twoSectionComplementIso u v).hom ≫ twoSectionComplementEmbedding u v =
      (twoSectionComplement u v).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end ShimizuYamaguchi26BranchedCoverings
