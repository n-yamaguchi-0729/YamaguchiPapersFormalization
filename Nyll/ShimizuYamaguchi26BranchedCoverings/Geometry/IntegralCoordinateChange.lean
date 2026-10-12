/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.QuadraticCover
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Integral changes of coordinates on the projective line

Bézout coefficients `a*u+b*v = 1` give a homogeneous substitution with matrix
`[[a,b],[v,-u]]`. Its inverse has matrix `[[u,b],[v,-a]]`. The two substitutions
preserve degrees, and their compositions are the identity. Applying `Proj.map`
therefore constructs an actual scheme automorphism of the integral projective
line, rather than only an action on field-valued projective points.

The inverse image of the infinity chart is `D₊(v*T₀-u*T₁)`. Restriction then
identifies the complement of this equation with the affine line for every
primitive pair `(u,v)`. The transformed second equation has its determinant as
the coefficient of `T₀`. Restriction identifies the common complement of the
two equations with the spectrum of the corresponding affine localization,
as needed in Proposition 2.5 of Ryoji Shimizu and
Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).

The identification of the closed equation with the image of a section and the
local intersection-multiplicity comparison are separate assertions.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- The degree-preserving substitution `(T₀,T₁) ↦ (a*T₀+b*T₁,v*T₀-u*T₁)`. -/
def bezoutCoordinateSubstitution (u v a b : R) :
    MvPolynomial.homogeneousSubmodule (Fin 2) R →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin 2) R where
  __ := MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
    else linearSectionEquation u v)
  map_mem {i} {p} hp := by
    apply (MvPolynomial.mem_homogeneousSubmodule i _).mpr
    have h := (MvPolynomial.mem_homogeneousSubmodule i p).mp hp
    have hcoordinates : ∀ j : Fin 2,
        (if j = 0 then MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
          else linearSectionEquation u v).IsHomogeneous 1 := by
      intro j
      by_cases hj : j = 0
      · rw [ite_eq_left hj]
        exact (MvPolynomial.isHomogeneous_C_mul_X a (0 : Fin 2)).add
          (MvPolynomial.isHomogeneous_C_mul_X b (1 : Fin 2))
      · rw [ite_eq_right hj]
        exact (MvPolynomial.mem_homogeneousSubmodule 1 _).mp
          (linearSectionEquation_mem_one u v)
    simpa only [MvPolynomial.coe_eval₂Hom, one_mul] using
      h.eval₂ MvPolynomial.C _ (MvPolynomial.isHomogeneous_C _) hcoordinates

/-- The substitution fixes the coefficient ring. -/
theorem bezoutCoordinateSubstitution_C (u v a b r : R) :
    bezoutCoordinateSubstitution u v a b (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- The first coordinate of the homogeneous substitution. -/
theorem bezoutCoordinateSubstitution_X_zero (u v a b : R) :
    bezoutCoordinateSubstitution u v a b (MvPolynomial.X 0) =
      MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 := by
  change MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.X (0 : Fin 2)) = _
  rw [MvPolynomial.eval₂Hom_X', ite_eq_left rfl]

/-- The second coordinate is the primitive section equation. -/
theorem bezoutCoordinateSubstitution_X_one (u v a b : R) :
    bezoutCoordinateSubstitution u v a b (MvPolynomial.X 1) = linearSectionEquation u v := by
  change MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.X (1 : Fin 2)) = _
  rw [MvPolynomial.eval₂Hom_X', ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]

/-- Bézout's identity makes the two explicit homogeneous substitutions inverse. -/
theorem bezoutCoordinateSubstitution_comp (u v a b : R) (hab : a * u + b * v = 1) :
    (bezoutCoordinateSubstitution u v a b).comp (bezoutCoordinateSubstitution a v u b) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin 2) R) := by
  apply GradedRingHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro r
    change bezoutCoordinateSubstitution u v a b
        (bezoutCoordinateSubstitution a v u b (MvPolynomial.C r)) = MvPolynomial.C r
    rw [bezoutCoordinateSubstitution_C, bezoutCoordinateSubstitution_C]
  · intro j
    change bezoutCoordinateSubstitution u v a b
        (bezoutCoordinateSubstitution a v u b (MvPolynomial.X j)) = MvPolynomial.X j
    fin_cases j
    · change bezoutCoordinateSubstitution u v a b
        (bezoutCoordinateSubstitution a v u b (MvPolynomial.X (0 : Fin 2))) =
          MvPolynomial.X (0 : Fin 2)
      rw [bezoutCoordinateSubstitution_X_zero, map_add, map_mul, map_mul,
        bezoutCoordinateSubstitution_C, bezoutCoordinateSubstitution_C,
        bezoutCoordinateSubstitution_X_zero, bezoutCoordinateSubstitution_X_one]
      calc
        (MvPolynomial.C u *
            (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1) +
          MvPolynomial.C b * linearSectionEquation u v : MvPolynomial (Fin 2) R) =
            MvPolynomial.C (a * u + b * v) * MvPolynomial.X 0 := by
          simp only [linearSectionEquation, map_add, map_mul]
          ring
        _ = MvPolynomial.X 0 := by rw [hab, map_one, one_mul]
    · change bezoutCoordinateSubstitution u v a b
        (bezoutCoordinateSubstitution a v u b (MvPolynomial.X (1 : Fin 2))) =
          MvPolynomial.X (1 : Fin 2)
      rw [bezoutCoordinateSubstitution_X_one]
      simp only [linearSectionEquation, map_sub, map_mul, bezoutCoordinateSubstitution_C,
        bezoutCoordinateSubstitution_X_zero, bezoutCoordinateSubstitution_X_one]
      calc
        (MvPolynomial.C v *
            (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1) -
          MvPolynomial.C a *
            (MvPolynomial.C v * MvPolynomial.X 0 - MvPolynomial.C u * MvPolynomial.X 1) :
              MvPolynomial (Fin 2) R) =
            MvPolynomial.C (a * u + b * v) * MvPolynomial.X 1 := by
          simp only [map_add, map_mul]
          ring
        _ = MvPolynomial.X 1 := by rw [hab, map_one, one_mul]

private theorem bezoutCoordinateSubstitution_irrelevant
    (u v a b : R) (hab : a * u + b * v = 1) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) R) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) R)).map
        (bezoutCoordinateSubstitution u v a b) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi p hp
  have hpre : bezoutCoordinateSubstitution a v u b p ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 2) R) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi
      ((bezoutCoordinateSubstitution a v u b).map_mem hp)
  have heq : bezoutCoordinateSubstitution u v a b
      (bezoutCoordinateSubstitution a v u b p) = p := by
    exact GradedRingHom.congr_fun (bezoutCoordinateSubstitution_comp u v a b hab) p
  rw [← heq]
  exact Ideal.mem_map_of_mem (bezoutCoordinateSubstitution u v a b).toRingHom hpre

/-- The projective scheme automorphism over the base ring sending the equation of
`(u,v)` to infinity. In particular this gives the integral coordinate change over `ℤ`. -/
def integralCoordinateChange (u v a b : R) (hab : a * u + b * v = 1) :
    ProjectiveLine R ≅ ProjectiveLine R where
  hom := Proj.map (bezoutCoordinateSubstitution u v a b)
    (bezoutCoordinateSubstitution_irrelevant u v a b hab)
  inv := Proj.map (bezoutCoordinateSubstitution a v u b)
    (bezoutCoordinateSubstitution_irrelevant a v u b (by
      rw [mul_comm u a]
      exact hab))
  hom_inv_id := by
    rw [← Proj.map_comp]
    simp only [bezoutCoordinateSubstitution_comp u v a b hab, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    simp only [bezoutCoordinateSubstitution_comp a v u b (by
      rw [mul_comm u a]
      exact hab), Proj.map_id]

/-- The projective automorphism exchanging the two homogeneous coordinates. -/
def projectiveCoordinateSwap (R : Type u) [CommRing R] :
    ProjectiveLine R ≅ ProjectiveLine R :=
  integralCoordinateChange (0 : R) 1 0 1
    (by rw [zero_mul, one_mul, zero_add])

/-- The primitive linear equation is the inverse image of the infinity equation. -/
theorem integralCoordinateChange_preimage_infinity
    (u v a b : R) (hab : a * u + b * v = 1) :
    (integralCoordinateChange u v a b hab).hom ⁻¹ᵁ infinityComplement R =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (linearSectionEquation u v) := by
  change Proj.map (bezoutCoordinateSubstitution u v a b) _ ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X 1) = _
  rw [Proj.map_preimage_basicOpen, bezoutCoordinateSubstitution_X_one]

/-- The coefficient of `T₀` in the transformed second equation is the original determinant. -/
theorem inverseCoordinateSubstitution_linearSection (u v a b u' v' : ℤ) :
    bezoutCoordinateSubstitution a v u b (linearSectionEquation u' v') =
      linearSectionEquation (-(a * u' + b * v')) (coordinateDeterminant u v u' v') := by
  simp only [linearSectionEquation, map_sub, map_mul, bezoutCoordinateSubstitution_C,
    bezoutCoordinateSubstitution_X_zero, bezoutCoordinateSubstitution_X_one,
    coordinateDeterminant, map_neg, map_add]
  ring

/-- A second section equation transforms with determinant denominator under the inverse map. -/
theorem integralCoordinateChange_inv_preimage_linearSection
    (u v a b u' v' : ℤ) (hab : a * u + b * v = 1) :
    (integralCoordinateChange u v a b hab).inv ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (linearSectionEquation u' v') =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (linearSectionEquation (-(a * u' + b * v')) (coordinateDeterminant u v u' v')) := by
  change Proj.map (bezoutCoordinateSubstitution a v u b) _ ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (linearSectionEquation u' v') = _
  rw [Proj.map_preimage_basicOpen, inverseCoordinateSubstitution_linearSection]

/-- In the new coordinates, the first equation becomes the infinity equation. -/
theorem integralCoordinateChange_inv_preimage_firstSection
    (u v a b : ℤ) (hab : a * u + b * v = 1) :
    (integralCoordinateChange u v a b hab).inv ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (linearSectionEquation u v) =
      infinityComplement ℤ := by
  rw [← integralCoordinateChange_preimage_infinity u v a b hab,
    ← Scheme.Hom.comp_preimage, Iso.inv_hom_id, Scheme.Hom.id_preimage]

/-- The common nonvanishing open of two integral homogeneous linear equations. -/
def integralPairComplement (u v u' v' : ℤ) : (ProjectiveLine ℤ).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (linearSectionEquation u v) ⊓
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (linearSectionEquation u' v')

/-- The two-equation complement pulls back to the explicit standard affine complement. -/
theorem integralCoordinateChange_inv_preimage_pairComplement
    (u v a b u' v' : ℤ) (hab : a * u + b * v = 1) :
    (integralCoordinateChange u v a b hab).inv ⁻¹ᵁ integralPairComplement u v u' v' =
      twoSectionComplement (-(a * u' + b * v')) (coordinateDeterminant u v u' v') := by
  unfold integralPairComplement twoSectionComplement
  rw [Scheme.Hom.preimage_inf, integralCoordinateChange_inv_preimage_firstSection,
    integralCoordinateChange_inv_preimage_linearSection]

/-- A pair of equations with primitive first coordinates has an explicit affine localization model.

The new denominator coefficient is the determinant of the original coordinate pairs.
No affine or projective comparison is assumed: the isomorphism restricts the constructed
projective automorphism and then uses the standard chart comparison.
-/
def integralPairComplementIso (u v a b u' v' : ℤ) (hab : a * u + b * v = 1) :
    (integralPairComplement u v u' v').toScheme ≅
      Spec (CommRingCat.of (TwoSectionCoordinateRing (-(a * u' + b * v'))
        (coordinateDeterminant u v u' v'))) :=
  ((integralCoordinateChange u v a b hab).inv.preimageIso
      (integralPairComplement u v u' v')).symm ≪≫
    (ProjectiveLine ℤ).isoOfEq
      (integralCoordinateChange_inv_preimage_pairComplement u v a b u' v' hab) ≪≫
        twoSectionComplementIso (-(a * u' + b * v')) (coordinateDeterminant u v u' v')

/-- The complement of any primitive integral linear equation is an affine line. -/
theorem nonempty_primitiveSectionComplementIso
    (u v : ℤ) (huv : IsCoprime u v) :
    Nonempty ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      (linearSectionEquation u v)).toScheme ≅ Spec (CommRingCat.of (Polynomial ℤ))) := by
  obtain ⟨a, b, hab⟩ := huv
  exact ⟨(ProjectiveLine ℤ).isoOfEq
    (integralCoordinateChange_preimage_infinity u v a b hab).symm ≪≫
      (integralCoordinateChange u v a b hab).hom.preimageIso (infinityComplement ℤ) ≪≫
        standardAffineChartIso ℤ⟩

end ShimizuYamaguchi26BranchedCoverings
