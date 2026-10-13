/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.Smooth
import Nyll.SchemeTheory.ProjectiveSpace.GenericPoint
import Nyll.SchemeTheory.Divisors.LocalComplement
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FieldSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionFamily
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Irreducible

/-!
# Geometry of the complement of rational sections

The structure morphism of the actual finite-section complement is smooth and
has geometrically connected fibers. The latter also supplies surjectivity via
the existing `GeometricallyConnected` instance. In particular its generic
fiber is geometrically connected.

For each field, the zero homogeneous prime avoids every primitive linear
section. The coefficient pullback of the complement is thus a nonempty open
subset of an irreducible projective line. Pasting the actual projective-space
base-change square with the open-restriction square identifies this open with
the required fiber product.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1), Observation 2.1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The complement of finitely many rational sections is smooth over `Spec ℤ`. -/
theorem rationalSectionFamily_complement_smooth
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    Smooth ((∏ a ∈ A, (rationalSection a).ker).supportComplement.ι ≫
      ProjSpace.π ℤ 1) := by
  have : Smooth (ProjSpace.π ℤ 1) := ProjSpace.smooth_π ℤ 1
  infer_instance

private theorem linearSectionEquation_ne_zero {K : Type} [Field K]
    (u v : K) (huv : u ≠ 0 ∨ v ≠ 0) : linearSectionEquation u v ≠ 0 := by
  intro hzero
  have hu := congrArg (fieldSectionEvaluation (0 : K) 1) hzero
  have hv := congrArg (fieldSectionEvaluation (1 : K) 0) hzero
  rw [fieldSectionEvaluation_linearSectionEquation, map_zero,
    mul_zero, mul_one, zero_sub, neg_eq_zero] at hu
  rw [fieldSectionEvaluation_linearSectionEquation, map_zero,
    mul_one, mul_zero, sub_zero] at hv
  exact huv.elim (fun h => h hu) (fun h => h hv)

/-- The zero homogeneous prime over any field avoids every original rational
section, even when distinct sections meet after reduction. -/
theorem projectiveGenericPoint_mem_rationalSectionFamily_complement
    (K : Type) [Field K] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    ProjSpace.genericPoint K 1 ∈ ProjSpace.map ℤ K 1 ⁻¹ᵁ
      (∏ a ∈ A, (rationalSection a).ker).supportComplement := by
  change ProjSpace.map ℤ K 1 (ProjSpace.genericPoint K 1) ∈
    (∏ a ∈ A, (rationalSection a).ker).supportComplement
  rw [Scheme.IdealSheafData.mem_supportComplement]
  intro hsupport
  obtain ⟨a, _, ha⟩ := (mem_support_finset_prod_iff A
    (fun a => (rationalSection a).ker) _).mp hsupport
  have hrange := (mem_kernel_support_iff_range (rationalSection a)
    (ProjSpace.map ℤ K 1 (ProjSpace.genericPoint K 1))).mp ha
  have hequation := (mem_rationalSectionSupport_baseChange_iff K a
    (ProjSpace.genericPoint K 1)).mp ((range_rationalSection a) ▸ hrange)
  change linearSectionEquation (rationalPointNumerator a : K)
    (rationalPointDenominator a : K) = 0 at hequation
  exact linearSectionEquation_ne_zero _ _
    (((rationalPointCoordinates_isCoprime a).intCast (R := K)).ne_zero_or_ne_zero)
    hequation

/-- Over every field the coefficient pullback of the actual section complement
is irreducible; no bound on the number of sections or on the characteristic is needed. -/
theorem rationalSectionFamily_baseChangeComplement_irreducible
    (K : Type) [Field K] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    IrreducibleSpace
      (ProjSpace.map ℤ K 1 ⁻¹ᵁ (∏ a ∈ A, (rationalSection a).ker).supportComplement) := by
  have : IrreducibleSpace (ProjectiveLine K) := ProjSpace.irreducibleSpace K 1
  let V : (ProjectiveLine K).Opens :=
    ProjSpace.map ℤ K 1 ⁻¹ᵁ (∏ a ∈ A, (rationalSection a).ker).supportComplement
  have : Nonempty V :=
    ⟨⟨ProjSpace.genericPoint K 1,
      projectiveGenericPoint_mem_rationalSectionFamily_complement K A⟩⟩
  exact V.ι.isOpenEmbedding.irreducibleSpace

/-- Every geometric fiber of the actual finite-section complement over `Spec ℤ`
is connected. This gives both surjectivity and geometric generic connectedness. -/
theorem rationalSectionFamily_complement_geometricallyConnected
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    GeometricallyConnected
      ((∏ a ∈ A, (rationalSection a).ker).supportComplement.ι ≫ ProjSpace.π ℤ 1) := by
  let U : (ProjectiveLine ℤ).Opens :=
    (∏ a ∈ A, (rationalSection a).ker).supportComplement
  refine ⟨?_⟩
  intro K hK y Z fst snd h
  have hy : y = Spec.map (CommRingCat.ofHom (algebraMap ℤ K)) :=
    specZIsTerminal.hom_ext _ _
  subst y
  let V : (ProjectiveLine K).Opens := ProjSpace.map ℤ K 1 ⁻¹ᵁ U
  have hcanonical : CategoryTheory.IsPullback
      (ProjSpace.map ℤ K 1 ∣_ U) (V.ι ≫ ProjSpace.π K 1)
      (U.ι ≫ ProjSpace.π ℤ 1)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) :=
    (isPullback_morphismRestrict (ProjSpace.map ℤ K 1) U).paste_vert
      (ProjSpace.isPullback_map ℤ K 1)
  have : IrreducibleSpace V := rationalSectionFamily_baseChangeComplement_irreducible K A
  let e : Z ≅ V.toScheme := h.isoIsPullback _ _ hcanonical
  exact e.hom.homeomorph.connectedSpace_iff.mpr inferInstance

end ShimizuYamaguchi26BranchedCoverings
