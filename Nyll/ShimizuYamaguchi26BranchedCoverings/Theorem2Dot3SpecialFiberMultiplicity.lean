/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.IntegerLocalizationValuation
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot3IntersectionMultiplicity
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Set.Image
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Lemma 2.3: intersection length at an arbitrary special-fibre point

A point of the actual prime special fibre lying on an original rational
section maps to that section's point over `(p)` on the integral projective
line. This is proved from the section identity and the contraction of the
unique prime of `ZMod p`, without assuming an identification of points.

The existing intersection-length theorem can consequently be evaluated at
any such point, including the unique closed intersection point supplied by
`SpecialFiberIntersection`. Both the ring and the intersection ideal are
transported along the same equality of actual scheme points.

Source: Ryoji Shimizu and Naganori Yamaguchi, Lemma 2.3 of
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ShimizuYamaguchi26BranchedCoverings

private theorem specialFiber_projection_eq_integerPrimePoint
    (p : ℕ) [Fact p.Prime] (y : ProjectiveLine (ZMod p)) :
    ProjSpace.π ℤ 1 (ProjSpace.map ℤ (ZMod p) 1 y) = integerPrimePoint p := by
  have hcomp : ProjSpace.map ℤ (ZMod p) 1 ≫ ProjSpace.π ℤ 1 =
      ProjSpace.π (ZMod p) 1 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))) :=
    specZIsTerminal.hom_ext _ _
  change (ProjSpace.map ℤ (ZMod p) 1 ≫ ProjSpace.π ℤ 1) y = _
  rw [hcomp, Scheme.Hom.comp_apply]
  have hy : ProjSpace.π (ZMod p) 1 y = (⊥ : PrimeSpectrum (ZMod p)) :=
    Subsingleton.elim _ _
  rw [hy]
  apply PrimeSpectrum.ext
  ext z
  change algebraMap ℤ (ZMod p) z ∈ (⊥ : Ideal (ZMod p)) ↔
    z ∈ Ideal.span ({(p : ℤ)} : Set ℤ)
  rw [Ideal.mem_bot, Ideal.mem_span_singleton]
  simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p)

/-- Any point on an original rational section in the prime special fibre
has exactly the section's original integral point over `(p)` as its image. -/
theorem specialFiber_image_eq_rationalSection_primePoint
    (p : ℕ) [Fact p.Prime] (b : Projectivization ℚ (ℚ × ℚ))
    (y : ProjectiveLine (ZMod p))
    (hy : ProjSpace.map ℤ (ZMod p) 1 y ∈ rationalSectionSupport b) :
    ProjSpace.map ℤ (ZMod p) 1 y = rationalSection b (integerPrimePoint p) := by
  rw [← range_rationalSection] at hy
  obtain ⟨q, hq⟩ := hy
  have hbase := congrArg (ProjSpace.π ℤ 1) hq
  rw [← Scheme.Hom.comp_apply, rationalSection_comp_π] at hbase
  exact hq.symm.trans (congrArg (rationalSection b)
    (hbase.trans (specialFiber_projection_eq_integerPrimePoint p y)))

/-- The original local intersection length at the image of any
special-fibre point on the second section is the paper's determinant
valuation. A common point of the two sections is a special case; no choice
of coordinates or a preassigned equality of points is required. -/
theorem rationalSectionIntersection_length_at_specialFiber_point
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b)
    (y : ProjectiveLine (ZMod p))
    (hy : ProjSpace.map ℤ (ZMod p) 1 y ∈ rationalSectionSupport b) :
    let x : ProjectiveLine ℤ := ProjSpace.map ℤ (ZMod p) 1 y
    Module.length ((ProjectiveLine ℤ).presheaf.stalk x)
      ((ProjectiveLine ℤ).presheaf.stalk x ⧸ rationalSectionIntersectionIdeal a b x) =
        (padicValInt p (rationalPointDelta a b) : ℕ∞) := by
  intro x
  have hpoint : x = rationalSection b (integerPrimePoint p) :=
    specialFiber_image_eq_rationalSection_primePoint p b y hy
  have hlength := congrArg (fun z : ProjectiveLine ℤ =>
    Module.length ((ProjectiveLine ℤ).presheaf.stalk z)
      ((ProjectiveLine ℤ).presheaf.stalk z ⧸ rationalSectionIntersectionIdeal a b z)) hpoint
  exact hlength.trans (rationalSectionIntersection_length p a b hab)

end ShimizuYamaguchi26BranchedCoverings
