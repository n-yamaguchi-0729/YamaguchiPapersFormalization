/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FieldSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Data.Set.Insert
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The unique closed point of a homogeneous linear equation over a field

The equation `v*T₀-u*T₁` for a nonzero pair `(u,v)` has exactly the point
constructed by homogeneous evaluation as its zero locus in the actual
projective scheme. If `v` is nonzero, relevance forces the zero locus into
the standard affine chart, where the equation generates the maximal ideal
of evaluation at `u/v`. A coordinate exchange treats the point at infinity.
The singleton is closed because it is this projective zero locus.

This proves the field-fibre uniqueness underlying the first assertion of
Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

private theorem coordinate_mem_of_scaled_mem (x : ProjectiveLine k)
    (c : k) (hc : c ≠ 0) (i : Fin 2)
    (h : MvPolynomial.C c * MvPolynomial.X i ∈ x.asHomogeneousIdeal) :
    MvPolynomial.X i ∈ x.asHomogeneousIdeal := by
  have hm := x.asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.C c⁻¹) h
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at hm
  exact hm

private theorem linearSection_mem_infinityComplement (u v : k) (hv : v ≠ 0)
    (x : ProjectiveLine k) (h : linearSectionEquation u v ∈ x.asHomogeneousIdeal) :
    x ∈ infinityComplement k := by
  change MvPolynomial.X (1 : Fin 2) ∉ x.asHomogeneousIdeal
  intro hx1
  have hvx0 : MvPolynomial.C v * MvPolynomial.X 0 ∈ x.asHomogeneousIdeal := by
    apply HomogeneousIdeal.mem_iff.mp
    have hm := x.asHomogeneousIdeal.toIdeal.add_mem h
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.C u) hx1)
    simpa only [linearSectionEquation, sub_add_cancel] using hm
  exact projectiveLine_not_both_coordinates_mem x
    (coordinate_mem_of_scaled_mem x v hv 0 hvx0) hx1

private theorem affinePrime_eq_evalKer (u v : k) (hv : v ≠ 0)
    (q : PrimeSpectrum (Polynomial k))
    (hq : Polynomial.C v * Polynomial.X - Polynomial.C u ∈ q.asIdeal) :
    q.asIdeal = RingHom.ker (Polynomial.evalRingHom (u / v)) := by
  have hnorm : Polynomial.C v⁻¹ * (Polynomial.C v * Polynomial.X - Polynomial.C u) =
      Polynomial.X - Polynomial.C (u / v) := by
    rw [mul_sub, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hv,
      Polynomial.C_1, one_mul, ← Polynomial.C_mul, div_eq_mul_inv, mul_comm u]
  have hlinear : Polynomial.X - Polynomial.C (u / v) ∈ q.asIdeal := by
    rw [← hnorm]
    exact q.asIdeal.mul_mem_left (Polynomial.C v⁻¹) hq
  have hmax : (RingHom.ker (Polynomial.evalRingHom (u / v))).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom (u / v))
      (Polynomial.eval_surjective (u / v))
  have hle : RingHom.ker (Polynomial.evalRingHom (u / v)) ≤ q.asIdeal := by
    rw [Polynomial.ker_evalRingHom, Ideal.span_le, Set.singleton_subset_iff]
    exact hlinear
  exact (hmax.eq_of_le q.isPrime.ne_top hle).symm

private theorem affineLinear_mem_of_section_mem (u v : k)
    (q : PrimeSpectrum (Polynomial k))
    (h : linearSectionEquation u v ∈
      (standardChartEmbedding k q).asHomogeneousIdeal) :
    Polynomial.C v * Polynomial.X - Polynomial.C u ∈ q.asIdeal := by
  classical
  by_contra hq
  have hpre : q ∈ standardChartEmbedding k ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (linearSectionEquation u v) := by
    rw [standardChartEmbedding_preimage_linearSection u v]
    exact (PrimeSpectrum.mem_basicOpen _ q).mpr hq
  change linearSectionEquation u v ∉
    (standardChartEmbedding k q).asHomogeneousIdeal at hpre
  exact hpre h

private theorem eq_of_linearSection_mem_of_snd_ne_zero
    (u v : k) (hv : v ≠ 0) (x y : ProjectiveLine k)
    (hx : linearSectionEquation u v ∈ x.asHomogeneousIdeal)
    (hy : linearSectionEquation u v ∈ y.asHomogeneousIdeal) : x = y := by
  have hxrange : x ∈ (standardChartEmbedding k).opensRange := by
    rw [standardChartEmbedding_opensRange]
    exact linearSection_mem_infinityComplement u v hv x hx
  have hyrange : y ∈ (standardChartEmbedding k).opensRange := by
    rw [standardChartEmbedding_opensRange]
    exact linearSection_mem_infinityComplement u v hv y hy
  obtain ⟨qx, hqx⟩ := Scheme.Hom.mem_opensRange.mp hxrange
  obtain ⟨qy, hqy⟩ := Scheme.Hom.mem_opensRange.mp hyrange
  have hqxmem : Polynomial.C v * Polynomial.X - Polynomial.C u ∈ qx.asIdeal :=
    affineLinear_mem_of_section_mem u v qx (hqx.symm ▸ hx)
  have hqymem : Polynomial.C v * Polynomial.X - Polynomial.C u ∈ qy.asIdeal :=
    affineLinear_mem_of_section_mem u v qy (hqy.symm ▸ hy)
  have hqq : qx = qy := PrimeSpectrum.ext
    ((affinePrime_eq_evalKer u v hv qx hqxmem).trans
      (affinePrime_eq_evalKer u v hv qy hqymem).symm)
  exact hqx.symm.trans ((congrArg (standardChartEmbedding k) hqq).trans hqy)

private theorem eq_of_linearSection_mem
    (u v : k) (huv : u ≠ 0 ∨ v ≠ 0) (x y : ProjectiveLine k)
    (hx : linearSectionEquation u v ∈ x.asHomogeneousIdeal)
    (hy : linearSectionEquation u v ∈ y.asHomogeneousIdeal) : x = y := by
  by_cases hv : v = 0
  · have hu : u ≠ 0 := huv.resolve_right (fun hv' => hv' hv)
    have hcoordinate (z : ProjectiveLine k)
        (hz : linearSectionEquation u v ∈ z.asHomogeneousIdeal) :
        MvPolynomial.X (1 : Fin 2) ∈ z.asHomogeneousIdeal := by
      apply coordinate_mem_of_scaled_mem z u hu 1
      apply z.asHomogeneousIdeal.toIdeal.neg_mem_iff.mp
      apply HomogeneousIdeal.mem_iff.mpr
      simpa only [linearSectionEquation, hv, map_zero, zero_mul, zero_sub] using hz
    let e : ProjectiveLine k ≅ ProjectiveLine k :=
      integralCoordinateChange (0 : k) 1 0 1 (by rw [zero_mul, one_mul, zero_add])
    have hswap (z : ProjectiveLine k)
        (hz : MvPolynomial.X (1 : Fin 2) ∈ z.asHomogeneousIdeal) :
        linearSectionEquation (0 : k) 1 ∈ (e.hom z).asHomogeneousIdeal := by
      change bezoutCoordinateSubstitution (0 : k) 1 0 1
        (linearSectionEquation (0 : k) 1) ∈ z.asHomogeneousIdeal
      rw [show linearSectionEquation (0 : k) 1 = MvPolynomial.X 0 by
        simp only [linearSectionEquation, map_one, map_zero, one_mul, zero_mul, sub_zero],
        bezoutCoordinateSubstitution_X_zero]
      simpa only [map_zero, map_one, zero_mul, one_mul, zero_add] using hz
    exact (Scheme.homeoOfIso e).injective
      (eq_of_linearSection_mem_of_snd_ne_zero (0 : k) 1 one_ne_zero (e.hom x) (e.hom y)
        (hswap x (hcoordinate x hx)) (hswap y (hcoordinate y hy)))
  · exact eq_of_linearSection_mem_of_snd_ne_zero u v hv x y hx hy

/-- A point of the projective line containing the nonzero homogeneous linear equation
is the point constructed by evaluation at its coordinates. -/
theorem eq_fieldSectionPoint_of_linearSection_mem
    (u v : k) (huv : u ≠ 0 ∨ v ≠ 0) (x : ProjectiveLine k)
    (h : linearSectionEquation u v ∈ x.asHomogeneousIdeal) :
    x = fieldSectionPoint u v huv :=
  eq_of_linearSection_mem u v huv x (fieldSectionPoint u v huv) h
    (linearSectionEquation_mem_fieldSectionPoint u v huv)

/-- The zero locus of a nonzero homogeneous linear equation is exactly its rational point. -/
theorem zeroLocus_linearSectionEquation_eq_singleton
    (u v : k) (huv : u ≠ 0 ∨ v ≠ 0) :
    ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) k)
      {linearSectionEquation u v} = {fieldSectionPoint u v huv} := by
  apply Set.ext
  intro x
  refine (ProjectiveSpectrum.mem_zeroLocus
    (MvPolynomial.homogeneousSubmodule (Fin 2) k) x {linearSectionEquation u v}).trans ?_
  change {linearSectionEquation u v} ⊆ (x.asHomogeneousIdeal : Set (MvPolynomial (Fin 2) k)) ↔
    x = fieldSectionPoint u v huv
  rw [Set.singleton_subset_iff]
  constructor
  · exact eq_fieldSectionPoint_of_linearSection_mem u v huv x
  · rintro rfl
    exact linearSectionEquation_mem_fieldSectionPoint u v huv

/-- The actual projective-scheme point supplied by a nonzero field-valued pair is closed. -/
theorem isClosed_singleton_fieldSectionPoint (u v : k) (huv : u ≠ 0 ∨ v ≠ 0) :
    IsClosed ({fieldSectionPoint u v huv} : Set (ProjectiveLine k)) := by
  have hclosed : IsClosed
      (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        {linearSectionEquation u v} : Set (ProjectiveLine k)) :=
    ProjectiveSpectrum.isClosed_zeroLocus
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) {linearSectionEquation u v}
  exact (congrArg (fun S : Set (ProjectiveLine k) => IsClosed S)
    (zeroLocus_linearSectionEquation_eq_singleton u v huv)).mp hclosed

end ShimizuYamaguchi26BranchedCoverings
