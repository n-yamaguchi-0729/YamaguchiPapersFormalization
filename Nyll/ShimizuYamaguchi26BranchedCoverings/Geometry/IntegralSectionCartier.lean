/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.CartierEtale
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PrimitiveSectionIdeal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Sets.Opens

/-!
# The actual ideal of an integral rational section is effective Cartier

On the two polynomial charts, the section at infinity has equations `X`
and `1`. An integral projective coordinate change then transports its
actual kernel ideal to that of any rational section.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem isEffectiveCartierAt_of_polynomial_chart
    (I : (ProjectiveLine ℤ).IdealSheafData)
    (j : Spec (CommRingCat.of ℤ[X]) ⟶ ProjectiveLine ℤ)
    [IsOpenImmersion j] (f : ℤ[X]) (hf : f ≠ 0)
    (htop :
      (I.comap j).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of ℤ[X]))⟩ =
        (Ideal.span {f}).map (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom)
    (q : Spec (CommRingCat.of ℤ[X])) :
    I.IsEffectiveCartierAt (j q) := by
  let Y : Scheme := Spec (CommRingCat.of ℤ[X])
  let T : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let U : (ProjectiveLine ℤ).affineOpens :=
    ⟨j ''ᵁ ⊤, (isAffineOpen_top Y).image_of_isOpenImmersion j⟩
  let c : Γ(ProjectiveLine ℤ, U.1) ≅ Γ(Y, ⊤) := j.appIso ⊤
  let k : Γ(Y, ⊤) →+* Γ(ProjectiveLine ℤ, U.1) := c.inv.hom
  let e : ℤ[X] ≃+* Γ(ProjectiveLine ℤ, U.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).symm.commRingCatIsoToRingEquiv).trans
      c.symm.commRingCatIsoToRingEquiv
  have : IsDomain Γ(ProjectiveLine ℤ, U.1) :=
    MulEquiv.isDomain ℤ[X] e.symm.toMulEquiv
  have hregular : IsRegular (e f) := by
    apply IsRegular.of_ne_zero
    intro h
    exact hf (e.injective (h.trans (map_zero e).symm))
  have hcomap : (I.comap j).ideal T = (I.ideal U).comap k :=
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I j T
  have hideal : I.ideal U =
      ((Ideal.span {f}).map
        (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom).map k :=
    (Ideal.map_comap_of_surjective k
      c.symm.commRingCatIsoToRingEquiv.surjective (I.ideal U)).symm.trans
        (congrArg (Ideal.map k) (hcomap.symm.trans htop))
  have hspan : I.ideal U = Ideal.span {e f} := by
    rw [hideal, Ideal.map_span, Set.image_singleton,
      Ideal.map_span, Set.image_singleton]
    have hΓ :
        ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).symm.commRingCatIsoToRingEquiv :
          ℤ[X] →+* Γ(Y, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom :=
      Iso.commRingCatIsoToRingEquiv_toRingHom
        (R := CommRingCat.of ℤ[X]) (S := Γ(Y, ⊤))
        (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).symm
    have he : e.toRingHom =
        k.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom := by
      simp only [e, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_ringHom_trans,
        Iso.commRingCatIsoToRingEquiv_toRingHom, Iso.symm_hom, k]
      exact congrArg (fun g : ℤ[X] →+* Γ(Y, ⊤) => c.inv.hom.comp g) hΓ
    have heval : e f = k ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom f) :=
      congrArg (fun g : ℤ[X] →+* Γ(ProjectiveLine ℤ, U.1) => g f) he
    exact congrArg (fun z : Γ(ProjectiveLine ℤ, U.1) => Ideal.span {z}) heval.symm
  have hqU : j q ∈ U.1 :=
    j.apply_mem_image_iff.mpr (show q ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨U, hqU, e f, hregular, hspan⟩

private theorem infinitySection_ker_isEffectiveCartier :
    (integralSection 1 0 1 0 (by decide)).ker.IsEffectiveCartier := by
  let I : (ProjectiveLine ℤ).IdealSheafData :=
    (integralSection 1 0 1 0 (by decide)).ker
  have hInf :
      (I.comap (infinityChartEmbedding ℤ)).ideal
          ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of ℤ[X]))⟩ =
        (Ideal.span {(Polynomial.X : ℤ[X])}).map
          (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom := by
    simpa only [I, infinitySectionIdeal, map_zero, map_one, one_mul,
      zero_sub, Ideal.span_singleton_neg] using
      integralSection_infinityChart_ideal_top 1 0 1 0 (by decide)
  have hj : infinityChartEmbedding ℤ ≫ (projectiveCoordinateSwap ℤ).inv =
      standardChartEmbedding ℤ := by
    rw [infinityChartEmbedding, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hswapIdeal : I.comap (projectiveCoordinateSwap ℤ).inv =
      (integralSection 0 (-1) 0 (-1) (by decide)).ker :=
    integralSection_ker_comap_coordinateChange_inv
      0 1 0 1 1 0 1 0 0 (-1) (by decide) (by decide) (by decide)
  have hstdPull : I.comap (standardChartEmbedding ℤ) =
      (integralSection 0 (-1) 0 (-1) (by decide)).ker.comap
        (infinityChartEmbedding ℤ) := by
    rw [← hj, Scheme.IdealSheafData.comap_comp, hswapIdeal]
  have hStd :
      (I.comap (standardChartEmbedding ℤ)).ideal
          ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of ℤ[X]))⟩ =
        (Ideal.span {(1 : ℤ[X])}).map
          (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom := by
    rw [hstdPull]
    simpa only [infinitySectionIdeal, map_neg, map_one, map_zero,
      zero_mul, sub_zero, Ideal.span_singleton_neg] using
      integralSection_infinityChart_ideal_top 0 (-1) 0 (-1) (by decide)
  have hcover :
      (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)
      (ProjSpace.irrelevant_le_span_X ℤ 1)
  change I.IsEffectiveCartier
  intro x
  have hx : x ∈
      (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (MvPolynomial.X i)) := by
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  fin_cases i
  · have hmem : x ∈ (infinityChartEmbedding ℤ).opensRange := by
      rw [infinityChartEmbedding_opensRange]
      exact hi
    change x ∈ Set.range (infinityChartEmbedding ℤ) at hmem
    obtain ⟨q, rfl⟩ := hmem
    exact isEffectiveCartierAt_of_polynomial_chart I (infinityChartEmbedding ℤ)
      Polynomial.X Polynomial.X_ne_zero hInf q
  · have hmem : x ∈ (standardChartEmbedding ℤ).opensRange := by
      rw [standardChartEmbedding_opensRange, infinityComplement]
      exact hi
    change x ∈ Set.range (standardChartEmbedding ℤ) at hmem
    obtain ⟨q, rfl⟩ := hmem
    exact isEffectiveCartierAt_of_polynomial_chart I (standardChartEmbedding ℤ)
      1 one_ne_zero hStd q

/-- The actual kernel ideal of the integral section associated with a rational
projective point defines an effective Cartier divisor. -/
theorem rationalSection_ker_isEffectiveCartier
    (a : Projectivization ℚ (ℚ × ℚ)) :
    (rationalSection a).ker.IsEffectiveCartier := by
  let ha : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  let e : ProjectiveLine ℤ ≅ ProjectiveLine ℤ :=
    integralCoordinateChange (rationalPointNumerator a) (rationalPointDenominator a)
      ha.choose ha.choose_spec.choose ha.choose_spec.choose_spec
  let I : (ProjectiveLine ℤ).IdealSheafData := (rationalSection a).ker
  let J : (ProjectiveLine ℤ).IdealSheafData :=
    (integralSection 1 0 1 0 (by decide)).ker
  have hpull : I.comap e.inv = J :=
    integralSection_ker_comap_coordinateChange_inv_self
      (rationalPointNumerator a) (rationalPointDenominator a)
      ha.choose ha.choose_spec.choose ha.choose_spec.choose_spec
  have hback : J.comap e.hom = I := by
    rw [← hpull, ← Scheme.IdealSheafData.comap_comp,
      e.hom_inv_id, Scheme.IdealSheafData.comap_id]
  have hCartier : (J.comap e.hom).IsEffectiveCartier :=
    Scheme.IdealSheafData.IsEffectiveCartier.comap_of_flat_of_isAffineHom
      J infinitySection_ker_isEffectiveCartier e.hom
  change I.IsEffectiveCartier
  exact hback ▸ hCartier

end ShimizuYamaguchi26BranchedCoverings
