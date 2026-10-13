/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.CartierProducts
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionCartier
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionIdeal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PrimitiveSectionIdeal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Topology.Sets.Closeds

/-!
# The reduced union of finitely many rational sections

For distinct rational points, the actual section kernel ideals have product
equal to their intersection. On each standard affine chart this is the
existing calculation for distinct primitive linear factors in `ℤ[X]`.
Consequently the product is the vanishing ideal of the union of the closures
of those rational points, with its reduced scheme structure.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1), §2 and Lemma 2.3.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem sectionFamily_inf_eq_prod_on_chart {ι : Type*}
    (A : Finset ι) (I : ι → (ProjectiveLine ℤ).IdealSheafData)
    (j : Spec (CommRingCat.of ℤ[X]) ⟶ ProjectiveLine ℤ) [IsOpenImmersion j]
    (u v : ι → ℤ) (hprimitive : ∀ a ∈ A, IsCoprime (u a) (v a))
    (hdet : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      coordinateDeterminant (u a) (v a) (u b) (v b) ≠ 0)
    (htop : ∀ a ∈ A,
      ((I a).comap j).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of ℤ[X]))⟩ =
        (infinitySectionIdeal (u a) (v a)).map
          (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom) :
    (A.inf I).ideal ⟨j ''ᵁ ⊤, (isAffineOpen_top
        (Spec (CommRingCat.of ℤ[X]))).image_of_isOpenImmersion j⟩ =
      (∏ a ∈ A, I a).ideal ⟨j ''ᵁ ⊤, (isAffineOpen_top
        (Spec (CommRingCat.of ℤ[X]))).image_of_isOpenImmersion j⟩ := by
  classical
  let Y : Scheme := Spec (CommRingCat.of ℤ[X])
  let T : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let U : (ProjectiveLine ℤ).affineOpens :=
    ⟨j ''ᵁ ⊤, (isAffineOpen_top Y).image_of_isOpenImmersion j⟩
  let c : Γ(ProjectiveLine ℤ, U.1) ≅ Γ(Y, ⊤) := j.appIso ⊤
  let k : Γ(Y, ⊤) →+* Γ(ProjectiveLine ℤ, U.1) := c.inv.hom
  let e : ℤ[X] ≃+* Γ(ProjectiveLine ℤ, U.1) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).symm ≪≫ c.symm).commRingCatIsoToRingEquiv
  let P : ι → Ideal ℤ[X] := fun a => infinitySectionIdeal (u a) (v a)
  have he : (e : ℤ[X] →+* Γ(ProjectiveLine ℤ, U.1)) =
      k.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom := by
    rw [Iso.commRingCatIsoToRingEquiv_toRingHom]
    rfl
  have hI (a : ι) (ha : a ∈ A) : (I a).ideal U = (P a).map e := by
    have hcomap : ((I a).comap j).ideal T = ((I a).ideal U).comap k :=
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I a) j T
    calc
      (I a).ideal U = (((I a).ideal U).comap k).map k :=
        (Ideal.map_comap_of_surjective k c.symm.commRingCatIsoToRingEquiv.surjective
          ((I a).ideal U)).symm
      _ = ((P a).map (Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom).map k :=
        congrArg (Ideal.map k) (hcomap.symm.trans (htop a ha))
      _ = (P a).map e := by rw [Ideal.map_map, ← he, Ideal.map_coe]
  have hinf : (A.inf I).ideal U = A.inf (fun a => (I a).ideal U) := by
    refine Finset.induction_on A ?_ ?_
    · simp only [Finset.inf_empty, Scheme.IdealSheafData.ideal_top, Pi.top_apply]
    · intro a B ha ih
      simp only [Finset.inf_insert, Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, ih]
  have hprod : (∏ a ∈ A, I a).ideal U = ∏ a ∈ A, (I a).ideal U := by
    refine Finset.induction_on A ?_ ?_
    · simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.ideal_top, Pi.top_apply, Ideal.one_eq_top]
    · intro a B ha ih
      simp only [Finset.prod_insert ha, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih]
  change (A.inf I).ideal U = (∏ a ∈ A, I a).ideal U
  rw [hinf, hprod]
  calc
    A.inf (fun a => (I a).ideal U) = A.inf (fun a => (P a).map e) :=
      Finset.inf_congr rfl hI
    _ = (A.inf P).map e :=
      (map_finset_inf e.idealComapOrderIso.symm A P).symm
    _ = (∏ a ∈ A, P a).map e :=
      congrArg (Ideal.map e) (infinitySectionIdeal_finset_inf_eq_prod
        A u v hprimitive hdet)
    _ = ∏ a ∈ A, (P a).map e := map_prod (Ideal.mapHom e) P A
    _ = ∏ a ∈ A, (I a).ideal U := Finset.prod_congr rfl fun a ha => (hI a ha).symm

/-- The product of the actual ideals of distinct rational sections is their
intersection; no coprimality of their reductions at a prime is required. -/
theorem rationalSectionFamily_inf_eq_prod
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (A.inf fun a => (rationalSection a).ker) = ∏ a ∈ A, (rationalSection a).ker := by
  classical
  let Y : Scheme := Spec (CommRingCat.of ℤ[X])
  let U₀ : (ProjectiveLine ℤ).affineOpens :=
    ⟨(infinityChartEmbedding ℤ) ''ᵁ ⊤,
      (isAffineOpen_top Y).image_of_isOpenImmersion (infinityChartEmbedding ℤ)⟩
  let U₁ : (ProjectiveLine ℤ).affineOpens :=
    ⟨(standardChartEmbedding ℤ) ''ᵁ ⊤,
      (isAffineOpen_top Y).image_of_isOpenImmersion (standardChartEmbedding ℤ)⟩
  let U : Fin 2 → (ProjectiveLine ℤ).affineOpens := fun i => if i = 0 then U₀ else U₁
  have hU (i : Fin 2) : (U i).1 =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i) := by
    fin_cases i
    · change (infinityChartEmbedding ℤ) ''ᵁ ⊤ = _
      rw [Scheme.Hom.image_top_eq_opensRange, infinityChartEmbedding_opensRange]
      rfl
    · change (standardChartEmbedding ℤ) ''ᵁ ⊤ = _
      rw [Scheme.Hom.image_top_eq_opensRange, standardChartEmbedding_opensRange,
        infinityComplement]
      rfl
  have hcover : (⨆ i : Fin 2, (U i).1) = ⊤ :=
    (iSup_congr hU).trans
      (Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
        (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)
        (ProjSpace.irrelevant_le_span_X ℤ 1))
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro i
  fin_cases i
  · apply sectionFamily_inf_eq_prod_on_chart A (fun a => (rationalSection a).ker)
      (infinityChartEmbedding ℤ) rationalPointNumerator rationalPointDenominator
    · exact fun a _ => rationalPointCoordinates_isCoprime a
    · exact fun a _ b _ hab => rationalPoint_coordinateDeterminant_ne_zero a b hab
    · intro a ha
      let h : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
        rationalPointCoordinates_isCoprime a
      exact integralSection_infinityChart_ideal_top
        (rationalPointNumerator a) (rationalPointDenominator a)
        h.choose h.choose_spec.choose h.choose_spec.choose_spec
  · apply sectionFamily_inf_eq_prod_on_chart A (fun a => (rationalSection a).ker)
      (standardChartEmbedding ℤ)
      (fun a => -(rationalPointDenominator a)) (fun a => -(rationalPointNumerator a))
    · intro a ha
      simpa only [zero_mul, one_mul, zero_add, coordinateDeterminant, zero_sub] using
        isCoprime_normalizedCoordinates 0 1 0 1
          (rationalPointNumerator a) (rationalPointDenominator a) (by decide)
          (rationalPointCoordinates_isCoprime a)
    · intro a ha b hb hab
      have hdet := rationalPoint_coordinateDeterminant_ne_zero a b hab
      have heq :
          coordinateDeterminant (-(rationalPointDenominator a)) (-(rationalPointNumerator a))
            (-(rationalPointDenominator b)) (-(rationalPointNumerator b)) =
          -coordinateDeterminant (rationalPointNumerator a) (rationalPointDenominator a)
            (rationalPointNumerator b) (rationalPointDenominator b) := by
        unfold coordinateDeterminant
        ring
      rw [heq]
      exact neg_ne_zero.mpr hdet
    · intro a ha
      let u : ℤ := rationalPointNumerator a
      let v : ℤ := rationalPointDenominator a
      let h : IsCoprime u v := rationalPointCoordinates_isCoprime a
      let c : ℤ := h.choose
      let d : ℤ := h.choose_spec.choose
      have hcd : c * u + d * v = 1 := h.choose_spec.choose_spec
      have hcd' : (-d) * (-v) + (-c) * (-u) = 1 := by
        calc
          (-d) * (-v) + (-c) * (-u) = c * u + d * v := by ring
          _ = 1 := hcd
      have hswap : (rationalSection a).ker.comap (projectiveCoordinateSwap ℤ).inv =
          (integralSection (-v) (-u) (-d) (-c) hcd').ker := by
        change (integralSection u v c d hcd).ker.comap (projectiveCoordinateSwap ℤ).inv =
          (integralSection (-v) (-u) (-d) (-c) hcd').ker
        simpa only [projectiveCoordinateSwap, zero_mul, one_mul, zero_add,
          coordinateDeterminant, zero_sub] using
          integralSection_ker_comap_coordinateChange_inv 0 1 0 1 u v c d (-d) (-c)
            (by decide) hcd (by
              simpa only [zero_mul, one_mul, zero_add, coordinateDeterminant, zero_sub]
                using hcd')
      have hj : infinityChartEmbedding ℤ ≫ (projectiveCoordinateSwap ℤ).inv =
          standardChartEmbedding ℤ := by
        rw [infinityChartEmbedding, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← hj, Scheme.IdealSheafData.comap_comp, hswap]
      exact integralSection_infinityChart_ideal_top (-v) (-u) (-d) (-c) hcd'

/-- The actual product ideal cuts out the reduced union of the closures of
the original rational points. -/
theorem rationalSectionFamily_prod_eq_vanishingIdeal
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (∏ a ∈ A, (rationalSection a).ker) =
      Scheme.IdealSheafData.vanishingIdeal
        (A.sup fun a => TopologicalSpace.Closeds.closure
          ({rationalSectionGenericPoint a} : Set (ProjectiveLine ℤ))) := by
  classical
  rw [← rationalSectionFamily_inf_eq_prod]
  induction A using Finset.induction_on with
  | empty =>
    simp only [Finset.inf_empty, Finset.sup_empty, Scheme.IdealSheafData.vanishingIdeal_bot]
  | @insert a A ha ih =>
    rw [Finset.inf_insert, Finset.sup_insert,
      Scheme.IdealSheafData.vanishingIdeal_sup, ih,
      rationalSection_ker_eq_vanishingIdeal_closure]

/-- A finite product of distinct rational section ideals is radical. -/
theorem rationalSectionFamily_prod_isReduced
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (∏ a ∈ A, (rationalSection a).ker).IsReduced := by
  rw [rationalSectionFamily_prod_eq_vanishingIdeal,
    Scheme.IdealSheafData.IsReduced, ← Scheme.IdealSheafData.vanishingIdeal_support]
  exact Scheme.IdealSheafData.gc.u_l_u_eq_u _

/-- The sum of a finite family of rational sections is effective Cartier. -/
theorem rationalSectionFamily_prod_isEffectiveCartier
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (∏ a ∈ A, (rationalSection a).ker).IsEffectiveCartier :=
  Scheme.IdealSheafData.isEffectiveCartier_finset_prod A
    (fun a => (rationalSection a).ker) (fun a _ => rationalSection_ker_isEffectiveCartier a)

/-- The divisor `D_A` of §2: the sum of the actual integral rational sections. -/
def rationalSectionDivisor (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    Scheme.EffectiveCartierDivisor (ProjectiveLine ℤ) :=
  ⟨∏ a ∈ A, (rationalSection a).ker, rationalSectionFamily_prod_isEffectiveCartier A⟩

/-- The divisor `D_A` carries the reduced structure on the union of its sections. -/
theorem rationalSectionDivisor_isReduced
    (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (rationalSectionDivisor A).IsReduced :=
  rationalSectionFamily_prod_isReduced A

end ShimizuYamaguchi26BranchedCoverings
