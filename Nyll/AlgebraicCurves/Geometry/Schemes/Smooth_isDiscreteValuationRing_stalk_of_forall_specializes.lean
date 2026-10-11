/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing

/-!
# Smooth is Discrete Valuation Ring stalk of forall specializes
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
universe u
open CategoryTheory AlgebraicGeometry Topology

theorem _root_.AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ _ : IsDomain (T.presheaf.stalk η), IsDiscreteValuationRing (T.presheaf.stalk η) := by
  classical
  obtain ⟨hdom, hic⟩ :=
    AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R t η
  refine ⟨hdom, ?_⟩
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let g : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk (t.base η) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (t.base η)
      trivial
  let φ : CommRingCat.of R ⟶ T.presheaf.stalk η := g ≫ t.stalkMap η
  have hfac : T.fromSpecStalk η ≫ t = Spec.map φ := by
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk t, Spec.fromSpecStalk_eq]
  have hbase : ∀ 𝔮 : PrimeSpectrum (T.presheaf.stalk η),
      t.base ((T.fromSpecStalk η).base 𝔮) = (Spec.map φ).base 𝔮 := fun 𝔮 => by
    rw [← hfac]; rfl
  have hcomap : ∀ 𝔮 : PrimeSpectrum (T.presheaf.stalk η),
      ((Spec.map φ).base 𝔮).asIdeal = 𝔮.asIdeal.comap φ.hom := fun _ => rfl
  have key : ∀ 𝔮 : PrimeSpectrum (T.presheaf.stalk η), φ.hom ϖ ∈ 𝔮.asIdeal →
      𝔮 = IsLocalRing.closedPoint (T.presheaf.stalk η) := by
    intro 𝔮 hϖ𝔮
    have hy : t.base ((T.fromSpecStalk η).base 𝔮) = IsLocalRing.closedPoint R := by
      rw [hbase]
      apply PrimeSpectrum.ext
      change ((Spec.map φ).base 𝔮).asIdeal = IsLocalRing.maximalIdeal R
      rw [hcomap]
      have hne : 𝔮.asIdeal.comap φ.hom ≠ ⊥ := by
        intro h
        have hmem : ϖ ∈ 𝔮.asIdeal.comap φ.hom := hϖ𝔮
        rw [h] at hmem
        exact hϖ.ne_zero (Ideal.mem_bot.mp hmem)
      exact IsLocalRing.eq_maximalIdeal
        (Ring.DimensionLEOne.maximalOfPrime hne (Ideal.comap_isPrime φ.hom 𝔮.asIdeal))
    have hyη : (T.fromSpecStalk η).base 𝔮 ⤳ η := by
      have hmem : (T.fromSpecStalk η).base 𝔮 ∈ Set.range (T.fromSpecStalk η).base := ⟨𝔮, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hmem
    have heq := hgen _ hyη hy
    apply (T.fromSpecStalk η).isEmbedding.injective
    rw [heq, Scheme.fromSpecStalk_closedPoint]
  have hϖm : φ.hom ϖ ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk η) := by
    have h1 : ((Spec.map φ).base (IsLocalRing.closedPoint _)).asIdeal = IsLocalRing.maximalIdeal R
      := by
      rw [← hbase, Scheme.fromSpecStalk_closedPoint, hηs]; rfl
    have h2 : ϖ ∈ (IsLocalRing.maximalIdeal (T.presheaf.stalk η)).comap φ.hom := by
      change ϖ ∈ (IsLocalRing.closedPoint (T.presheaf.stalk η)).asIdeal.comap φ.hom
      rw [← hcomap, h1]
      exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact h2
  have hgreg : IsSMulRegular ((Spec (CommRingCat.of R)).presheaf.stalk (t.base η)) (g.hom ϖ) := by
    let : Algebra Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (t.base
      η)) :=
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (t.base η) trivial).hom.toAlgebra
    have := (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_stalk ⟨t.base η, trivial⟩
    have : IsDomain Γ(Spec (CommRingCat.of R), ⊤) :=
      Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
    have hle := ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
      ⟨t.base η, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
    have : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk (t.base η)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
    have hne : g.hom ϖ ≠ 0 := by
      intro h0
      have hinj := IsLocalization.injective ((Spec (CommRingCat.of R)).presheaf.stalk (t.base η))
        hle
      have h0' : algebraMap Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk
        (t.base η))
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)
          = algebraMap Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk
            (t.base η)) 0 := by
        rw [map_zero]; exact h0
      have := hinj h0'
      exact hϖ.ne_zero ((Scheme.ΓSpecIso (CommRingCat.of
        R)).symm.commRingCatIsoToRingEquiv.injective
        (by rw [map_zero]; exact this))
    exact (IsRegular.of_ne_zero hne).left.isSMulRegular
  have hflat : (t.stalkMap η).hom.Flat := Flat.stalkMap t η
  have hreg : IsSMulRegular (T.presheaf.stalk η) (φ.hom ϖ) := by
    let := (t.stalkMap η).hom.toAlgebra
    have : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (t.base η)) (T.presheaf.stalk η)
      := hflat
    exact hgreg.of_flat
  have hne0 : φ.hom ϖ ≠ 0 := by
    intro h0
    have h1 : φ.hom ϖ * 1 = φ.hom ϖ * 0 := by rw [h0, zero_mul, zero_mul]
    exact one_ne_zero (hreg h1)
  have hht : (IsLocalRing.maximalIdeal (T.presheaf.stalk η)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {φ.hom ϖ}) _
      ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hϖm⟩, fun q hq _ =>
        (congrArg PrimeSpectrum.asIdeal
          (key ⟨q, hq.1⟩ ((Ideal.span_singleton_le_iff_mem _).mp hq.2))).ge⟩
  have hdim : ringKrullDim (T.presheaf.stalk η) ≤ 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hht
  have : Ring.KrullDimLE 1 (T.presheaf.stalk η) := Ring.krullDimLE_iff.mpr hdim
  have hm0 : IsLocalRing.maximalIdeal (T.presheaf.stalk η) ≠ ⊥ := by
    intro h
    have hmem := hϖm
    rw [h] at hmem
    exact hne0 (Ideal.mem_bot.mp hmem)
  have hnf : ¬ IsField (T.presheaf.stalk η) := fun hf =>
    hm0 (IsLocalRing.isField_iff_maximalIdeal_eq.mp hf)
  have h03 : IsDiscreteValuationRing (T.presheaf.stalk η) ↔
      IsIntegrallyClosed (T.presheaf.stalk η) ∧
        ∃! P : Ideal (T.presheaf.stalk η), P ≠ ⊥ ∧ P.IsPrime :=
    (IsDiscreteValuationRing.TFAE (T.presheaf.stalk η) hnf).out 1 4
  refine h03.mpr ⟨hic, ?_⟩
  refine ⟨IsLocalRing.maximalIdeal _, ⟨hm0, inferInstance⟩, ?_⟩
  rintro P ⟨hP0, hPp⟩
  have hnotmin : P ∉ minimalPrimes (T.presheaf.stalk η) := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]; exact hP0
  exact IsLocalRing.eq_maximalIdeal
    (((Ring.krullDimLE_one_iff.mp inferInstance) P hPp).resolve_left hnotmin)
end Smooth_isDiscreteValuationRing_stalk_of_forall_specializes
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
