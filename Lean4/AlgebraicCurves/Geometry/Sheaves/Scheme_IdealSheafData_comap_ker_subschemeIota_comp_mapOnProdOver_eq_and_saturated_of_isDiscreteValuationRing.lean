/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Ring
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv

/-!
# Scheme Ideal Sheaf Data comap ker subscheme Iota comp map On Prod Over eq and saturated of
is Discrete Valuation Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.SaturatedProductIdeal

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace LABody


open _root_.AlgebraicGeometry.Scheme


section DVR

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']

theorem isLocalizationAway_of_irreducible {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ T'
  where
  map_units := fun ⟨y, hy⟩ => by
    obtain ⟨n, rfl⟩ := hy
    exact IsUnit.mk0 _ (by
      rw [map_pow]
      exact pow_ne_zero _ (fun h => hϖ.ne_zero ((IsFractionRing.injective O T')
        (by rw [h, map_zero]))))
  surj := fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨⟨a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    have hb' : algebraMap O T' (↑u * ϖ ^ n) ≠ 0 := fun h =>
      hb0 ((IsFractionRing.injective O T') (by rw [h, map_zero]))
    change algebraMap O T' a / algebraMap O T' (↑u * ϖ ^ n) * algebraMap O T' (ϖ ^ n) =
      algebraMap O T' (a * ↑u⁻¹)
    rw [div_mul_eq_mul_div, div_eq_iff hb', ← map_mul, ← map_mul]
    congr 1
    rw [show a * ↑u⁻¹ * (↑u * ϖ ^ n) = a * (↑u⁻¹ * ↑u) * ϖ ^ n by ring, Units.inv_mul, mul_one]
  exists_of_eq := fun {a b} h => ⟨1, by rw [IsFractionRing.injective O T' h]⟩

theorem isOpenImmersion_specMap_algebraMap :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap O T'))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := isLocalizationAway_of_irreducible T' hϖ
  exact IsOpenImmersion.of_isLocalization ϖ

omit [IsDiscreteValuationRing O] in
theorem specMap_algebraMap_apply (x : Spec (CommRingCat.of T')) :
    (Spec.map (CommRingCat.ofHom (algebraMap O T'))).base x = (⊥ : PrimeSpectrum O) := by
  change PrimeSpectrum.comap (algebraMap O T') x = _
  ext1
  change Ideal.comap (algebraMap O T') x.asIdeal = ⊥
  have hx : x.asIdeal = ⊥ := by
    rcases (Ideal.eq_bot_or_top x.asIdeal) with h | h
    · exact h
    · exact absurd h x.2.ne_top
  rw [hx]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O T')

end DVR

end LABody
end AlgebraicCurves.Geometry.Sheaves.Proofs.SaturatedProductIdeal

namespace AlgebraicGeometry.Scheme.IdealSheafData

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.SaturatedProductIdeal
universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry


open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.SaturatedProductIdeal.LABody in
theorem comap_ker_subschemeIota_comp_mapOnProdOver_eq_and_saturated_of_isDiscreteValuationRing
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S}
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g : Spec (CommRingCat.of O)
      ⟶ S)
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    {gT : Spec (CommRingCat.of T') ⟶ S} (hψ : Spec.map (CommRingCat.ofHom (algebraMap O T')) ≫ g =
      gT)
    (I : (pullback f gT).IdealSheafData) :
    ((I.subschemeι ≫ mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ).ker).comap
        (mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T'))) hψ) = I ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ (U : (pullback f g).affineOpens) (s : Γ(pullback f g, U)),
        (pullback f g).presheaf.map (homOfLE (le_top : (U : (pullback f g).Opens) ≤ ⊤)).op
            ((pullback.snd f g).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) * s ∈
            (I.subschemeι ≫ mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T')))
              hψ).ker.ideal U →
          s ∈ (I.subschemeι ≫ mapOnProdOver f (Spec.map (CommRingCat.ofHom (algebraMap O T')))
            hψ).ker.ideal U := by
  classical
  let ψ : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom
    (algebraMap O T'))
  have hψo : IsOpenImmersion ψ := isOpenImmersion_specMap_algebraMap T'
  let X := pullback f g
  let q : X ⟶ Spec (CommRingCat.of O) := pullback.snd f g
  let gen : pullback f gT ⟶ X := mapOnProdOver f ψ hψ
  have Hgen : IsPullback gen (pullback.snd f gT) q ψ := isPullback_mapOnProdOver f ψ hψ
  have : IsOpenImmersion gen := MorphismProperty.of_isPullback Hgen.flip hψo
  have : QuasiCompact gen := MorphismProperty.of_isPullback Hgen.flip inferInstance
  let ι := I.subschemeι
  let h : I.subscheme ⟶ X := ι ≫ gen
  have : QuasiCompact h := inferInstance
  let J : X.IdealSheafData := h.ker
  have hJE : J.comap gen = I := by
    apply Scheme.IdealSheafData.ext
    funext W
    have L2 := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion J.subschemeι
      (pullback.fst gen J.subschemeι) (pullback.snd gen J.subschemeι) gen
        (IsPullback.of_hasPullback gen J.subschemeι) W
    have L1 := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion h
      (pullback.snd h gen) (pullback.fst h gen) gen (IsPullback.of_hasPullback h gen).flip W
    have hfst : pullback.fst h gen ≫ ι = pullback.snd h gen := by
      rw [← cancel_mono gen, Category.assoc]
      exact pullback.condition
    have : IsIso (pullback.fst h gen) := pullback_snd_iso_of_left_factors_mono ι gen
    have hk : (pullback.snd h gen).ker = I := by
      rw [← hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
    change (J.comap gen).ideal W = I.ideal W
    rw [← hk, L1]
    change ((pullback.fst gen J.subschemeι).ker).ideal W = _
    rw [L2, Scheme.IdealSheafData.ker_subschemeι]
  have hsat : ∀ (ϖ : O), Irreducible ϖ → ∀ (U : X.affineOpens) (s : Γ(X, U)),
      X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op (q.appTop ((Scheme.ΓSpecIso
        (CommRingCat.of O)).inv ϖ)) * s
        ∈ J.ideal U → s ∈ J.ideal U := by
    intro ϖ hϖ U s hs
    rw [Scheme.Hom.ker_apply] at hs ⊢
    rw [RingHom.mem_ker, map_mul] at hs
    rw [RingHom.mem_ker]
    have hunit : IsUnit ((h.app U).hom (X.presheaf.map (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op
        (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)))) := by
      have nat := congrArg (fun k => (CommRingCat.Hom.hom k) (q.appTop ((Scheme.ΓSpecIso
        (CommRingCat.of O)).inv ϖ)))
        (h.naturality (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at nat
      erw [nat]
      refine IsUnit.map _ ?_
      have hcomp : h.appTop (q.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) =
          (ι ≫ pullback.snd f gT).appTop (ψ.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) :=
            by
        have e1 : h ≫ q = (ι ≫ pullback.snd f gT) ≫ ψ := by
          simp only [h, gen, q, Category.assoc, mapOnProdOver_snd]
        have e2 := congrArg (fun k => (CommRingCat.Hom.hom k) ((Scheme.ΓSpecIso (CommRingCat.of
          O)).inv ϖ))
          (show q.appTop ≫ h.appTop = ψ.appTop ≫ (ι ≫ pullback.snd f gT).appTop by
            rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, e1])
        simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using e2
      change IsUnit ((CommRingCat.Hom.hom (Scheme.Hom.appTop h)) _)
      erw [hcomp]
      refine IsUnit.map _ ?_
      have hψϖ : ψ.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) =
          (Scheme.ΓSpecIso (CommRingCat.of T')).inv (algebraMap O T' ϖ) := by
        have e3 := congrArg (fun k => (CommRingCat.Hom.hom k) ϖ)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap O T')))
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          CommRingCat.hom_ofHom] at e3
        exact e3.symm
      erw [hψϖ]
      refine IsUnit.map _ ?_
      exact IsUnit.mk0 _ (fun h0 => hϖ.ne_zero ((IsFractionRing.injective O T')
        (by rw [h0, map_zero])))
    exact (hunit.mul_right_eq_zero).mp hs
  exact ⟨hJE, hsat⟩
end AlgebraicGeometry.Scheme.IdealSheafData
end ProofImplementation
