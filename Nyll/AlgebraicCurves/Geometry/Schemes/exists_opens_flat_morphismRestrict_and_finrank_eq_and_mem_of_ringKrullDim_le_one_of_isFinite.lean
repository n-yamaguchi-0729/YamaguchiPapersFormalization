/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Restrict
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Module_exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one

/-!
# exists opens flat morphism Restrict and finrank eq and mem of ring Krull Dim le one of is
Finite
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.FiniteFlatOpenLocus

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace FlatCodimOne
open _root_.AlgebraicGeometry

open TopologicalSpace

attribute [local instance] RingHomInvPair.of_ringEquiv in
theorem free_of_isLocalizedModule {R : Type*} [CommRing R] (S : Submonoid R)
    {M : Type*} [AddCommGroup M] [Module R M]
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free Rₛ Mₛ := by
  set e := (IsLocalization.algEquiv S (Localization S) Rₛ).toRingEquiv
  have key : Module.Free (Localization S) (LocalizedModule S M) ↔ Module.Free Rₛ Mₛ := by
    apply Module.Free.iff_of_equiv (σ := e)
    refine { __ := IsLocalizedModule.iso S f, map_smul' := ?_ }
    intro r x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S r
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
    simp only [e, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      Module.algebraMap_end_apply,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, IsLocalization.algEquiv_apply,
      IsLocalization.map_id_mk']
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]
  exact key.mp ‹_›

theorem flat_away_map {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] (r : A) [Algebra A A'] [IsLocalization.Away r A'] [Algebra B B']
    [IsLocalization.Away (algebraMap A B r) B']
    (hfree : Module.Free (Localization.Away r) (LocalizedModule (Submonoid.powers r) B)) :
    (IsLocalization.Away.map A' B' (algebraMap A B) r).Flat := by
  let alg : Algebra A' B' := (IsLocalization.Away.map A' B' (algebraMap A B) r).toAlgebra
  let algAB' : Algebra A B' := ((algebraMap B B').comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap B B' (algebraMap A B a) = IsLocalization.Away.map A' B' (algebraMap A B) r
      (algebraMap A A' a)
    rw [IsLocalization.Away.map, IsLocalization.map_eq])
  have hS : Algebra.algebraMapSubmonoid B (Submonoid.powers r) = Submonoid.powers (algebraMap A B
    r) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  have : IsLocalizedModule (Submonoid.powers r) (IsScalarTower.toAlgHom A B B').toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, hS]; infer_instance
  have : Module.Free (Localization (Submonoid.powers r)) (LocalizedModule (Submonoid.powers r) B)
    := hfree
  have : Module.Free A' B' :=
    free_of_isLocalizedModule (Submonoid.powers r) A' (IsScalarTower.toAlgHom A B B').toLinearMap
  change Module.Flat A' B'
  infer_instance

end AlgebraicGeometry.FlatCodimOne
end AlgebraicCurves.Geometry.Schemes.Proofs.FiniteFlatOpenLocus

namespace AlgebraicGeometry

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs.FiniteFlatOpenLocus
universe u
open _root_.CategoryTheory
open _root_.AlgebraicGeometry


open
  _root_.AlgebraicCurves.Geometry.Schemes.Proofs.FiniteFlatOpenLocus.AlgebraicGeometry.FlatCodimOne
  _root_.TopologicalSpace in
theorem exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y]
      [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∃ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) ∧ LocallyOfFinitePresentation (π ∣_ V) ∧
      (∀ y : V, (π ∣_ V).finrank y = d) ∧
      ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 → y ∈ V := by
  classical
  have key : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 → ∃ W : Y.Opens, Flat (π ∣_ W) ∧ y ∈ W
    := by
    intro y hy
    obtain ⟨U, hU, hyU, -⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y))
      (show y ∈ (⊤ : Y.Opens) from trivial)
    have hπU : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
    have : Nonempty U := ⟨⟨y, hyU⟩⟩
    obtain ⟨x, hx⟩ := π.surjective y
    have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨x, show π x ∈ U by rw [hx]; exact hyU⟩⟩
    have : IsDomain Γ(X, π ⁻¹ᵁ U) := IsIntegral.component_integral (π ⁻¹ᵁ U)
    let algAB : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : Module.Finite Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := IsFinite.finite_app π U hU
    have hinj : Function.Injective (algebraMap Γ(Y, U) Γ(X, π ⁻¹ᵁ U)) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      have h1 : π ⁻¹ᵁ (Y.basicOpen a) = ⊥ := by
        rw [Scheme.preimage_basicOpen]
        exact (basicOpen_eq_bot_iff _).mpr ha
      have h2 : Y.basicOpen a = ⊥ := by
        refine eq_bot_iff.mpr fun z hz => ?_
        obtain ⟨w, rfl⟩ := π.surjective z
        have hw : w ∈ π ⁻¹ᵁ (Y.basicOpen a) := hz
        rw [h1] at hw
        exact hw.elim
      exact (basicOpen_eq_bot_iff a).mp h2
    have : NoZeroSMulDivisors Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := ⟨fun {c b} h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun hc => (injective_iff_map_eq_zero _).mp hinj c hc⟩
    set 𝔭 := hU.primeIdealOf ⟨y, hyU⟩ with h𝔭
    let := Y.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
    have hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) 𝔭.asIdeal := hU.isLocalization_stalk
      ⟨y, hyU⟩
    let e : Y.presheaf.stalk y ≃ₐ[Γ(Y, U)] Localization.AtPrime 𝔭.asIdeal :=
      IsLocalization.algEquiv 𝔭.asIdeal.primeCompl _ _
    have hic : IsIntegrallyClosed (Localization.AtPrime 𝔭.asIdeal) := by
      have := hY y; exact IsIntegrallyClosed.of_equiv e.toRingEquiv
    have hdim : ringKrullDim (Localization.AtPrime 𝔭.asIdeal) ≤ 1 := by
      rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]; exact hy
    obtain ⟨r, hr, hfree⟩ :=
      Module.exists_notMem_and_free_localizedModule_of_isIntegrallyClosed_of_ringKrullDim_le_one
        Γ(Y, U) 𝔭.asIdeal hic hdim Γ(X, π ⁻¹ᵁ U)
    refine ⟨Y.basicOpen r, ?_, ?_⟩
    · have : IsAffine (Y.basicOpen r) := hU.basicOpen r
      have : IsAffine (π ⁻¹ᵁ Y.basicOpen r) := (hU.basicOpen r).preimage π
      have hQ : ∀ W : Y.Opens, W = Y.basicOpen r → (π.app W).hom.Flat := by
        rintro W rfl
        have := hU.isLocalization_basicOpen r
        have := hπU.isLocalization_basicOpen (π.app U r)
        refine (RingHom.Flat.respectsIso.arrow_mk_iso_iff (hU.appBasicOpenIsoAwayMap π hπU r)).mpr
          ?_
        simp only [CommRingCat.hom_ofHom]
        exact flat_away_map r hfree
      rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), morphismRestrict_appTop]
      refine (RingHom.RespectsIso.cancel_right_isIso RingHom.Flat.respectsIso _ _).mpr ?_
      exact hQ _ (Scheme.Opens.ι_image_top _)
    · rw [Scheme.mem_basicOpen (hx := hyU)]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) 𝔭.asIdeal r).mpr
        (Ideal.mem_primeCompl_iff.mpr hr)
  let V : Y.Opens := sSup {W : Y.Opens | Flat (π ∣_ W)}
  have hVflat : Flat (π ∣_ V) := by
    refine Flat.of_stalkMap _ fun x => ?_
    obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp (show π x.1 ∈ V from x.2)
    have : Flat (π ∣_ W) := hW
    have h1 := Flat.stalkMap (π ∣_ W) ⟨x.1, hxW⟩
    have h2 : (π.stalkMap x.1).hom.Flat :=
      (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap π W ⟨x.1, hxW⟩)).mp h1
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap π V x)).mpr h2
  have hVlfp : LocallyOfFinitePresentation (π ∣_ V) := inferInstance
  have hmem : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 → y ∈ V := fun y hy => by
    obtain ⟨W, hW, hyW⟩ := key y hy
    exact Opens.mem_sSup.mpr ⟨W, hW, hyW⟩
  have hlc := Scheme.Hom.isLocallyConstant_finrank (π ∣_ V)
  by_cases hne : Nonempty V
  · have : IsIntegral (V : Scheme.{u}) := isIntegral_of_isOpenImmersion V.ι
    obtain ⟨d, hd⟩ := hlc.exists_eq_const
    exact ⟨V, d, hVflat, hVlfp, fun y => congrFun hd y, hmem⟩
  · exact ⟨V, 0, hVflat, hVlfp, fun y => (hne ⟨y⟩).elim, hmem⟩
end AlgebraicGeometry
end ProofImplementation
