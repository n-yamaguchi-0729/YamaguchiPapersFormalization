/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import AlgebraicCurves.Geometry.Schemes.exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite

/-!
# flat and finrank eq of is Finite of surjective of ring Krull Dim le one
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

theorem
  _root_.AlgebraicGeometry.flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y]
      [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdim : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] (d : ℕ)
    (hd : letI : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      Module.finrank Y.functionField (Y.functionField ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U)) = d) :
    ∃ (_ : LocallyOfFinitePresentation π), Flat π ∧ ∀ y : Y, π.finrank y = d := by
  classical
  obtain ⟨V, d', hflat, hlfp, hrank, hmem⟩ :=
    exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite π
      hY
  obtain rfl : V = ⊤ := top_le_iff.mp fun y _ => hmem y (hdim y)
  have := hflat
  have := hlfp
  have hι : IsIso (π ⁻¹ᵁ (⊤ : Y.Opens)).ι := by
    have : Epi (π ⁻¹ᵁ (⊤ : Y.Opens)).ι.base := (TopCat.epi_iff_surjective _).mpr fun x => ⟨⟨x,
      trivial⟩, rfl⟩
    exact IsOpenImmersion.isIso _
  have hcomp : (π ⁻¹ᵁ (⊤ : Y.Opens)).ι ≫ π = (π ∣_ ⊤) ≫ (⊤ : Y.Opens).ι := (morphismRestrict_ι π
    ⊤).symm
  have hFlatBC : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => Flat f) := Flat.isStableUnderBaseChange
  have : MorphismProperty.RespectsIso
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => Flat f) := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g e
    exact hFlatBC.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
  have hLfpBC : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => LocallyOfFinitePresentation f) :=
    locallyOfFinitePresentation_isStableUnderBaseChange
  have : MorphismProperty.RespectsIso
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => LocallyOfFinitePresentation f) := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g e
    exact hLfpBC.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
  have hflatπ : Flat π := by
    have h : Flat ((π ⁻¹ᵁ (⊤ : Y.Opens)).ι ≫ π) := by rw [hcomp]; infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => Flat f)
      (π ⁻¹ᵁ (⊤ : Y.Opens)).ι π).mp h
  have hlfpπ : LocallyOfFinitePresentation π := by
    have h : LocallyOfFinitePresentation ((π ⁻¹ᵁ (⊤ : Y.Opens)).ι ≫ π) :=
      by rw [hcomp]; infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => LocallyOfFinitePresentation f)
      (π ⁻¹ᵁ (⊤ : Y.Opens)).ι π).mp h
  have hrankπ : ∀ y : Y, π.finrank y = d' := fun y => by
    have := Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict π ⊤).flip ⟨y,
      trivial⟩
    rw [hrank] at this
    exact this.symm
  refine ⟨hlfpπ, hflatπ, fun y => ?_⟩
  rw [hrankπ]
  have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
  let alg : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := by
    have h := IsFinite.finite_app π U hU
    rw [Scheme.Hom.app_eq_appLE] at h
    exact h
  have : Module.Flat Γ(Y, U) Γ(X, π ⁻¹ᵁ U) :=
    HasRingHomProperty.appLE @Flat π hflatπ ⟨U, hU⟩ ⟨π ⁻¹ᵁ U, hV⟩ le_rfl
  have sq : IsPullback (Spec.map (π.appLE U (π ⁻¹ᵁ U) le_rfl)) hV.fromSpec hU.fromSpec π :=
    IsOpenImmersion.isPullback _ _ _ _ (IsAffineOpen.SpecMap_appLE_fromSpec π hU hV le_rfl).symm
      (by rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec])
  let 𝔭 : PrimeSpectrum Γ(Y, U) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 : π.finrank (hU.fromSpec.base 𝔭) = (Spec.map (π.appLE U (π ⁻¹ᵁ U) le_rfl)).finrank 𝔭 :=
    (Scheme.Hom.finrank_of_isPullback _ _ _ _ sq.flip 𝔭).symm
  have h2 : (Spec.map (π.appLE U (π ⁻¹ᵁ U) le_rfl)).finrank 𝔭 = Module.rankAtStalk (R := Γ(Y, U))
    Γ(X, π ⁻¹ᵁ U) 𝔭 :=
    Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, π ⁻¹ᵁ U) 𝔭
  have : Algebra.IsPushout Γ(Y, U) Γ(X, π ⁻¹ᵁ U) Y.functionField (Y.functionField ⊗[Γ(Y, U)] Γ(X, π
    ⁻¹ᵁ U)) :=
    Algebra.IsPushout.symm inferInstance
  have h3 : Module.rankAtStalk (R := Y.functionField) (Y.functionField ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U))
    ⟨⊥, Ideal.isPrime_bot⟩ =
      Module.rankAtStalk (R := Γ(Y, U)) Γ(X, π ⁻¹ᵁ U) 𝔭 := by
    rw [Algebra.rankAtStalk_eq_of_isPushout Γ(Y, U) Γ(X, π ⁻¹ᵁ U) Y.functionField
      (Y.functionField ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U))]
    congr 1
    ext1
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective Γ(Y, U) Y.functionField)
  have h4 : Module.rankAtStalk (R := Y.functionField) (Y.functionField ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U))
    ⟨⊥, Ideal.isPrime_bot⟩ = d := by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact hd
  have hd' : d' = d := by rw [← hrankπ (hU.fromSpec.base 𝔭), h1, h2, ← h3, h4]
  exact hd'
end flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
