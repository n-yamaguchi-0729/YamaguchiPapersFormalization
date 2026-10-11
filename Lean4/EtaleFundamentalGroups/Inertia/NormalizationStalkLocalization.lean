/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationAffineBaseLocalization
import SchemeTheory.Affine.StalkLocalization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Relative normalization over localized stalks

The actual map from a localized stalk factors through an affine neighbourhood.
Its section map is a localization, using the germ map and the standard
localization-at-prime construction. The normalization comparison therefore is
an isomorphism for any qcqs source, without assuming the source is affine.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem fromSpec_appLE_self
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  have heq : (eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h).op =
      𝟙 (Opposite.op (⊤ : (Spec Γ(X, U)).Opens)) := Subsingleton.elim _ _
  rw [heq, CategoryTheory.Functor.map_id, Category.comp_id]

/-- A localization of the coordinate ring of an affine neighbourhood commutes
with normalization through the actual comparison map. -/
theorem isIso_normalizationPullback_fromAffineLocalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U)
    (S : CommRingCat.{u}) [Algebra Γ(Y, U) S]
    (M : Submonoid Γ(Y, U)) [IsLocalization M S] :
    IsIso (f.normalizationPullback
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) S)) ≫ hU.fromSpec)) := by
  let a : Γ(Y, U) ⟶ S := CommRingCat.ofHom (algebraMap Γ(Y, U) S)
  let l : Spec S ⟶ Spec Γ(Y, U) := Spec.map a
  let g : Spec S ⟶ Y := l ≫ hU.fromSpec
  have hlFlat : Flat l := by
    apply Flat.of_stalkMap
    intro x
    have : IsIso (l.stalkMap x) := isIso_stalkMap_SpecMap_of_isLocalization M x
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (l.stalkMap x))
  have hgFlat : Flat g := inferInstance
  have hTU : (⊤ : (Spec S).Opens) ≤ g ⁻¹ᵁ U := by
    dsimp only [g]
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self, Scheme.Hom.preimage_top]
  have hR : (⊤ : (Spec Γ(Y, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
  have hMap : g.appLE U ⊤ hTU = a ≫ (Scheme.ΓSpecIso S).inv := by
    calc
      g.appLE U ⊤ hTU =
          hU.fromSpec.appLE U ⊤ hR ≫ l.appLE ⊤ ⊤ le_top :=
        (Scheme.Hom.appLE_comp_appLE l hU.fromSpec U ⊤ ⊤ hR le_top).symm
      _ = (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ l.appTop := by
        rw [fromSpec_appLE_self hU hR]
        exact congrArg (fun k => (Scheme.ΓSpecIso Γ(Y, U)).inv ≫ k)
          l.app_eq_appLE.symm
      _ = a ≫ (Scheme.ΓSpecIso S).inv := (Scheme.ΓSpecIso_inv_naturality a).symm
  let : Algebra Γ(Y, U) Γ(Spec S, ⊤) := (g.appLE U ⊤ hTU).hom.toAlgebra
  let e : Γ(Spec S, ⊤) ≃ₐ[Γ(Y, U)] S :=
    { toRingEquiv := (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv
      commutes' := by
        intro r
        have hcomp : g.appLE U ⊤ hTU ≫ (Scheme.ΓSpecIso S).hom = a := by
          rw [hMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
        exact ConcreteCategory.congr_hom hcomp r }
  have hLoc : IsLocalization M Γ(Spec S, ⊤) :=
    (IsLocalization.isLocalization_iff_of_algEquiv M e).mpr inferInstance
  exact isIso_normalizationPullback_of_affineLocalizationSections f g hU hTU M hLoc

/-- Relative normalization commutes with the actual map from the spectrum of
any stalk, independently of an affine-neighbourhood choice. -/
theorem isIso_normalizationPullback_fromSpecStalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (y : Y) : IsIso (f.normalizationPullback (Y.fromSpecStalk y)) := by
  let U := (Y.affineCover.f (Y.affineCover.idx y)).opensRange
  let hU : IsAffineOpen U := isAffineOpen_opensRange _
  let hy : y ∈ U := Y.affineCover.covers y
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ U y hy).hom.toAlgebra
  have hLoc : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hy]
  exact isIso_normalizationPullback_fromAffineLocalization f hU
    (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl

/-- Relative normalization commutes with the canonical map from any prime
localization of a stalk. All localization and flatness data are constructed. -/
theorem isIso_normalizationPullback_fromSpecStalkLocalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (y : Y) (P : Ideal (Y.presheaf.stalk y)) [P.IsPrime] :
    IsIso (f.normalizationPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y)
        (Localization.AtPrime P))) ≫ Y.fromSpecStalk y)) := by
  let U := (Y.affineCover.f (Y.affineCover.idx y)).opensRange
  let hU : IsAffineOpen U := isAffineOpen_opensRange _
  let hy : y ∈ U := Y.affineCover.covers y
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ U y hy).hom.toAlgebra
  let : Algebra Γ(Y, U) (Localization.AtPrime P) :=
    ((algebraMap (Y.presheaf.stalk y) (Localization.AtPrime P)).comp
      (Y.presheaf.germ U y hy).hom).toAlgebra
  have : @IsScalarTower Γ(Y, U) (Y.presheaf.stalk y) (Localization.AtPrime P)
      (@Algebra.toSMul Γ(Y, U) (Y.presheaf.stalk y) _ _ inferInstance)
      (@Algebra.toSMul (Y.presheaf.stalk y) (Localization.AtPrime P) _ _ inferInstance)
      (@Algebra.toSMul Γ(Y, U) (Localization.AtPrime P) _ _ inferInstance) :=
    IsScalarTower.of_algebraMap_eq' (R := Γ(Y, U)) (S := Y.presheaf.stalk y)
      (A := Localization.AtPrime P) rfl
  have hA : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  have hLoc : IsLocalization.AtPrime (Localization.AtPrime P)
      (P.comap (algebraMap Γ(Y, U) (Y.presheaf.stalk y))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Localization.AtPrime P) P
  have hMap : Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y, U) (Localization.AtPrime P))) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y)
        (Localization.AtPrime P))) ≫ Y.fromSpecStalk y := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hy, IsAffineOpen.fromSpecStalk,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  rw [← hMap]
  exact isIso_normalizationPullback_fromAffineLocalization f hU
    (CommRingCat.of (Localization.AtPrime P))
    (P.comap (algebraMap Γ(Y, U) (Y.presheaf.stalk y))).primeCompl

end EtaleFundamentalGroups.Inertia
