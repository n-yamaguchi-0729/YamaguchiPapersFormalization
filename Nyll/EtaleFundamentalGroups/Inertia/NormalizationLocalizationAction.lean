/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationLocalization
import Nyll.EtaleFundamentalGroups.Inertia.AffineNormalizationGeometricPoint
import Mathlib.RingTheory.Localization.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Geometric-point stabilizers under arbitrary affine localization

The algebra automorphism on the localized cover is constructed from the
original automorphism by the localization universal property. The cartesian
normalization square then lifts each compatible geometric point, preserving
its exact stabilizer. No smoothness or finite-presentation condition is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

section LocalizationAutomorphism

variable (R B Bm : Type u) [CommRing R] [CommRing B] [CommRing Bm]
variable [Algebra R B] [Algebra B Bm] [Algebra R Bm] [IsScalarTower R B Bm]
variable (M : Submonoid R) [IsLocalization (Algebra.algebraMapSubmonoid B M) Bm]

/-- An algebra automorphism fixes the multiplicative set coming from the base. -/
theorem algebraMapSubmonoid_map_algEquiv (sigma : B ≃ₐ[R] B) :
    (Algebra.algebraMapSubmonoid B M).map sigma.toMonoidHom =
      Algebra.algebraMapSubmonoid B M := by
  ext b
  constructor
  · rintro ⟨a, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (sigma.commutes r).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨algebraMap R B r, ⟨r, hr, rfl⟩, sigma.commutes r⟩

/-- Extend the actual cover automorphism to the localization. -/
def localizationBaseAlgEquiv (sigma : B ≃ₐ[R] B) : Bm ≃ₐ[R] Bm :=
  IsLocalization.algEquivOfAlgEquiv Bm Bm sigma
    (algebraMapSubmonoid_map_algEquiv R B M sigma)

theorem localizationBaseAlgEquiv_algebraMap
    (sigma : B ≃ₐ[R] B) (b : B) :
    localizationBaseAlgEquiv R B Bm M sigma (algebraMap B Bm b) =
      algebraMap B Bm (sigma b) :=
  IsLocalization.algEquivOfAlgEquiv_eq
    (algebraMapSubmonoid_map_algEquiv R B M sigma) b

end LocalizationAutomorphism

-- Nine data instances describe the two compatible algebra squares. Each
-- ring and each algebra target occurs once; both tower witnesses are Props.
variable (R B Rm Bm : Type u)
variable [CommRing R] [CommRing B] [CommRing Rm] [CommRing Bm]
variable [Algebra R B] [Algebra R Rm] [Algebra B Bm]
variable [Algebra Rm Bm] [Algebra R Bm]
variable [IsScalarTower R B Bm] [IsScalarTower R Rm Bm]
variable (M : Submonoid R) [IsLocalization M Rm]
variable [IsLocalization (Algebra.algebraMapSubmonoid B M) Bm]

/-- The extended automorphism is linear over the localized base as well. -/
def localizationAlgEquiv (sigma : B ≃ₐ[R] B) : Bm ≃ₐ[Rm] Bm :=
  (localizationBaseAlgEquiv R B Bm M sigma).extendScalarsOfIsLocalization Rm M

/-- The actual affine normalization map intertwines the extended deck maps. -/
@[reassoc]
theorem affineNormalizationLocalizationMap_deck (sigma : B ≃ₐ[R] B) :
    affineNormalizationDeck Rm Bm (localizationAlgEquiv R B Rm Bm M sigma) ≫
        affineNormalizationLocalizationMap R B Rm Bm =
      affineNormalizationLocalizationMap R B Rm Bm ≫
        affineNormalizationDeck R B sigma := by
  apply (cancel_mono (specNormalizationIso R B).hom).mp
  simp only [affineNormalizationLocalizationMap, Category.assoc,
    Iso.inv_hom_id, Category.comp_id,
    affineNormalizationDeck_specNormalizationIso_hom,
    affineNormalizationDeck_specNormalizationIso_hom_assoc,
    Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  apply Subtype.ext
  exact localizationBaseAlgEquiv_algebraMap R B Bm M sigma (b : B)

/-- A compatible point lifts through the actual normalization localization
square, and the lift is fixed precisely by the original fixing automorphisms. -/
theorem exists_affineNormalizationLocalizationPoint_fixes_iff
    {T : Scheme.{u}}
    (z : T ⟶ (Spec.map (CommRingCat.ofHom (algebraMap R B))).normalization)
    (y : T ⟶ Spec (.of Rm))
    (hzy : z ≫ (Spec.map (CommRingCat.ofHom (algebraMap R B))).fromNormalization =
      y ≫ Spec.map (CommRingCat.ofHom (algebraMap R Rm))) :
    ∃ q : T ⟶ (Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))).normalization,
      q ≫ affineNormalizationLocalizationMap R B Rm Bm = z ∧
      q ≫ (Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))).fromNormalization = y ∧
      ∀ sigma : B ≃ₐ[R] B,
        q ≫ affineNormalizationDeck Rm Bm
            (localizationAlgEquiv R B Rm Bm M sigma) = q ↔
          z ≫ affineNormalizationDeck R B sigma = z := by
  let h := affineNormalizationLocalization_isPullback R B Rm Bm M
  let q := h.lift z y hzy
  have hq : q ≫ affineNormalizationLocalizationMap R B Rm Bm = z :=
    h.lift_fst z y hzy
  have hqy :
      q ≫ (Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))).fromNormalization = y :=
    h.lift_snd z y hzy
  refine ⟨q, hq, hqy, fun sigma => ?_⟩
  constructor
  · intro hfix
    calc
      z ≫ affineNormalizationDeck R B sigma =
          (q ≫ affineNormalizationLocalizationMap R B Rm Bm) ≫
            affineNormalizationDeck R B sigma := by rw [hq]
      _ = (q ≫ affineNormalizationDeck Rm Bm
          (localizationAlgEquiv R B Rm Bm M sigma)) ≫
            affineNormalizationLocalizationMap R B Rm Bm := by
        simpa only [Category.assoc] using
          congrArg (fun k => q ≫ k)
            (affineNormalizationLocalizationMap_deck R B Rm Bm M sigma).symm
      _ = z := by rw [hfix, hq]
  · intro hfix
    apply h.hom_ext
    · rw [Category.assoc, affineNormalizationLocalizationMap_deck,
        ← Category.assoc, hq, hfix]
    · rw [Category.assoc, affineNormalizationDeck,
        Scheme.Hom.normalizationDesc_comp]

end EtaleFundamentalGroups.Inertia
