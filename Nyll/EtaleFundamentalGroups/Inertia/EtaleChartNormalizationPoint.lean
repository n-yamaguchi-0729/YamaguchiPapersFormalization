/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationBaseChange
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationStalkLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# A fixed normalization point on a localized etale chart

First pull the specified point into an etale chart, then to the chosen prime
localization of its stalk. The canonical normalization comparisons are actual
isomorphisms at both steps. The resulting point has exactly the original
fixing endomorphisms, simultaneously for all endomorphisms over the base.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

/-- An actual normalization point lifts through an etale chart and a prime
localization of its stalk, preserving the fixing condition for every deck map. -/
theorem exists_normalizationPoint_etaleChart_localizedStalk
    {X Y U T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (g : U ⟶ Y) [Etale g] (u : U) (P : Ideal (U.presheaf.stalk u)) [P.IsPrime]
    (z : T ⟶ f.normalization)
    (y : T ⟶ Spec (.of (Localization.AtPrime P)))
    (hzy : z ≫ f.fromNormalization =
      y ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P))) ≫ U.fromSpecStalk u ≫ g) :
    let h : Spec (.of (Localization.AtPrime P)) ⟶ U :=
      Spec.map (CommRingCat.ofHom
        (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P))) ≫ U.fromSpecStalk u
    ∃ q : T ⟶ (pullback.snd (pullback.snd f g) h).normalization,
      q ≫ (pullback.snd (pullback.snd f g) h).fromNormalization = y ∧
      ∀ (σ : X ⟶ X) (hσ : σ ≫ f = f),
        q ≫ normalizationEndomorphism (pullback.snd (pullback.snd f g) h)
          (pullbackEndomorphism (pullback.snd f g) h
            (pullbackEndomorphism f g σ hσ) (pullbackEndomorphism_snd f g σ hσ))
          (pullbackEndomorphism_snd (pullback.snd f g) h
            (pullbackEndomorphism f g σ hσ) (pullbackEndomorphism_snd f g σ hσ)) = q ↔
        z ≫ normalizationEndomorphism f σ hσ = z := by
  intro h
  have hc : IsIso ((pullback.snd f g).normalizationPullback h) :=
    isIso_normalizationPullback_fromSpecStalkLocalization (pullback.snd f g) u P
  have hzy₁ : z ≫ f.fromNormalization = (y ≫ h) ≫ g := by
    simpa only [h, Category.assoc] using hzy
  let z₁ : T ⟶ (pullback.snd f g).normalization :=
    pullback.lift z (y ≫ h) hzy₁ ≫ inv (f.normalizationPullback g)
  have hz₁ : z₁ ≫ (pullback.snd f g).fromNormalization = y ≫ h := by
    rw [← Scheme.Hom.normalizationPullback_snd f g]
    simp only [z₁, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  let q : T ⟶ (pullback.snd (pullback.snd f g) h).normalization :=
    pullback.lift z₁ y hz₁ ≫ inv ((pullback.snd f g).normalizationPullback h)
  refine ⟨q, ?_, ?_⟩
  · rw [← Scheme.Hom.normalizationPullback_snd (pullback.snd f g) h]
    simp only [q, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  · intro σ hσ
    exact (normalizationPullback_fixes_point_iff (pullback.snd f g) h z₁ y hz₁
      (pullbackEndomorphism f g σ hσ) (pullbackEndomorphism_snd f g σ hσ)).trans
        (normalizationPullback_fixes_point_iff f g z (y ≫ h) hzy₁ σ hσ)

end EtaleFundamentalGroups.Inertia
