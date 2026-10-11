/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationLocalization
import EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The canonical normalization pullback for an affine localization

The localization square of actual coordinate rings is a pushout. Its spectrum
identifies the affine localized source with the categorical pullback. The
corresponding source isomorphism extends to normalization, and uniqueness of
normalization shows that the already constructed localization comparison is
exactly the canonical normalizationPullback morphism. Hence that canonical
morphism is an isomorphism without any smoothness assumption.

There are nine data instances: four commutative rings and the five displayed
algebra edges. Every target has one owner; both compatible paths to `Bm` use
the same `Algebra R Bm`. The localization and tower instances are propositions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R B Rm Bm : Type u)
variable [CommRing R] [CommRing B] [CommRing Rm] [CommRing Bm]
variable [Algebra R B] [Algebra R Rm] [Algebra B Bm]
variable [Algebra Rm Bm] [Algebra R Bm]
variable [IsScalarTower R B Bm] [IsScalarTower R Rm Bm]
variable (M : Submonoid R) [IsLocalization M Rm]
variable [IsLocalization (Algebra.algebraMapSubmonoid B M) Bm]

include M Bm

/-- Normalization commutes with an arbitrary affine localization through its
actual canonical pullback comparison. -/
theorem isIso_normalizationPullback_of_affineLocalization :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R B))).normalizationPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R Rm)))) := by
  let f : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let g : Spec (.of Rm) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Rm))
  let fm : Spec (.of Bm) ⟶ Spec (.of Rm) := Spec.map (CommRingCat.ofHom (algebraMap Rm Bm))
  have hSource : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap B Bm))) fm f g := by
    have : Algebra.IsPushout R B Rm Bm :=
      Algebra.isPushout_of_isLocalization M Rm B Bm
    exact isPullback_SpecMap_of_isPushout
      (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap R Rm))
      (CommRingCat.ofHom (algebraMap B Bm))
      (CommRingCat.ofHom (algebraMap Rm Bm))
      (CommRingCat.isPushout_of_isPushout R B Rm Bm)
  let e : Spec (.of Bm) ≅ pullback f g := hSource.isoPullback
  have he : e.hom ≫ pullback.snd f g = fm := hSource.isoPullback_hom_snd
  have heFst : e.hom ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom (algebraMap B Bm)) := hSource.isoPullback_hom_fst
  let eN := normalizationSourceIso fm (pullback.snd f g) e he
  let a := affineNormalizationLocalizationIso R B Rm Bm M
  have haFst : a.hom ≫ pullback.fst f.fromNormalization g =
      affineNormalizationLocalizationMap R B Rm Bm :=
    affineNormalizationLocalizationIso_hom_fst R B Rm Bm M
  have haSnd : a.hom ≫ pullback.snd f.fromNormalization g = fm.fromNormalization :=
    affineNormalizationLocalizationIso_hom_snd R B Rm Bm M
  have hComparison : eN.hom ≫ f.normalizationPullback g = a.hom := by
    refine Scheme.Hom.normalization.hom_ext fm _ _
      (pullback.snd f.fromNormalization g) ?_ ?_ ?_
    · apply pullback.hom_ext
      · simp only [Category.assoc, eN,
          toNormalization_normalizationSourceIso_hom_assoc,
          Scheme.Hom.toNormalization_normalizationPullback_fst,
          haFst]
        rw [← Category.assoc, heFst]
        exact (toNormalization_affineNormalizationLocalizationMap R B Rm Bm).symm
      · simp only [Category.assoc, Scheme.Hom.normalizationPullback_snd,
          eN, normalizationSourceIso_hom_fromNormalization,
          haSnd]
    · simp only [Category.assoc, Scheme.Hom.normalizationPullback_snd,
        eN, normalizationSourceIso_hom_fromNormalization]
    · exact haSnd
  have hMap : f.normalizationPullback g = eN.inv ≫ a.hom := by
    rw [← hComparison, ← Category.assoc, eN.inv_hom_id, Category.id_comp]
  change IsIso (f.normalizationPullback g)
  rw [hMap]
  infer_instance

end EtaleFundamentalGroups.Inertia
