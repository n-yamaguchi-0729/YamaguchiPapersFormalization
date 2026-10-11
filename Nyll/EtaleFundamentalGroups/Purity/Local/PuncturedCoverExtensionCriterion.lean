/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.DepthTwoSections
import Nyll.SchemeTheory.FiniteEtale.AffinizationExtension
import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Finite étale extension detected by global sections

For a Noetherian local ring of depth at least two, a finite étale cover of
the punctured spectrum extends precisely when its actual global-sections
algebra is finite étale over the base ring.

This proves Stacks Project, Lemma 58.20.2 (tag `0BLK`).
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

/-- A punctured finite étale cover extends if and only if its actual
global-sections algebra is finite étale. -/
theorem exists_punctured_finiteEtale_extension_iff_sections_finiteEtale
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdepth : (2 : ℕ∞) ≤ Module.depth R R)
    {Y : Scheme.{u}} (f : Y ⟶ Scheme.puncturedSpectrum R) [IsFiniteEtale f] :
    (∃ V : FiniteEtale (Spec (.of R)),
      Nonempty ((FiniteEtale.pullback (Scheme.puncturedSpectrumInclusion R)).obj V ≅
        FiniteEtale.mk f)) ↔
    ((Scheme.ΓSpecIso (.of R)).inv ≫
      (f ≫ Scheme.puncturedSpectrumInclusion R).appTop).hom.FiniteEtale := by
  let U := Scheme.puncturedSpectrumOpen R
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  constructor
  · rintro ⟨V, ⟨e⟩⟩
    let p : V.left ⟶ Spec (.of R) := V.hom
    let : IsFiniteEtale p := V.prop
    let : IsAffine V.left := isAffine_of_isAffineHom p
    let eY : pullback p U.ι ≅ Y :=
      ((FiniteEtale.forget (U : Scheme.{u})) ⋙ Over.forget (U : Scheme.{u})).mapIso e
    let j : Y ⟶ V.left := eY.inv ≫ pullback.fst p U.ι
    have hj : j ≫ p = f ≫ U.ι := by
      dsimp only [j]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun g => g ≫ U.ι) e.inv.hom.w
    have heOpen : (pullbackRestrictIsoRestrict p U).hom ≫ (p ⁻¹ᵁ U).ι =
        pullback.fst p U.ι := pullbackRestrictIsoRestrict_hom_ι p U
    let : IsIso (p ⁻¹ᵁ U).ι.appTop :=
      isIso_punctured_finiteFlat_inclusion_appTop_of_two_le_depth R hdepth p
    let : IsIso (pullback.fst p U.ι).appTop := by
      rw [← heOpen, Scheme.Hom.comp_appTop]
      exact IsIso.comp_isIso' inferInstance
        (Scheme.Γ.map_isIso (pullbackRestrictIsoRestrict p U).hom.op)
    let : IsIso j.appTop := by
      dsimp only [j]
      rw [Scheme.Hom.comp_appTop]
      exact IsIso.comp_isIso' inferInstance (Scheme.Γ.map_isIso eY.inv.op)
    have hpΓ : p.appTop.hom.FiniteEtale :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsFiniteEtale)
        (Q := affineAnd RingHom.FiniteEtale) (f := p)).mp inferInstance).2
    let : IsFiniteEtale (Spec.map p.appTop) := IsFiniteEtale.SpecMap_iff.mpr hpΓ
    let : IsFiniteEtale (Spec.map j.appTop) := ⟨⟩
    let : IsFiniteEtale (Spec.map (Scheme.ΓSpecIso (.of R)).inv) := ⟨⟩
    apply IsFiniteEtale.SpecMap_iff.mp
    change IsFiniteEtale (Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ (f ≫ U.ι).appTop))
    rw [← hj, Scheme.Hom.comp_appTop, Spec.map_comp, Spec.map_comp]
    infer_instance
  · intro h
    let : NoetherianSpace (U : Scheme.{u}) :=
      U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let : CompactSpace (U : Scheme.{u}) := inferInstance
    let : (U : Scheme.{u}).IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.ι
    let : Y.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom f
    let : IsFiniteEtale
        (Spec.map (((Scheme.ΓSpecIso (.of R)).inv) ≫ (f ≫ U.ι).appTop)) :=
      IsFiniteEtale.SpecMap_iff.mpr h
    let : IsFiniteEtale
        (Spec.map (f ≫ U.ι).appTop ≫ Spec.map (Scheme.ΓSpecIso (.of R)).inv) := by
      rw [← Spec.map_comp]
      infer_instance
    have hp : IsFiniteEtale (Spec.map (f ≫ U.ι).appTop) :=
      MorphismProperty.of_postcomp (@IsFiniteEtale)
        (W' := (@IsFiniteEtale)) _ (Spec.map (Scheme.ΓSpecIso (.of R)).inv)
        (by exact ⟨⟩) inferInstance
    exact exists_finiteEtale_extension_of_open_affinization U f
      (IsFiniteEtale.SpecMap_iff.mp hp)

end EtaleFundamentalGroups
