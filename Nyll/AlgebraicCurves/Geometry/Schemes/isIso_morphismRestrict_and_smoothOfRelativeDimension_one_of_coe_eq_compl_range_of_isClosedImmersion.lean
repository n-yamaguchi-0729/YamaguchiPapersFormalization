/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# is Iso morphism Restrict and smooth Of Relative Dimension one of coe eq compl range of is
Closed Immersion
-/

section ProofImplementation

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry

theorem
 isIso_morphismRestrict_and_smoothOfRelativeDimension_one_of_coe_eq_compl_range_of_isClosedImmersion
    {k : Type u} [Field k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 c₁]
    (i₁ : SchemeHomOver c₁ x) (i₂ : C₂ ⟶ X) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.base)
    (U : X.Opens) (hU : (U : Set X) = (Set.range i₂.base)ᶜ) :
    IsIso (i₁.1 ∣_ U) ∧ SmoothOfRelativeDimension 1 (U.ι ≫ x) := by
  obtain ⟨i, hi⟩ := i₁
  subst hi
  let _ : Surjective (i ∣_ U) := by
    refine ⟨fun u => ?_⟩
    rcases hjs u.1 with ⟨z, hz⟩ | ⟨z, hz⟩
    · have hzU : z ∈ i ⁻¹ᵁ U := by
        change i.base z ∈ U
        rw [hz]; exact u.2
      let z' : (i ⁻¹ᵁ U : Scheme.{u}) := ⟨z, hzU⟩
      refine ⟨z', Subtype.ext ?_⟩
      exact (morphismRestrict_base_coe i U z').trans hz
    · exfalso
      have hu : (u.1 : X) ∈ (U : Set X) := u.2
      rw [hU] at hu
      exact hu ⟨z, hz⟩
  let _ : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
  have hiso : IsIso (i ∣_ U) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨hiso, ?_⟩
  have hfac : U.ι ≫ x = inv (i ∣_ U) ≫ ((i ⁻¹ᵁ U).ι ≫ i ≫ x) := by
    rw [← Category.assoc (i ⁻¹ᵁ U).ι i x, ← morphismRestrict_ι, Category.assoc,
      IsIso.inv_hom_id_assoc]
  have h01 : SmoothOfRelativeDimension (0 + 1) ((i ⁻¹ᵁ U).ι ≫ i ≫ x) := inferInstance
  let _ : SmoothOfRelativeDimension 1 ((i ⁻¹ᵁ U).ι ≫ i ≫ x) := by simpa using h01
  have h : SmoothOfRelativeDimension (0 + 1) (inv (i ∣_ U) ≫ ((i ⁻¹ᵁ U).ι ≫ i ≫ x)) := inferInstance
  rw [hfac]
  simpa using h
end AlgebraicGeometry
end ProofImplementation
