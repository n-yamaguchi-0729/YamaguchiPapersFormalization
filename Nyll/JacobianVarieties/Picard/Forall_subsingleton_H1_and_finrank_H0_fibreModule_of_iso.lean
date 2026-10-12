/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso

/-!
Transport geometric-fibre cohomology vanishing and dimension conditions along an isomorphism of
module sheaves.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.Forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
    NeronModelInfra

theorem _root_.AlgebraicGeometry.RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso
    {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) {F F' : (pullback c t).Modules} (e : F ≅ F') (n : ℕ)
    (h : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F')).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F')).H0 = n := by
  intro k _ s 𝒲
  have e' : fibreModule c t s F ≅ (Scheme.Modules.pullback (Iso.refl (pullback (pullback.snd c
    t) s)).hom).obj
      (fibreModule c t s F') :=
    (Scheme.Modules.pullback _).mapIso e ≪≫ ((Scheme.Modules.pullbackId _).app _).symm
  obtain ⟨𝒱, hU0, hU1, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (fibreAt c t s) (fibreAt c t s)
      (Iso.refl _) (Category.id_comp _) 𝒲 _ _ e'
  obtain ⟨h1, h0⟩ := h k s 𝒱
  refine ⟨?_, ?_⟩
  · have := h1
    exact eH1.symm.toEquiv.subsingleton
  · rw [← eH0.finrank_eq]
    exact h0
end JacobianVarieties.Picard.Proofs.Forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso
end ProofImplementation
