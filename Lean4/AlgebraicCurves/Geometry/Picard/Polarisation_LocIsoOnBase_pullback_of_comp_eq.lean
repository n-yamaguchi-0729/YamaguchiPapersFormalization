/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import AlgebraicCurves.Geometry.Picard.PolarisationRosati

/-!
# Polarisation Loc Iso On Base pullback of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs.Polarisation_LocIsoOnBase_pullback_of_comp_eq

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Polarisation

universe u

theorem _root_.AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq
    {S S' : Type u} [CommRing S] [CommRing S'] {X Y : Scheme.{u}}
    {g : X ⟶ Spec (CommRingCat.of S)} (g' : Y ⟶ Spec (CommRingCat.of S')) (h : Y ⟶ X)
    (φ : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (comm : h ≫ g = g' ≫ φ)
    {M M' : X.Modules} (hM : LocIsoOnBase g M M') :
    LocIsoOnBase g' ((Scheme.Modules.pullback h).obj M) ((Scheme.Modules.pullback h).obj M') := by
  intro s'
  obtain ⟨U, hs, ⟨e⟩⟩ := hM (φ.base s')
  refine ⟨φ ⁻¹ᵁ U, hs, ⟨?_⟩⟩
  have hle : g' ⁻¹ᵁ (φ ⁻¹ᵁ U) ≤ h ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, comm]
  let r : (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)).toScheme ⟶ (g ⁻¹ᵁ U).toScheme := h.resLE (g ⁻¹ᵁ U) (g' ⁻¹ᵁ (φ ⁻¹ᵁ U))
    hle
  have hr : r ≫ (g ⁻¹ᵁ U).ι = (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)).ι ≫ h := Scheme.Hom.resLE_comp_ι _ _
  exact ((Scheme.Modules.pullbackComp (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)).ι h).app M) ≪≫
    (Scheme.Modules.pullbackCongr hr.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp r (g ⁻¹ᵁ U).ι).app M).symm ≪≫
        (Scheme.Modules.pullback r).mapIso e ≪≫
          (Scheme.Modules.pullbackComp r (g ⁻¹ᵁ U).ι).app M' ≪≫
            (Scheme.Modules.pullbackCongr hr).app M' ≪≫
              ((Scheme.Modules.pullbackComp (g' ⁻¹ᵁ (φ ⁻¹ᵁ U)).ι h).app M').symm
end AlgebraicCurves.Geometry.Picard.Proofs.Polarisation_LocIsoOnBase_pullback_of_comp_eq
end ProofImplementation
