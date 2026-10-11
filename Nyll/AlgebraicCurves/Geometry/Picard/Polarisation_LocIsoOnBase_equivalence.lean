/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati

/-!
# Polarisation Loc Iso On Base equivalence
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs.Polarisation_LocIsoOnBase_equivalence

noncomputable section


open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Polarisation


universe u

namespace LocIsoOnBaseEquivSol

open _root_.AlgebraicGeometry.Polarisation
open _root_.AlgebraicGeometry


variable {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S))

private theorem refl (M : X.Modules) : LocIsoOnBase g M M :=
  fun _ => ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

variable {g} in
private theorem symm {M M' : X.Modules} (h : LocIsoOnBase g M M') : LocIsoOnBase g M' M := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  exact ⟨U, hs, ⟨e.symm⟩⟩

/-- The restriction of a local module isomorphism to a smaller open of the base. -/
def restrictIso {M M' : X.Modules} {U V : (Spec (CommRingCat.of S)).Opens} (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj
      M') :
    (Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ V).ι).obj M' :=
  have hle : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U := fun _ hx => hVU hx
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hle) (g ⁻¹ᵁ U).ι).app M).symm ≪≫
      (Scheme.Modules.pullback (X.homOfLE hle)).mapIso e ≪≫
        (Scheme.Modules.pullbackComp (X.homOfLE hle) (g ⁻¹ᵁ U).ι).app M' ≪≫
          (Scheme.Modules.pullbackCongr (X.homOfLE_ι hle)).app M'

variable {g} in
theorem trans {M M' M'' : X.Modules} (h : LocIsoOnBase g M M') (h' : LocIsoOnBase g M' M'') :
    LocIsoOnBase g M M'' := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  obtain ⟨U', hs', ⟨e'⟩⟩ := h' s
  exact ⟨U ⊓ U', ⟨hs, hs'⟩, ⟨restrictIso g inf_le_left e ≪≫ restrictIso g inf_le_right e'⟩⟩

end LocIsoOnBaseEquivSol

open LocIsoOnBaseEquivSol in
theorem _root_.AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence
    {S : Type u} [CommRing S] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) :
    Equivalence (LocIsoOnBase g) :=
  ⟨fun M => refl g M, fun h => LocIsoOnBaseEquivSol.symm h, fun h h' => LocIsoOnBaseEquivSol.trans
    h h'⟩

end
end AlgebraicCurves.Geometry.Picard.Proofs.Polarisation_LocIsoOnBase_equivalence
end ProofImplementation
