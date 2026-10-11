/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Spectrum.Prime.Topology
import AlgebraicCurves.Geometry.Picard.PolarisationRosati

/-!
# Polarisation loc Iso On Base iff nonempty iso of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs
namespace Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Polarisation

theorem _root_.AlgebraicGeometry.Polarisation.locIsoOnBase_iff_nonempty_iso_of_isLocalRing
    {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S)) (M
      M' : X.Modules) :
    LocIsoOnBase g M M' ↔ Nonempty (M ≅ M') := by
  classical
  constructor
  · intro h
    obtain ⟨U, hsU, ⟨e⟩⟩ := h (IsLocalRing.closedPoint S)
    have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hsU
    subst hU
    let ι : (↑(g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens)) : Scheme.{0}) ⟶ X := (g ⁻¹ᵁ (⊤ : (Spec
      (CommRingCat.of S)).Opens)).ι
    let j : X ⟶ ↑(g ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of S)).Opens)) := (Scheme.topIso X).inv
    have hj : j ≫ ι = 𝟙 X := (Scheme.topIso X).inv_hom_id
    let Φ : 𝟭 X.Modules ≅ Scheme.Modules.pullback ι ⋙ Scheme.Modules.pullback j :=
      (Scheme.Modules.pullbackId X).symm ≪≫ eqToIso
        (by rw [hj]) ≪≫ (Scheme.Modules.pullbackComp j ι).symm
    exact ⟨Φ.app M ≪≫ (Scheme.Modules.pullback j).mapIso e ≪≫ (Φ.app M').symm⟩
  · rintro ⟨e⟩ s
    exact ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩
end AlgebraicCurves.Geometry.Picard.Proofs.Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
end ProofImplementation
