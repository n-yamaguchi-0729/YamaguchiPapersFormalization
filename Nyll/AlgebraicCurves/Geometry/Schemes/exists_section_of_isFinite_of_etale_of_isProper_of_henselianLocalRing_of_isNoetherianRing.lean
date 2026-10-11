/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


import Nyll.SchemeTheory.FiniteEtale.ProperHenselianSections

/-!
# Lifting finite etale sections over a Noetherian Henselian base

The existing public statement is retained as a specialization of the
unrestricted Henselian section-lifting theorem in SchemeTheory.
-/

namespace AlgebraicGeometry

universe u

open CategoryTheory CategoryTheory.Limits

theorem exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (π : Y ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π]
    (s₀ : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶ Y)
    (hs₀ : s₀ ≫ π = pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    ∃ s : X ⟶ Y, s ≫ π = 𝟙 X ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ s = s₀ :=
  exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing f π s₀ hs₀

end AlgebraicGeometry
