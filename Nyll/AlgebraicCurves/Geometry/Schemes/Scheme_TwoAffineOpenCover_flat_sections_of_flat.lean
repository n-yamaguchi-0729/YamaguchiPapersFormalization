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

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
# Flat sections on affine opens

For a flat scheme over an affine base, the sections on an affine open are flat over the
base ring with the algebra structure induced by the scheme morphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_TwoAffineOpenCover_flat_sections_of_flat

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_sections_of_flat
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) [Flat c]
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Flat R Γ(X, U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have h1 : (c.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat c inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have hb : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat :=
    RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of
        R)).symm.commRingCatIsoToRingEquiv.bijective
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appLE ⊤ U le_top).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp hb h1
  exact RingHom.flat_algebraMap_iff.mp h2
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_TwoAffineOpenCover_flat_sections_of_flat
end ProofImplementation
