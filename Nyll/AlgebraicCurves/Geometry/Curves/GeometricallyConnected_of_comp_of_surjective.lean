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

import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric connectedness descends through a surjective morphism

If a composite is geometrically connected and its first map is surjective, the second
map is geometrically connected.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs.GeometricallyConnected_of_comp_of_surjective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyConnected (f ≫ g)] [Surjective f] :
    GeometricallyConnected g := by
  have : MorphismProperty.IsStableUnderComposition
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) :=
    ⟨fun h k hh hk => ⟨hk.surj.comp hh.surj⟩⟩
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) := by
    refine .mk' ?_
    introv hg
    simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
    rw [hg, Set.preimage_univ]
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k ↦ ?_⟩
  have hX : ConnectedSpace ↥(pullback (f ≫ g) k) :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := f ≫ g)) K k
  let φ : pullback (f ≫ g) k ⟶ pullback g k :=
    pullback.map (f ≫ g) k g k f (𝟙 _) (𝟙 Z) (Category.comp_id _) (by simp)
  have hφ : Surjective φ :=
    MorphismProperty.pullbackMap (P := fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h)
        ‹Surjective f› inferInstance rfl
      (Category.id_comp _).symm
  rw [connectedSpace_iff_univ, ← hφ.surj.range_eq]
  exact isConnected_range φ.continuous
end AlgebraicCurves.Geometry.Curves.Proofs.GeometricallyConnected_of_comp_of_surjective
end ProofImplementation
