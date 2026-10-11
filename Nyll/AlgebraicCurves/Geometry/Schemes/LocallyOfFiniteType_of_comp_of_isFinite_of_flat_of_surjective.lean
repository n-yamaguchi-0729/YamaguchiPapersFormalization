/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Adjoin.Tower

/-!
# Descent of finite type through a finite flat cover

A finite, flat, surjective first morphism allows local finite type of its composite to
descend to the second morphism over a locally Noetherian base.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.LocallyOfFiniteType.of_comp_of_isFinite_of_flat_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType (f ≫ g)] [IsFinite f]
    [Flat f] [Surjective f] [IsLocallyNoetherian Z] : LocallyOfFiniteType g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)]
  intro U V e
  have hV' : IsAffineOpen (f ⁻¹ᵁ (V : Y.Opens)) := V.2.preimage f
  let V' : X.affineOpens := ⟨f ⁻¹ᵁ (V : Y.Opens), hV'⟩
  have e' : (V' : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ (U : Z.Opens) :=
    ((TopologicalSpace.Opens.map f.base).map (homOfLE e)).le
  let φAB := g.appLE U V e
  let φBC := f.appLE V V' le_rfl
  let φAC := (f ≫ g).appLE U V' e'
  have hcomp : φAB ≫ φBC = φAC := Scheme.Hom.appLE_comp_appLE f g U V V' e le_rfl
  have hAC : φAC.hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) _ ‹_› U V' e'
  have hBC : φBC.hom.Finite := by
    have := IsFinite.finite_app f V V.2
    rwa [Scheme.Hom.app_eq_appLE] at this
  have hBCflat : φBC.hom.Flat := HasRingHomProperty.appLE (P := @Flat) _ ‹_› V V' le_rfl
  have : IsOpenImmersion (V.2.fromSpec : Spec Γ(Y, (V : Y.Opens)) ⟶ Y) :=
    IsAffineOpen.isOpenImmersion_fromSpec V.2
  have hBCsurj : Surjective (Spec.map φBC) := by
    refine ⟨fun q ↦ ?_⟩
    have hq : (V.2.fromSpec q : Y) ∈ (V : Y.Opens) :=
      V.2.range_fromSpec.le (Set.mem_range_self q)
    obtain ⟨x, hx⟩ := ‹Surjective f›.surj (V.2.fromSpec q)
    have hxV' : x ∈ (V' : X.Opens) := show f x ∈ (V : Y.Opens) by rw [hx]; exact hq
    obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    refine ⟨p, V.2.fromSpec.isOpenEmbedding.injective ?_⟩
    have key := congrArg (fun h ↦ h p) (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 hV' le_rfl)
    simp only [Scheme.Hom.comp_apply] at key
    change V.2.fromSpec (Spec.map φBC p) = V.2.fromSpec q
    rw [key, hp, hx]
  have hBCinj : Function.Injective φBC.hom :=
    ((flat_and_surjective_SpecMap_iff φBC).mp
      ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mpr hBCflat, hBCsurj⟩).injective
  algebraize [φAB.hom, φBC.hom, φAC.hom]
  have : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, V') :=
    .of_algebraMap_eq' (by change φAC.hom = φBC.hom.comp φAB.hom; rw [← hcomp]; rfl)
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian U
  have hfg := fg_of_fg_of_fg Γ(Z, U) Γ(Y, V) Γ(X, V') hAC.out Module.Finite.fg_top hBCinj
  exact ⟨hfg⟩
end LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
