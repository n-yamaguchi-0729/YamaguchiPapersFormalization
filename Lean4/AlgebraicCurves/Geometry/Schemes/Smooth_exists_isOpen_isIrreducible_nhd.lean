/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_isOpen_isIrreducible_nhd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Topology.NoetherianSpace
import AlgebraicCurves.Geometry.Schemes.isIntegral_of_smooth_of_preconnectedSpace

/-!
# Smooth exists is Open is Irreducible nhd
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_exists_isOpen_isIrreducible_nhd

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SmoothUnibranchAux

theorem isOpen_connectedComponent_of_noetherianSpace {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  classical
  let F : Set (Set α) := {Z ∈ irreducibleComponents α | Disjoint Z (connectedComponent x)}
  have hF : F.Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z
    hZ => hZ.1)
  have hcl : IsClosed (⋃ Z ∈ F, Z) :=
    hF.isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have hcompl : (connectedComponent x)ᶜ = ⋃ Z ∈ F, Z := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩,
        mem_irreducibleComponent⟩
      rw [Set.disjoint_left]
      intro w hwZ hwx
      apply hz
      have hsub : irreducibleComponent z ⊆ connectedComponent w :=
        (isIrreducible_irreducibleComponent.isConnected.isPreconnected).subset_connectedComponent
          hwZ
      rw [connectedComponent_eq hwx]
      exact hsub mem_irreducibleComponent
    · rintro ⟨Z, ⟨-, hZd⟩, hzZ⟩ hzx
      exact Set.disjoint_left.1 hZd hzZ hzx
  rw [← isClosed_compl_iff, hcompl]
  exact hcl

end SmoothUnibranchAux

open SmoothUnibranchAux in
theorem _root_.AlgebraicGeometry.Smooth.exists_isOpen_isIrreducible_nhd
    {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f] (y : ↥Y) :
    ∃ Ω : Y.Opens, y ∈ Ω ∧ IsIrreducible (Ω : Set ↥Y) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : TopologicalSpace.NoetherianSpace ↥(U : Scheme.{u}) := noetherianSpace_of_isAffineOpen U hU
  let y' : ↥(U : Scheme.{u}) := ⟨y, hyU⟩
  let V : (U : Scheme.{u}).Opens := ⟨connectedComponent y',
    isOpen_connectedComponent_of_noetherianSpace y'⟩
  have : PreconnectedSpace ↥(V : Scheme.{u}) := Subtype.preconnectedSpace
    isPreconnected_connectedComponent
  have : Nonempty ↥(V : Scheme.{u}) := ⟨⟨y', mem_connectedComponent⟩⟩
  have : Smooth (V.ι ≫ U.ι ≫ f) := inferInstance
  have : IsIntegral (V : Scheme.{u}) := isIntegral_of_smooth_of_preconnectedSpace (V.ι ≫ U.ι ≫ f)
  refine ⟨U.ι ''ᵁ V, ⟨y', mem_connectedComponent, rfl⟩, ?_⟩
  change IsIrreducible (U.ι.base '' (V : Set ↥(U : Scheme.{u})))
  have hV : IsIrreducible (V : Set ↥(U : Scheme.{u})) := by
    have h := (IrreducibleSpace.isIrreducible_univ (X := ↥(V : Scheme.{u}))).image V.ι.base
      V.ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at h
  exact hV.image _ U.ι.continuous.continuousOn
end AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_exists_isOpen_isIrreducible_nhd
end ProofImplementation
