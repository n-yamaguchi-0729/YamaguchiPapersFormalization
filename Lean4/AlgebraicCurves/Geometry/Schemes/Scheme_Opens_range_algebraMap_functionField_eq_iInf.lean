/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.IsAffineOpen_range_algebraMap_functionField_eq_iInf

/-!
# Sections as an intersection of stalks in the function field

For a nonempty open of an integral scheme, the image of its section ring in the
function field equals the intersection of the images of the stalks at its points.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Opens_range_algebraMap_functionField_eq_iInf

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace EngineOpen
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X]

theorem germToFunctionField_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(X,
    U)) :
    (X.germToFunctionField V).hom ((X.presheaf.map i.op).hom s) = (X.germToFunctionField U).hom
        s := by
  change (X.presheaf.map i.op ≫ X.germToFunctionField V).hom s = _
  rw [Scheme.germToFunctionField, X.presheaf.germ_res]

end AlgebraicGeometry.EngineOpen

open AlgebraicGeometry.EngineOpen in
theorem _root_.AlgebraicGeometry.Scheme.Opens.range_algebraMap_functionField_eq_iInf
    {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U] :
    (algebraMap Γ(X, U) X.functionField).range =
      ⨅ (x : X) (_ : x ∈ U), (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  classical
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    let halgebra := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
    have htower : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U ⟨x, hx⟩
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap Γ(X, U) (X.presheaf.stalk x) a,
      (IsScalarTower.algebraMap_apply Γ(X, U) _ X.functionField a).symm⟩
  · intro f hf
    have hW : ∀ x : U, ∃ W : X.Opens, IsAffineOpen W ∧ (x : X) ∈ W ∧ (W : Set X) ⊆ U := fun x =>
      exists_isAffineOpen_mem_and_subset x.2
    choose W hWaff hxW hWU using hW
    have hWne : ∀ x : U, Nonempty (W x) := fun x => ⟨⟨x, hxW x⟩⟩
    have hsec : ∀ x : U, ∃ s : Γ(X, W x), (X.germToFunctionField (W x)).hom s = f := by
      intro x
      have hfx : f ∈ (algebraMap Γ(X, W x) X.functionField).range := by
        rw [(hWaff x).range_algebraMap_functionField_eq_iInf]
        refine Subring.mem_iInf.mpr fun y => Subring.mem_iInf.mpr fun hy => ?_
        exact (Subring.mem_iInf.mp ((Subring.mem_iInf.mp hf) y)) (hWU x hy)
      obtain ⟨s, hs⟩ := hfx
      exact ⟨s, hs⟩
    choose sf hsf using hsec
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 W sf := by
      intro x y
      have hintersection : Nonempty ((W x ⊓ W y : X.Opens)) := by
        obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (W x).isOpen (W y).isOpen
          ⟨x, hxW x⟩ ⟨y, hxW y⟩
        exact ⟨⟨z, hz⟩⟩
      apply X.germToFunctionField_injective (W x ⊓ W y)
      change (X.germToFunctionField (W x ⊓ W y)).hom ((X.presheaf.map _).hom (sf x)) =
        (X.germToFunctionField (W x ⊓ W y)).hom ((X.presheaf.map _).hom (sf y))
      rw [germToFunctionField_map, germToFunctionField_map, hsf, hsf]
    have hcover : U ≤ iSup W := fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxW ⟨z, hz⟩⟩
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun x => homOfLE (hWU x)) hcover sf
        hcompat
    refine ⟨s, ?_⟩
    obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty U)
    let i0 : U := ⟨x, hx⟩
    have hres : (X.presheaf.map (homOfLE (hWU i0)).op).hom s = sf i0 := hs i0
    change (X.germToFunctionField U).hom s = f
    rw [← germToFunctionField_map (homOfLE (hWU i0)) s]
    exact (congrArg (fun t => (X.germToFunctionField (W i0)).hom t) hres).trans (hsf i0)
end Scheme_Opens_range_algebraMap_functionField_eq_iInf
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
