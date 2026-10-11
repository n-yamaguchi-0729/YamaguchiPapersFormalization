/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.CompleteBooleanAlgebra
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech

/-!
# Scheme Ordered Affine Cover exists refinement preimage preimage of is Separated
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

end Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme.OrderedAffineCover



open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_OrderedAffineCover_exists_refinement_preimage_preimage_of_isSeparated in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem exists_refinement_preimage_preimage_of_isSeparated
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (𝒦 : X.OrderedAffineCover) (h₁ h₂ : X ⟶ X) [IsAffineHom h₁] [IsAffineHom h₂] :
    ∃ (𝒲 : X.OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι),
      (∀ w, 𝒲.U w ≤ h₁ ⁻¹ᵁ 𝒦.U (lam₁ w)) ∧ (∀ w, 𝒲.U w ≤ h₂ ⁻¹ᵁ 𝒦.U (lam₂ w)) := by
  classical
  have hsep : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = f ≫ terminal.from _ from terminal.hom_ext _ _]; infer_instance
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  let e := (Fintype.equivFin (𝒦.ι × 𝒦.ι)).symm
  let 𝒲 : X.OrderedAffineCover :=
    { ι := Fin (Fintype.card (𝒦.ι × 𝒦.ι))
      U := fun j => h₁ ⁻¹ᵁ 𝒦.U (e j).1 ⊓ h₂ ⁻¹ᵁ 𝒦.U (e j).2
      isAffineOpen := fun j => ((𝒦.isAffineOpen _).preimage h₁).inf ((𝒦.isAffineOpen _).preimage h₂)
      iSup_eq_top := by
        have h1 : (⨆ a, h₁ ⁻¹ᵁ 𝒦.U a) = ⊤ := by rw [← Scheme.Hom.preimage_iSup, 𝒦.iSup_eq_top]; rfl
        have h2 : (⨆ b, h₂ ⁻¹ᵁ 𝒦.U b) = ⊤ := by rw [← Scheme.Hom.preimage_iSup, 𝒦.iSup_eq_top]; rfl
        have key : (⨆ p : 𝒦.ι × 𝒦.ι, h₁ ⁻¹ᵁ 𝒦.U p.1 ⊓ h₂ ⁻¹ᵁ 𝒦.U p.2) = ⊤ := by
          rw [iSup_prod]
          dsimp only
          rw [show (⨆ i, ⨆ j, h₁ ⁻¹ᵁ 𝒦.U i ⊓ h₂ ⁻¹ᵁ 𝒦.U j) = ⨆ i, (h₁ ⁻¹ᵁ 𝒦.U i ⊓ ⨆ j, h₂ ⁻¹ᵁ 𝒦.U
            j) from
              iSup_congr fun i => (inf_iSup_eq _ _).symm,
            ← iSup_inf_eq, h1, h2, top_inf_eq]
        rw [← key]
        exact e.iSup_comp (g := fun p : 𝒦.ι × 𝒦.ι => h₁ ⁻¹ᵁ 𝒦.U p.1 ⊓ h₂ ⁻¹ᵁ 𝒦.U p.2) }
  exact ⟨𝒲, fun j => (e j).1, fun j => (e j).2, fun j => inf_le_left, fun j => inf_le_right⟩
end AlgebraicGeometry.Scheme.OrderedAffineCover
end ProofImplementation
