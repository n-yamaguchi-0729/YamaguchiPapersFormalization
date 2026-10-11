/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Data.Prod.Lex
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage

/-!
# Scheme Ordered Affine Cover exists refinement pullback fst snd of is Separated
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

end Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_OrderedAffineCover_exists_refinement_pullback_fst_snd_of_isSeparated in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
open _root_.AlgebraicGeometry.Scheme.Pullback in
theorem exists_refinement_pullback_fst_snd_of_isSeparated
    {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (𝒦 : A.OrderedAffineCover) (μ : pullback f f ⟶ A) (_hμ : μ ≫ f = pullback.fst f f ≫ f) :
    ∃ (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ lam₃ : 𝒲.ι → 𝒦.ι),
      (∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w)) ∧
      (∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w)) ∧
      (∀ w, 𝒲.U w ≤ μ ⁻¹ᵁ 𝒦.U (lam₃ w)) := by
  classical
  have mem_cover : ∀ y : A, ∃ i, y ∈ 𝒦.U i := fun y => by
    have hy : y ∈ (⊤ : A.Opens) := trivial
    rw [← 𝒦.iSup_eq_top] at hy
    exact TopologicalSpace.Opens.mem_iSup.mp hy
  have box : ∀ i j : 𝒦.ι, IsAffineOpen (pullback.fst f f ⁻¹ᵁ 𝒦.U i ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U j) :=
    fun i j => (isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
      f f (𝒦.U i) (𝒦.isAffineOpen i) (𝒦.U j) (𝒦.isAffineOpen j)).1
  let γ : pullback f f ⟶ pullback (μ ≫ f) f := pullback.lift (𝟙 _) μ (Category.id_comp (μ ≫ f))
  have : IsClosedImmersion γ := inferInstance
  have box3 : ∀ i j l : 𝒦.ι,
      IsAffineOpen (pullback.fst f f ⁻¹ᵁ 𝒦.U i ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U j ⊓ μ ⁻¹ᵁ 𝒦.U l) := by
    intro i j l
    have h2 := (isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage
      (μ ≫ f) f _ (box i j) (𝒦.U l) (𝒦.isAffineOpen l)).1
    have h3 := h2.preimage γ
    have e : γ ⁻¹ᵁ (pullback.fst (μ ≫ f) f ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ 𝒦.U i ⊓ pullback.snd f f ⁻¹ᵁ
      𝒦.U j) ⊓
        pullback.snd (μ ≫ f) f ⁻¹ᵁ 𝒦.U l) =
        pullback.fst f f ⁻¹ᵁ 𝒦.U i ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U j ⊓ μ ⁻¹ᵁ 𝒦.U l := by
      rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
        pullback.lift_fst,
        pullback.lift_snd, Scheme.Hom.id_preimage]
    rwa [e] at h3
  refine ⟨{ ι := 𝒦.ι × 𝒦.ι × 𝒦.ι
            instLinearOrder := (inferInstance : LinearOrder (𝒦.ι ×ₗ 𝒦.ι ×ₗ 𝒦.ι))
            U := fun w => pullback.fst f f ⁻¹ᵁ 𝒦.U w.1 ⊓ pullback.snd f f ⁻¹ᵁ 𝒦.U w.2.1 ⊓ μ ⁻¹ᵁ 𝒦.U
              w.2.2
            isAffineOpen := fun w => box3 w.1 w.2.1 w.2.2
            iSup_eq_top := ?_ }, fun w => w.1, fun w => w.2.1, fun w => w.2.2, ?_, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := mem_cover ((pullback.fst f f).base x)
    obtain ⟨j, hj⟩ := mem_cover ((pullback.snd f f).base x)
    obtain ⟨l, hl⟩ := mem_cover (μ.base x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j, l), ⟨⟨hi, hj⟩, hl⟩⟩
  · intro w; exact inf_le_left.trans inf_le_left
  · intro w; exact inf_le_left.trans inf_le_right
  · intro w; exact inf_le_right
end AlgebraicGeometry.Scheme.OrderedAffineCover
end ProofImplementation
