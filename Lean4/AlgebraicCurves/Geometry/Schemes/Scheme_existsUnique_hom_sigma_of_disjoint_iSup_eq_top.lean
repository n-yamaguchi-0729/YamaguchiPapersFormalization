/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Scheme exists Unique hom sigma of disjoint i Sup eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem _root_.AlgebraicGeometry.Scheme.existsUnique_hom_sigma_of_disjoint_iSup_eq_top
    {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (U : σ → T.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : (⨆ i, U i) = ⊤)
    (v : ∀ i, ((U i : T.Opens) : Scheme.{u}) ⟶ H i) :
    ∃! u : T ⟶ ∐ H, ∀ i, (U i).ι ≫ u = v i ≫ Sigma.ι H i := by
  let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover U (IsOpenCover.mk hcov)
  have hcompat : ∀ i j : σ, pullback.fst (U i).ι (U j).ι ≫ (v i ≫ Sigma.ι H i) =
      pullback.snd (U i).ι (U j).ι ≫ (v j ≫ Sigma.ι H j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [fst_eq_snd_of_mono_eq (f := (U i).ι)]
    · let _ : IsEmpty ↥(pullback (U i).ι (U j).ι) := by
        refine ⟨fun x => ?_⟩
        have hx : (pullback.fst (U i).ι (U j).ι).base x ∈ Set.range (pullback.fst (U i).ι (U
          j).ι).base := ⟨x, rfl⟩
        rw [Scheme.Pullback.range_fst] at hx
        obtain ⟨y, hy⟩ := hx
        have h1 : ((U i).ι.base ((pullback.fst (U i).ι (U j).ι).base x)) ∈ (U i : Set T) := by
          exact Subtype.property _
        have h2 : ((U j).ι.base y) ∈ (U j : Set T) := by
          exact Subtype.property _
        rw [hy] at h2
        exact Set.disjoint_iff.mp (Opens.coe_disjoint.mpr (hdisj i j hij)) ⟨h1, h2⟩
      exact (isInitialOfIsEmpty).hom_ext _ _
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 (fun i => v i ≫ Sigma.ι H i) hcompat, fun i => ?_, fun u'
    hu' => ?_⟩
  · exact Scheme.Cover.ι_glueMorphisms 𝒰 _ hcompat i
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
    exact (hu' i).trans (Scheme.Cover.ι_glueMorphisms 𝒰 _ hcompat i).symm
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top
end ProofImplementation
