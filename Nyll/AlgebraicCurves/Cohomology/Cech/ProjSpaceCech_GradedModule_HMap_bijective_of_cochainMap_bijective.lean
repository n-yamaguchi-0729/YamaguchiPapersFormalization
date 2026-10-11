/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule

/-!
# Proj Space Cech Graded Module HMap bijective of cochain Map bijective
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.ProjectiveGradedHMapBijective

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section HMapBijective

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
end GradedModule
open scoped _root_.ProjSpaceCech.GradedModule in
theorem GradedModule.HMap_bijective_of_cochainMap_bijective' (φ : GradedModule.Hom D₁ D₂)
    (h : ∀ i, Function.Bijective (GradedModule.Hom.cochainMap φ i)) (i : ℕ) :
    Function.Bijective (GradedModule.Hom.HMap φ i) := by
  classical
  have hcomm : ∀ k (x : GradedModule.cochain D₁ k),
      GradedModule.d D₂ k (GradedModule.Hom.cochainMap φ k x)
        = GradedModule.Hom.cochainMap φ (k + 1) (GradedModule.d D₁ k x) := fun k x => by
    rw [← LinearMap.comp_apply, GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply]
  have hker : ∀ k (x : GradedModule.cochain D₁ k),
      GradedModule.Hom.cochainMap φ k x ∈ LinearMap.ker (GradedModule.d D₂ k)
        ↔ x ∈ LinearMap.ker (GradedModule.d D₁ k) := fun k x => by
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hcomm]
    exact ⟨fun hx => (h (k + 1)).1 (by rw [hx, map_zero]), fun hx => by rw [hx, map_zero]⟩
  have hrange : ∀ k (y : GradedModule.cochain D₁ (k + 1)),
      GradedModule.Hom.cochainMap φ (k + 1) y ∈ LinearMap.range (GradedModule.d D₂ k)
        ↔ y ∈ LinearMap.range (GradedModule.d D₁ k) := fun k y => by
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := (h k).2 x'
      exact ⟨x, (h (k + 1)).1 (by rw [← hcomm, hx'])⟩
    · rintro ⟨x, rfl⟩
      exact ⟨GradedModule.Hom.cochainMap φ k x, hcomm k x⟩
  have hkerbij : ∀ k, Function.Bijective (GradedModule.Hom.cochainMapKer φ k) := fun k => by
    constructor
    · intro x y hxy
      exact Subtype.ext ((h k).1 (congrArg Subtype.val hxy))
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := (h k).2 z
      exact ⟨⟨x, (hker k x).mp hz⟩, rfl⟩
  rcases i with _ | j
  · exact hkerbij 0
  · simp only [GradedModule.Hom.HMap]
    constructor
    · refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      have ha' : GradedModule.Hom.cochainMapKer φ (j + 1) x
          ∈ (LinearMap.range (GradedModule.d D₂ j)).comap
              (LinearMap.ker (GradedModule.d D₂ (j + 1))).subtype :=
        (Submodule.Quotient.mk_eq_zero _).mp ha
      rw [Submodule.mem_comap, Submodule.subtype_apply] at ha'
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ((hrange j x.1).mp ha'))
    · intro q
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨x, rfl⟩ := (hkerbij (j + 1)).2 w
      exact ⟨Submodule.Quotient.mk x, rfl⟩

end HMapBijective

end ProjSpaceCech

theorem _root_.ProjSpaceCech.GradedModule.HMap_bijective_of_cochainMap_bijective {R : Type u}
  [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n}
    (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂) (h : ∀ i, Function.Bijective
      (ProjSpaceCech.GradedModule.Hom.cochainMap φ i)) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.HMap φ i) :=
  ProjSpaceCech.GradedModule.HMap_bijective_of_cochainMap_bijective' φ h i

end
end AlgebraicCurves.Cohomology.Cech.Proofs.ProjectiveGradedHMapBijective
end ProofImplementation
