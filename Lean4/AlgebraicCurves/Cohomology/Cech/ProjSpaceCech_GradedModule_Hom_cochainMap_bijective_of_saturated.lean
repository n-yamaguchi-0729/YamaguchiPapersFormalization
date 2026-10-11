/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import AlgebraicCurves.Cohomology.Cech.ProjSpaceCech_GradedModule_Hom_secMap_bijective_of_saturated

/-!
# Proj Space Cech Graded Module Hom cochain Map bijective of saturated
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.ProjectiveGradedHomCochainMap

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section CochainSat

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
namespace Hom
open _root_.ProjSpaceCech.GradedModule.Hom
end GradedModule.Hom
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Hom in
theorem GradedModule.Hom.cochainMap_bijective_of_saturated' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (GradedModule.Hom.cochainMap φ i) := by
  have hb : ∀ s : Idx n i, Function.Bijective (GradedModule.Hom.secMap φ (Idx.img n s)) := fun s =>
    GradedModule.Hom.secMap_bijective_of_saturated φ hinj hsat _
      (by rw [← Finset.card_pos, Idx.card_img]; exact Nat.succ_pos i)
  constructor
  · intro f g h
    funext s
    exact (hb s).1 (congrFun h s)
  · intro g
    choose f hf using fun s => (hb s).2 (g s)
    exact ⟨f, funext hf⟩

end CochainSat

end ProjSpaceCech

theorem _root_.ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated {R : Type u}
  [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ :
  ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.cochainMap φ i) :=
  ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated' φ hinj hsat i

end
end AlgebraicCurves.Cohomology.Cech.Proofs.ProjectiveGradedHomCochainMap
end ProofImplementation
