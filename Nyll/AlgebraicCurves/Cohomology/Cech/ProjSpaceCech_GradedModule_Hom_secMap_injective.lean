/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_Hom_secMap_injective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule

/-!
# Proj Space Cech Graded Module Hom sec Map injective
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_Hom_secMap_injective

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section SecMapInj

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule
open _root_.ProjSpaceCech.GradedModule
namespace Hom
open _root_.ProjSpaceCech.GradedModule.Hom
end GradedModule.Hom
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Hom in
theorem GradedModule.Hom.secMap_mk (φ : GradedModule.Hom D₁ D₂) (I : Finset (Fin (n + 1)))
    (x : GradedModule.Frac D₁ I) :
    GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
      = GradedModule.sec.mk D₂ I ⟨x.denExp, x.hden, φ.toLinearMap x.num, φ.mem_grade _ _ x.hnum⟩
        := rfl

open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Hom in
theorem GradedModule.Hom.secMap_injective' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (GradedModule.Hom.secMap φ I) := by
  intro p q h
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  change GradedModule.sec.mk D₁ I x = GradedModule.sec.mk D₁ I y
  change GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
    = GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I y) at h
  rw [GradedModule.Hom.secMap_mk, GradedModule.Hom.secMap_mk, GradedModule.sec_mk_eq] at h
  obtain ⟨c, hc, heq⟩ := h
  refine (GradedModule.sec_mk_eq D₁ I).mpr ⟨c, hc, hinj ?_⟩
  rw [GradedModule.Hom.map_monMul, GradedModule.Hom.map_monMul]
  exact heq

end SecMapInj

end ProjSpaceCech

theorem _root_.ProjSpaceCech.GradedModule.Hom.secMap_injective {R : Type u} [CommRing R] {n : ℕ}
  {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (ProjSpaceCech.GradedModule.Hom.secMap φ I) :=
  ProjSpaceCech.GradedModule.Hom.secMap_injective' φ hinj I

end
end AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_Hom_secMap_injective
end ProofImplementation
