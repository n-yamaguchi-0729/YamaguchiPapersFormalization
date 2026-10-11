/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_GradedModule_Hom_secMap_bijective_of_saturated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
import SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import AlgebraicCurves.Cohomology.Cech.ProjSpaceCech_GradedModule_Hom_secMap_injective

/-!
# Proj Space Cech Graded Module Hom sec Map bijective of saturated
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.GradedSecMapBijective

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section SecMapSat

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
theorem GradedModule.Hom.secMap_surjective_of_saturated (φ : GradedModule.Hom D₁ D₂)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Surjective (GradedModule.Hom.secMap φ I) := by
  classical
  obtain ⟨j, hj⟩ := hI
  intro q
  obtain ⟨⟨a, ha, m, hm⟩, rfl⟩ := Quotient.exists_rep q
  obtain ⟨k, m', hm', hφ⟩ := hsat j _ m hm
  let b : Fin (n + 1) → ℕ := a + Pi.single j k
  have hb : ∀ l, b l = a l + (Pi.single j k : Fin (n + 1) → ℕ) l := fun l => rfl
  have ha' : ∀ l ∉ I, b l = 0 := fun l hl => by
    have hlj : l ≠ j := fun h => hl (h ▸ hj)
    rw [hb, ha l hl, Pi.single_eq_of_ne hlj, add_zero]
  have hsum : (∑ l, (b l : ℤ)) = (∑ l, (a l : ℤ)) + k := by
    simp only [hb, Nat.cast_add, Finset.sum_add_distrib, add_right_inj]
    rw [Finset.sum_eq_single j (fun l _ hl => by rw [Pi.single_eq_of_ne hl, Nat.cast_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]
  refine ⟨GradedModule.sec.mk D₁ I ⟨b, ha', m', by rw [hsum]; exact hm'⟩, ?_⟩
  rw [GradedModule.Hom.secMap_mk]
  refine (GradedModule.sec_mk_eq D₂ I).mpr ⟨0, fun _ _ => rfl, ?_⟩
  change GradedModule.monMul D₂ (0 + a) (φ.toLinearMap m') = GradedModule.monMul D₂ (0 + b) m
  rw [zero_add, zero_add, hφ, show b = a + Pi.single j k from rfl, GradedModule.monMul_add_apply,
    GradedModule.monMul_single]

open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Hom in
theorem GradedModule.Hom.secMap_bijective_of_saturated' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Bijective (GradedModule.Hom.secMap φ I) :=
  ⟨GradedModule.Hom.secMap_injective φ hinj I, GradedModule.Hom.secMap_surjective_of_saturated φ
    hsat I hI⟩

end SecMapSat

end ProjSpaceCech

theorem _root_.ProjSpaceCech.GradedModule.Hom.secMap_bijective_of_saturated {R : Type u}
  [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ :
  ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m)
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.secMap φ I) :=
  ProjSpaceCech.GradedModule.Hom.secMap_bijective_of_saturated' φ hinj hsat I hI

end
end AlgebraicCurves.Cohomology.Cech.Proofs.GradedSecMapBijective
end ProofImplementation
