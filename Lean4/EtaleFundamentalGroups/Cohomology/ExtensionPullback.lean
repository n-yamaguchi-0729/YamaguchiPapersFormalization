/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Pulling an extension back with its original coefficient identification

The middle object is the actual categorical pullback. Its kernel is identified
using a specified isomorphism to the original kernel, and its short exactness
is proved from the pullback and kernel universal properties.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace EtaleFundamentalGroups.Cohomology

variable {C : Type u} [Category.{v} C] [Abelian C]
  (S : ShortComplex C) {F Y : C} (e : F ≅ S.X₁) (f : Y ⟶ S.X₃)

/-- The actual pullback extension, keeping the chosen coefficient object. -/
abbrev coefficientPullbackExtension : ShortComplex C :=
  ShortComplex.mk
    (e.hom ≫ pullback.lift S.f 0 (S.zero.trans (zero_comp).symm))
    (pullback.snd S.g f) (by rw [Category.assoc, pullback.lift_snd, comp_zero])

/-- Its middle map to the original extension preserves the original inclusion. -/
theorem coefficientPullbackExtension_f_fst :
    (coefficientPullbackExtension S e f).f ≫ pullback.fst S.g f = e.hom ≫ S.f := by
  change (e.hom ≫ pullback.lift S.f 0 _) ≫ pullback.fst S.g f = _
  rw [Category.assoc, pullback.lift_fst]

/-- Pullback preserves short exactness, including the original coefficient
identification; no new exactness hypothesis is imposed on the pullback. -/
theorem coefficientPullbackExtension_shortExact (hS : S.ShortExact) :
    (coefficientPullbackExtension S e f).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  let P := coefficientPullbackExtension S e f
  have hi : P.f ≫ pullback.fst S.g f = e.hom ≫ S.f :=
    coefficientPullbackExtension_f_fst S e f
  have : Mono P.f := mono_of_mono_fac hi
  have hk : IsLimit (KernelFork.ofι P.f P.zero) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hk' : (k ≫ pullback.fst S.g f) ≫ S.g = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact (congrArg (· ≫ f) hk).trans (zero_comp)
    obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hS.fIsKernel
      (k ≫ pullback.fst S.g f) hk'
    refine ⟨a ≫ e.inv, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hi, Category.assoc, e.inv_hom_id_assoc]
      exact ha
    · change ((a ≫ e.inv) ≫ P.f) ≫ P.g = k ≫ P.g
      rw [Category.assoc, P.zero, comp_zero, hk]
  exact
    { exact := P.exact_of_f_is_kernel hk
      mono_f := (show Mono P.f from inferInstance)
      epi_g := (show Epi (pullback.snd S.g f) from inferInstance) }

end EtaleFundamentalGroups.Cohomology
