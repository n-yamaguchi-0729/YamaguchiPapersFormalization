/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1Extensions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The zero extension class and splitting

The actual connecting class of a short exact sequence vanishes precisely
when the quotient map has a section. This is the exact-sequence criterion
used to detect trivial degree-one cohomology classes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe w v u

namespace EtaleFundamentalGroups.Cohomology

/-- The connecting class is zero exactly when the short exact sequence splits
on its quotient. The section is obtained from the actual Ext exact sequence. -/
theorem extClass_eq_zero_iff_exists_section
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  constructor
  · intro h
    have hi : (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) = 0 :=
      (Ext.mk₀_id_comp hS.extClass).trans h
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS (Ext.mk₀ (𝟙 S.X₃))
      (zero_add 1) hi
    obtain ⟨s, hs⟩ := (Ext.mk₀_bijective S.X₃ S.X₂).surjective b
    refine ⟨s, (Ext.mk₀_bijective S.X₃ S.X₃).injective ?_⟩
    exact (Ext.mk₀_comp_mk₀ s S.g).symm.trans
      ((congrArg (fun c => c.comp (Ext.mk₀ S.g) (add_zero 0)) hs).trans hb)
  · rintro ⟨s, hs⟩
    calc
      hS.extClass = (Ext.mk₀ (s ≫ S.g)).comp hS.extClass (zero_add 1) := by
        rw [hs, Ext.mk₀_id_comp]
      _ = (Ext.mk₀ s).comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1))
          (zero_add 1) := (Ext.mk₀_comp_mk₀_assoc s S.g hS.extClass).symm
      _ = 0 := by rw [hS.comp_extClass, Ext.comp_zero]

end EtaleFundamentalGroups.Cohomology
