/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Comparing representatives of a degree-one extension class

Compatibility of the actual derived extension classes with a kernel map gives
a morphism of short exact sequences which is the identity on the quotient. The morphism is
constructed using the two Ext exact sequences: first extend the kernel map,
then correct the induced quotient endomorphism. Thus independence of a chosen
extension representative does not require an additional comparison assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u

namespace EtaleFundamentalGroups.Cohomology

/-- Compatibility of derived extension classes gives a comparison with the
specified kernel map and identity quotient map. In particular, equal classes
have an isomorphism inducing the identity on both endpoints. -/
theorem exists_extension_comparison_of_extClass_naturality
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {K₁ K₂ Q E₁ E₂ : C} (α : K₁ ⟶ K₂)
    (i₁ : K₁ ⟶ E₁) (p₁ : E₁ ⟶ Q) (z₁ : i₁ ≫ p₁ = 0)
    (i₂ : K₂ ⟶ E₂) (p₂ : E₂ ⟶ Q) (z₂ : i₂ ≫ p₂ = 0)
    (h₁ : (ShortComplex.mk i₁ p₁ z₁).ShortExact)
    (h₂ : (ShortComplex.mk i₂ p₂ z₂).ShortExact)
    (he : h₁.extClass.comp (Ext.mk₀ α) (add_zero 1) = h₂.extClass) :
    ∃ f : E₁ ⟶ E₂, i₁ ≫ f = α ≫ i₂ ∧ f ≫ p₂ = p₁ := by
  have hz : h₁.extClass.comp (Ext.mk₀ (α ≫ i₂)) (add_zero 1) = 0 := by
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero, he]
    exact h₂.extClass_comp
  obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₁ h₁ E₂
    (Ext.mk₀ (α ≫ i₂)) (add_zero 1) hz
  obtain ⟨f, hf⟩ := (Ext.mk₀_bijective E₁ E₂).surjective b
  have hi : i₁ ≫ f = α ≫ i₂ := (Ext.mk₀_bijective K₁ E₂).injective
    ((Ext.mk₀_comp_mk₀ i₁ f).symm.trans
      ((congrArg (fun c => (Ext.mk₀ i₁).comp c (zero_add 0)) hf).trans hb))
  have hip : i₁ ≫ (f ≫ p₂) = 0 := by
    rw [← Category.assoc, hi, Category.assoc, z₂, comp_zero]
  obtain ⟨β, hβ⟩ := CokernelCofork.IsColimit.desc' h₁.gIsCokernel (f ≫ p₂) hip
  change Q ⟶ Q at β
  change p₁ ≫ β = f ≫ p₂ at hβ
  let φ : ShortComplex.mk i₁ p₁ z₁ ⟶ ShortComplex.mk i₂ p₂ z₂ :=
    { τ₁ := α
      τ₂ := f
      τ₃ := β
      comm₁₂ := hi.symm
      comm₂₃ := hβ.symm }
  have hn := ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ
  change h₁.extClass.comp (Ext.mk₀ α) (add_zero 1) =
    (Ext.mk₀ β).comp h₂.extClass (zero_add 1) at hn
  rw [he] at hn
  have hd : (Ext.mk₀ (β - 𝟙 Q)).comp h₂.extClass (zero_add 1) = 0 := by
    rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp,
      Ext.mk₀_id_comp, ← hn, add_neg_cancel]
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₃ Q h₂ (Ext.mk₀ (β - 𝟙 Q))
    (zero_add 1) hd
  obtain ⟨s, hs⟩ := (Ext.mk₀_bijective Q E₂).surjective c
  have hsp : s ≫ p₂ = β - 𝟙 Q := (Ext.mk₀_bijective Q Q).injective
    ((Ext.mk₀_comp_mk₀ s p₂).symm.trans
      ((congrArg (fun d => d.comp (Ext.mk₀ p₂) (add_zero 0)) hs).trans hc))
  refine ⟨f - p₁ ≫ s, ?_, ?_⟩
  · rw [Preadditive.comp_sub, ← Category.assoc, z₁, zero_comp, sub_zero]
    exact hi
  · rw [Preadditive.sub_comp, Category.assoc, hsp, Preadditive.comp_sub,
      Category.comp_id, ← hβ, sub_sub_cancel]

end EtaleFundamentalGroups.Cohomology
