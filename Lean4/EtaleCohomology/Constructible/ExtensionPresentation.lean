/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# A cokernel presentation of an extension

If an epimorphism onto the quotient of a short exact sequence lifts to its
middle term, the middle term is a cokernel of a map from the kernel of that
epimorphism to the sum of its source and the subobject. This supplies the
presentation used in the local constancy proof for extensions.
-/

noncomputable section
open CategoryTheory Limits
namespace EtaleCohomology

/-- A lifted epimorphism gives an actual cokernel presentation of the middle term. -/
theorem exists_extension_cokernel_presentation
    {C : Type*} [Category* C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact)
    {P : C} (q : P ⟶ S.X₃) [Epi q] (t : P ⟶ S.X₂) (ht : t ≫ S.g = q) :
    ∃ a : kernel q ⟶ S.X₁ ⊞ P, Nonempty (cokernel a ≅ S.X₂) := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  have hkt : (kernel.ι q ≫ t) ≫ S.g = 0 := by
    rw [Category.assoc, ht, kernel.condition]
  let d := hS.exact.lift (kernel.ι q ≫ t) hkt
  have hd : d ≫ S.f = kernel.ι q ≫ t := hS.exact.lift_f _ _
  let a : kernel q ⟶ S.X₁ ⊞ P := biprod.lift (-d) (kernel.ι q)
  let b : S.X₁ ⊞ P ⟶ S.X₂ := biprod.desc S.f t
  have hab : a ≫ b = 0 := by
    dsimp only [a, b]
    rw [biprod.lift_desc, Preadditive.neg_comp, hd, neg_add_cancel]
  have ha : a ≫ biprod.snd = kernel.ι q := biprod.lift_snd _ _
  have : Mono a := mono_of_mono_fac ha
  have hb : b ≫ S.g = biprod.snd ≫ q := by
    apply biprod.hom_ext'
    · simp only [b, biprod.inl_desc_assoc, S.zero, biprod.inl_snd_assoc, zero_comp]
    · simp only [b, biprod.inr_desc_assoc, ht, biprod.inr_snd_assoc]
  have hk : IsLimit (KernelFork.ofι a hab) := by
    apply KernelFork.IsLimit.ofι'
    intro T s hs
    have hsq : (s ≫ biprod.snd) ≫ q = 0 := by
      rw [Category.assoc, ← hb, ← Category.assoc, hs, zero_comp]
    refine ⟨kernel.lift q (s ≫ biprod.snd) hsq, ?_⟩
    apply biprod.hom_ext
    · apply (cancel_mono S.f).mp
      have hz : (s ≫ biprod.fst) ≫ S.f + (s ≫ biprod.snd) ≫ t = 0 := by
        rw [Category.assoc, Category.assoc, ← Preadditive.comp_add]
        rw [← biprod.desc_eq]
        exact hs
      simp only [Category.assoc, a, biprod.lift_fst, Preadditive.neg_comp,
        Preadditive.comp_neg, hd, kernel.lift_ι_assoc]
      simpa only [Category.assoc, Preadditive.neg_comp, Preadditive.comp_neg] using
        (eq_neg_of_add_eq_zero_left hz).symm
    · rw [Category.assoc, ha, kernel.lift_ι]
  have : Epi b := by
    apply Preadditive.epi_of_cancel_zero
    intro T v hv
    have hfv : S.f ≫ v = 0 := by
      rw [← biprod.inl_desc S.f t, Category.assoc]
      exact (congrArg (biprod.inl ≫ ·) hv).trans (comp_zero)
    let w := hS.exact.desc v hfv
    have hw : S.g ≫ w = v := hS.exact.g_desc _ _
    have hqw : q ≫ w = 0 := by
      rw [← ht, Category.assoc, hw, ← biprod.inr_desc S.f t, Category.assoc]
      exact (congrArg (biprod.inr ≫ ·) hv).trans (comp_zero)
    have hw0 : w = 0 := zero_of_epi_comp q hqw
    rw [← hw, hw0, comp_zero]
  let T := ShortComplex.mk a b hab
  have hT : T.Exact := T.exact_of_f_is_kernel hk
  exact ⟨a, ⟨(cokernelIsCokernel a).coconePointUniqueUpToIso hT.gIsCokernel⟩⟩

end EtaleCohomology
