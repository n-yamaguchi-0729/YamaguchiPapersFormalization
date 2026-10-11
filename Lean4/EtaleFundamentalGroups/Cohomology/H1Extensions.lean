/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Extensions representing étale cohomology in degree one

Every class in the existing derived-functor étale cohomology `Sheaf.H F 1`
is represented by a short exact sequence with kernel `F` and quotient the
constant integer sheaf. The sequence is constructed by embedding `F` into an
injective sheaf, lifting the class through the connecting morphism, and taking
an actual pullback. No extension or cohomology comparison is assumed.

This is the extension construction used in the comparison of degree-one
cohomology with torsors; it does not yet assert the fundamental-group comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe w v u

namespace EtaleFundamentalGroups.Cohomology

private abbrev pullbackExtension {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) {Y : C} (f : Y ⟶ S.X₃) : ShortComplex C :=
  ShortComplex.mk
    (pullback.lift S.f 0 (S.zero.trans (zero_comp).symm))
    (pullback.snd S.g f) (pullback.lift_snd _ _ _)

private lemma pullbackExtension_shortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) {Y : C} (f : Y ⟶ S.X₃) :
    (pullbackExtension S f).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  let i : S.X₁ ⟶ pullback S.g f :=
    pullback.lift S.f 0 (S.zero.trans (zero_comp).symm)
  have hi : i ≫ pullback.fst S.g f = S.f := pullback.lift_fst _ _ _
  have : Mono i := mono_of_mono_fac hi
  have hk : IsLimit (KernelFork.ofι i (pullback.lift_snd _ _ _)) := by
    apply KernelFork.IsLimit.ofι'
    intro Z k hk
    have hk' : (k ≫ pullback.fst S.g f) ≫ S.g = 0 := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hk, zero_comp]
    obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift' hS.fIsKernel
      (k ≫ pullback.fst S.g f) hk'
    refine ⟨a, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hi]
      exact ha
    · rw [Category.assoc, pullback.lift_snd, comp_zero, hk]
  exact
    { exact := (pullbackExtension S f).exact_of_f_is_kernel hk
      mono_f := (show Mono i from inferInstance)
      epi_g := (show Epi (pullback.snd S.g f) from inferInstance) }

private def pullbackExtensionMap {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) {Y : C} (f : Y ⟶ S.X₃) : pullbackExtension S f ⟶ S where
  τ₁ := 𝟙 S.X₁
  τ₂ := pullback.fst S.g f
  τ₃ := f
  comm₁₂ := by
    change 𝟙 S.X₁ ≫ S.f = _
    rw [Category.id_comp, pullback.lift_fst]
  comm₂₃ := pullback.condition

private theorem exists_extension_of_ext_one
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
    {X Y : C} (a : Ext.{w} X Y 1) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ X) (h : i ≫ p = 0)
      (hs : (ShortComplex.mk i p h).ShortExact), hs.extClass = a := by
  let S : ShortComplex C := ShortComplex.cokernelSequence (Injective.ι Y)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact (Injective.ι Y)
      mono_f := (show Mono (Injective.ι Y) from inferInstance) }
  have : Injective S.X₂ := (show Injective (Injective.under Y) from inferInstance)
  have ha : a.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective _
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ X hS a ha (n₀ := 0) (by omega)
  obtain ⟨f, hf⟩ := (Ext.mk₀_bijective X S.X₃).surjective b
  let P := pullbackExtension S f
  have hP : P.ShortExact := pullbackExtension_shortExact hS f
  refine ⟨P.X₂, P.f, P.g, P.zero, hP, ?_⟩
  have hn := ShortComplex.ShortExact.extClass_naturality hP hS
    (pullbackExtensionMap S f)
  change hP.extClass.comp (Ext.mk₀ (𝟙 Y)) (add_zero 1) =
    (Ext.mk₀ f).comp hS.extClass (zero_add 1) at hn
  exact (Ext.comp_mk₀_id hP.extClass).symm.trans
    (hn.trans ((congrArg (fun c => c.comp hS.extClass (zero_add 1)) hf).trans hb))


/-- Every actual étale `H¹` class is represented by a short exact extension
of the constant integer sheaf. This needs no connectedness, finiteness,
normality, or hypothesis on the characteristic of the scheme. -/
theorem exists_h1_extension (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (a : Sheaf.H.{u} F 1) :
    ∃ (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (i : F ⟶ E)
      (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))
      (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact), hs.extClass = a :=
  exists_extension_of_ext_one a

end EtaleFundamentalGroups.Cohomology
