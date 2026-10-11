/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Exactness in the coefficients of a flat tensor complex

Tensoring every term of a fixed complex defines a functor in the
coefficient module. When all its terms are flat, coefficient short exact
sequences remain short exact sequences of complexes. Consequently an
injective acyclicity result gives the usual cohomology dimension shift.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

/-- Tensor coefficients of a fixed nonnegative cochain complex. -/
def tensorComplexCoefficientFunctor (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj M := ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  map f :=
    { f := fun n => f ▷ K.X n
      comm' := fun i j _ => (whisker_exchange f (K.d i j)).symm }
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact id_whiskerRight M (K.X n)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact comp_whiskerRight f g (K.X n)

instance (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    (tensorComplexCoefficientFunctor K).Additive where
  map_add := by
    intro M N f g
    apply HomologicalComplex.Hom.ext
    funext n
    exact MonoidalPreadditive.add_whiskerRight (X := K.X n) f g

/-- Flat terms preserve each coefficient short exact sequence. -/
theorem tensorComplexCoefficientFunctor_shortExact
    (K : CochainComplex (ModuleCat.{u} R) ℕ) [∀ n, Module.Flat R (K.X n)]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.map (tensorComplexCoefficientFunctor K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  change (S.map (tensorRight (K.X n))).ShortExact
  refine ShortComplex.ShortExact.mk'
    (Module.Flat.rTensor_shortComplex_exact (K.X n) S hS.exact) ?_ ?_
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := K.X n) S.f.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.rTensor_surjective (K.X n)
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)

end EtaleFundamentalGroups.Purity

end
