/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Linear duals with injective values and homology

The contravariant linear Hom functor with injective values is exact.
This is obtained from preadditive Yoneda exactness by the forgetful
functor, which reflects finite limits and colimits. Applying the exact
functor to an opposite complex identifies its homology with the linear
dual of the original homology, without changing the scalar ring.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u v

open CategoryTheory Limits Opposite

variable {R : Type u} [CommRing R]

/-- Linear Yoneda with injective values preserves homology. The property
is supplied explicitly instead of adding a competing global instance. -/
theorem linearYoneda_preservesHomology_of_injective
    (E : ModuleCat.{u} R) [Module.Injective R E] :
    ((linearYoneda R (ModuleCat.{u} R)).obj E).PreservesHomology := by
  let : CategoryTheory.Injective E := Module.injective_object_of_injective_module R E
  let F : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
    (linearYoneda R (ModuleCat.{u} R)).obj E
  let U : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let : PreservesFiniteLimits (preadditiveYonedaObj E) :=
    Functor.preservesFiniteLimits_of_preservesHomology (preadditiveYonedaObj E)
  let : PreservesFiniteLimits (F ⋙ U) := by
    change PreservesFiniteLimits
      (preadditiveYonedaObj E ⋙ forget₂ (ModuleCat.{u} (End E)) AddCommGrpCat.{u})
    infer_instance
  let : PreservesFiniteColimits (F ⋙ U) := by
    change PreservesFiniteColimits
      (preadditiveYonedaObj E ⋙ forget₂ (ModuleCat.{u} (End E)) AddCommGrpCat.{u})
    infer_instance
  let : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F U
  let : PreservesFiniteColimits F := preservesFiniteColimits_of_reflects_of_preserves F U
  exact Functor.preservesHomologyOfExact F

/-- The homology of a reversed linear-dual short complex is the linear
dual of the original homology when the values are injective. -/
def injectiveLinearDualShortComplexHomologyIso
    (E : ModuleCat.{u} R) [Module.Injective R E]
    (S : ShortComplex (ModuleCat.{u} R)) :
    (S.op.map ((linearYoneda R (ModuleCat.{u} R)).obj E)).homology ≅
      ModuleCat.of R (S.homology →ₗ[R] E) := by
  let F : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
    (linearYoneda R (ModuleCat.{u} R)).obj E
  letI : F.PreservesHomology := linearYoneda_preservesHomology_of_injective E
  exact S.op.mapHomologyIso F ≪≫ F.mapIso S.homologyOpIso ≪≫
    (ModuleCat.homLinearEquiv (R := R) (S := R) (M := S.homology) (N := E)).toModuleIso

/-- The complex obtained by reversing arrows and applying the linear
Hom functor with values in the given module. -/
def linearDualComplex
    (E : ModuleCat.{u} R) {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (ModuleCat.{u} R) c.symm :=
  (((linearYoneda R (ModuleCat.{u} R)).obj E).mapHomologicalComplex c.symm).obj K.op

/-- Homology commutes with the linear dual into an injective module,
with the complex shape reversed. -/
def injectiveLinearDualComplexHomologyIso
    (E : ModuleCat.{u} R) [Module.Injective R E]
    {ι : Type v} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (j : ι) :
    (linearDualComplex E K).homology j ≅ ModuleCat.of R (K.homology j →ₗ[R] E) := by
  let F : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
    (linearYoneda R (ModuleCat.{u} R)).obj E
  letI : F.PreservesHomology := linearYoneda_preservesHomology_of_injective E
  exact (K.op.sc j).mapHomologyIso F ≪≫ F.mapIso (K.homologyOp j) ≪≫
    (ModuleCat.homLinearEquiv (R := R) (S := R) (M := K.homology j) (N := E)).toModuleIso

end EtaleFundamentalGroups.Purity

end
