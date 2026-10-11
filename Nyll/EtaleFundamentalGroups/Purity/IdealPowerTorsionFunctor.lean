/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# The ideal-power torsion functor and its injective-resolution complex

The functor takes the submodule of elements killed by a power of an ideal.
Its maps are restrictions of the original linear maps, so its inclusion into
the identity functor is natural and it is additive.  Applying it termwise to
an injective resolution gives the concrete complex used to compute derived
ideal-power torsion.
-/

noncomputable section

open CategoryTheory

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

/-- The submodule of elements annihilated by some power of `I`, functorially
in the coefficient module. -/
def idealPowerTorsionFunctor (I : Ideal R) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Ideal.primaryComponent M I)
  map f := ModuleCat.ofHom (Ideal.primaryComponent.map I f.hom)
  map_id M := by
    ext z
    rfl
  map_comp f g := by
    ext z
    rfl

instance (I : Ideal R) : (idealPowerTorsionFunctor I).Additive where
  map_add := by
    intro M N f g
    ext z
    rfl

/-- The canonical inclusion of power torsion into the original module. -/
def idealPowerTorsionInclusion (I : Ideal R) :
    idealPowerTorsionFunctor I ⟶ 𝟭 (ModuleCat.{u} R) where
  app M := ModuleCat.ofHom (Ideal.primaryComponent M I).subtype
  naturality _ _ f := by
    ext z
    rfl

/-- Applying ideal-power torsion to every term and differential. -/
def idealPowerTorsionComplex (I : Ideal R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((idealPowerTorsionFunctor I).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The torsion complex of an explicitly chosen injective resolution. -/
def derivedLocalCohomologyInjectiveComplex (I : Ideal R)
    {M : ModuleCat.{u} R} (J : InjectiveResolution M) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  idealPowerTorsionComplex I J.cocomplex

/-- The differential is the original differential restricted to torsion. -/
theorem idealPowerTorsionComplex_d_apply (I : Ideal R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (p q : ℕ)
    (z : (idealPowerTorsionComplex I K).X p) :
    ((show Ideal.primaryComponent (K.X q) I from
        ((idealPowerTorsionComplex I K).d p q) z) : K.X q) =
      K.d p q ((show Ideal.primaryComponent (K.X p) I from z) : K.X p) :=
  rfl

end EtaleFundamentalGroups.Purity

end
