/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCategories.FiberFunctorExactness
import EtaleFundamentalGroups.GaloisCategories.FiberFunctorUniqueness

/-!
# Comparison of exact functors on a Galois category

An exact functor from a Galois category to finite sets is isomorphic to any
chosen fiber functor.  As a consequence, exact functors between Galois
categories commute with fiber functors up to isomorphism.
-/

universe u₁ u₂ v₁ v₂ w

noncomputable section

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]

/-- Any exact finite-set-valued functor on a Galois category is isomorphic to
a chosen fiber functor. -/
theorem nonempty_iso_of_exact
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (P : C ⥤ FintypeCat.{w})
    [PreservesFiniteLimits P] [PreservesFiniteColimits P] :
    Nonempty (F ≅ P) := by
  let S :=
    FintypeCat.uSwitchEquivalence.{w, max u₁ u₂ w}
  let F' := F ⋙ S.functor
  let P' := P ⋙ S.functor
  let E := functorToContAction F'
  let A := ContAction FintypeCat.{max u₁ u₂ w} (Aut F')
  let U := forget₂ A FintypeCat
  let Q := E.asEquivalence.inverse ⋙ P'
  let : FiberFunctor F' :=
    FiberFunctor.comp_right _
  let : PreservesFiniteLimits P' := by
    apply comp_preservesFiniteLimits
  let : PreservesFiniteColimits P' := by
    apply comp_preservesFiniteColimits
  let : PreservesFiniteLimits Q := by
    apply comp_preservesFiniteLimits
  let : PreservesFiniteColimits Q := by
    apply comp_preservesFiniteColimits
  obtain ⟨e⟩ :=
    FiniteContinuousAction.nonempty_iso_forget_of_exact
      (Aut F') Q
  let eF : E ⋙ U ≅ F' :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  let eP : E ⋙ Q ≅ P' :=
    (Functor.associator E E.asEquivalence.inverse P').symm ≪≫
      Functor.isoWhiskerRight E.asEquivalence.unitIso.symm P' ≪≫
        Functor.leftUnitor P'
  let e' : F' ≅ P' :=
    eF.symm ≪≫ Functor.isoWhiskerLeft E e ≪≫ eP
  exact ⟨
    ((Functor.FullyFaithful.ofFullyFaithful S.functor).whiskeringRight C).preimageIso e'⟩

variable {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']

/-- An exact functor between Galois categories commutes with chosen fiber
functors up to isomorphism. -/
@[stacks 0BN5 "an exact functor commutes with chosen fiber functors up to isomorphism"]
theorem nonempty_iso_comp_of_exact
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']
    (H : C ⥤ C')
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
    Nonempty (H ⋙ F' ≅ F) := by
  let : PreservesFiniteColimits F' :=
    FiberFunctor.preservesFiniteColimits F'
  let : PreservesFiniteLimits (H ⋙ F') := by
    apply comp_preservesFiniteLimits
  let : PreservesFiniteColimits (H ⋙ F') := by
    apply comp_preservesFiniteColimits
  exact Nonempty.map Iso.symm
    (nonempty_iso_of_exact F (H ⋙ F'))

end CategoryTheory.PreGaloisCategory
