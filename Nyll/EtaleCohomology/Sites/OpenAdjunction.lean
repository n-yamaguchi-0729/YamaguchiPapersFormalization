/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.ExtensionByZero
import Nyll.EtaleCohomology.Sites.ExtensionByZeroStalks
import Nyll.EtaleCohomology.Sites.SheafAdjunction
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.EtaleCohomology.Sites.PullbackStalks
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Fully faithful adjoints for an open immersion

The fully faithful inclusion of the small étale sites makes the direct image
fully faithful. The adjoint triple `j_! ⊣ j^* ⊣ j_*` then proves that extension
by zero is fully faithful as well. Consequently the canonical unit
`F ⟶ j^*j_!F` is an isomorphism, by the general adjunction API.

The canonical counit `j_!j^*F ⟶ F` becomes an isomorphism after restriction.
The pullback stalk formula transfers this fact to each geometric stalk inside
the open subscheme. Outside, its source stalk is zero, so geometric stalks
show that the counit is a monomorphism. This supplies the first map of the
open-closed localization sequence with its actual adjunction, rather than
just a comparison between the objects at each stalk.

The schemes and commutative coefficient ring are arbitrary.
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (R : Type u) [CommRing R]

/-- Direct image along an open immersion is fully faithful. -/
def openEtalePushforwardFullyFaithful : (etalePushforward j R).FullyFaithful := by
  have : IsIso (openEtaleRestrictionPushforwardAdjunction j R).counit :=
    Sites.sheafAdjunction_counit_isIso (ModuleCat.{u} R)
      (openEtaleInclusionBaseChangeAdjunction j)
  exact (openEtaleRestrictionPushforwardAdjunction j R).fullyFaithfulROfIsIsoCounit

instance openEtalePushforward_full : (etalePushforward j R).Full :=
  (openEtalePushforwardFullyFaithful j R).full

instance openEtalePushforward_faithful : (etalePushforward j R).Faithful :=
  (openEtalePushforwardFullyFaithful j R).faithful

/-- Extension by zero is fully faithful, by the adjoint triple for an open immersion. -/
def etaleExtensionByZeroFullyFaithful : (etaleExtensionByZero j R).FullyFaithful :=
  (⟨etaleExtensionByZeroAdjunction j R, etalePullbackPushforwardAdjunction j R⟩ :
    Adjunction.Triple (etaleExtensionByZero j R) (etalePullback j R)
      (etalePushforward j R)).fullyFaithfulEquiv.symm (openEtalePushforwardFullyFaithful j R)

instance etaleExtensionByZero_full : (etaleExtensionByZero j R).Full :=
  (etaleExtensionByZeroFullyFaithful j R).full

instance etaleExtensionByZero_faithful : (etaleExtensionByZero j R).Faithful :=
  (etaleExtensionByZeroFullyFaithful j R).faithful

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U)

/-- The canonical counit is an isomorphism on stalks inside the open subscheme. -/
lemma etaleExtensionByZero_counit_stalk_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso ((Scheme.pointSmallEtale (s ≫ j)).sheafFiber.map
      ((etaleExtensionByZeroAdjunction j R).counit.app F)) := by
  apply (NatIso.isIso_map_iff (etalePullbackStalkIso j s R) _).mp
  change IsIso ((Scheme.pointSmallEtale s).sheafFiber.map
    ((etalePullback j R).map ((etaleExtensionByZeroAdjunction j R).counit.app F)))
  infer_instance

/-- The counit gives the monomorphism at the start of open-closed localization. -/
instance etaleExtensionByZero_counit_mono
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    Mono ((etaleExtensionByZeroAdjunction j R).counit.app F) := by
  apply (((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectMonomorphisms
    (ModuleCat.{u} R)).mono_iff _).mpr
  rintro ⟨_, ⟨x⟩⟩
  let tx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  change Mono ((Scheme.pointSmallEtale tx).sheafFiber.map
    ((etaleExtensionByZeroAdjunction j R).counit.app F))
  by_cases h : ∃ r : Spec (.of (SeparableClosure (X.residueField x))) ⟶ U, r ≫ j = tx
  · obtain ⟨r, hr⟩ := h
    rw [← hr]
    have := etaleExtensionByZero_counit_stalk_isIso j R r F
    infer_instance
  · have hn : ∀ r : Spec (.of (SeparableClosure (X.residueField x))) ⟶ U, r ≫ j ≠ tx :=
      fun r hr => h ⟨r, hr⟩
    exact (etaleExtensionByZero_stalk_isZero j R tx hn ((etalePullback j R).obj F)).mono _

end EtaleCohomology
