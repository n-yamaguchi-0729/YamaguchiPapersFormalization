/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.BaseChange
import EtaleCohomology.Sites.ClosedNeighborhoods
import EtaleCohomology.Sites.ClosedImmersionStalks
import EtaleCohomology.Sites.PullbackStalks
import EtaleCohomology.Sites.RestrictionAdjunction
import EtaleCohomology.Sites.SheafFunctors
import SchemeTheory.Morphisms.ClosedImmersionLift
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Fully faithful direct image for a closed immersion

Initiality of pointed neighborhoods identifies restriction of maps to
skyscraper sheaves. The general site result then proves that the actual
counit of inverse image and direct image is an isomorphism on every stalk.
Consequently direct image is fully faithful. The canonical unit is an
isomorphism on stalks inside the closed subscheme and an epimorphism globally.

The schemes and commutative coefficient ring are arbitrary.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (R : Type u) [CommRing R]

/-- The canonical counit of a closed immersion is an isomorphism. -/
lemma etalePushforwardClosed_counit_isIso
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso ((etalePullbackPushforwardAdjunction i R).counit.app G) := by
  apply (((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' Z).jointlyReflectIsomorphisms
    (ModuleCat.{u} R)).isIso_iff _).mpr
  rintro ⟨_, ⟨z⟩⟩
  let s : Spec (.of (SeparableClosure (Z.residueField z))) ⟶ Z :=
    (Scheme.SpecToEquivOfField (SeparableClosure (Z.residueField z)) Z).symm
      ⟨z, CommRingCat.ofHom (algebraMap (Z.residueField z) _)⟩
  change IsIso ((Scheme.pointSmallEtale s).sheafFiber.map
    ((etalePullbackPushforwardAdjunction i R).counit.app G))
  let : RepresentablyFlat (etaleBaseChange i) := flat_of_preservesFiniteLimits _
  let : (Functor.Elements.precomp (etaleBaseChange i) (Scheme.pointSmallEtale s).fiber).Initial :=
    closedNeighborhoodBaseChange_initial i s
  exact Sites.restriction_counit_stalk_isIso (etaleBaseChange i)
    (etaleBaseChange_coverPreserving i) (Scheme.pointSmallEtale s) (ModuleCat.{u} R)
    (etalePullback i R) (etalePullbackPushforwardAdjunction i R) G

/-- Direct image along a closed immersion is fully faithful. -/
def etalePushforwardClosedFullyFaithful : (etalePushforward i R).FullyFaithful := by
  let : ∀ G, IsIso ((etalePullbackPushforwardAdjunction i R).counit.app G) :=
    etalePushforwardClosed_counit_isIso i R
  let : IsIso (etalePullbackPushforwardAdjunction i R).counit := NatIso.isIso_of_isIso_app _
  exact (etalePullbackPushforwardAdjunction i R).fullyFaithfulROfIsIsoCounit

/-- The canonical unit is an isomorphism on stalks inside the closed subscheme. -/
lemma etalePushforwardClosed_unit_stalk_isIso
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Z)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    IsIso ((Scheme.pointSmallEtale (s ≫ i)).sheafFiber.map
      ((etalePullbackPushforwardAdjunction i R).unit.app G)) := by
  apply (NatIso.isIso_map_iff (etalePullbackStalkIso i s R) _).mp
  change IsIso ((Scheme.pointSmallEtale s).sheafFiber.map
    ((etalePullback i R).map ((etalePullbackPushforwardAdjunction i R).unit.app G)))
  have : IsIso ((etalePullbackPushforwardAdjunction i R).counit.app
      ((etalePullback i R).obj G)) := etalePushforwardClosed_counit_isIso i R _
  have : IsIso ((etalePullback i R).map ((etalePullbackPushforwardAdjunction i R).unit.app G)) :=
    isIso_of_comp_hom_eq_id _ ((etalePullbackPushforwardAdjunction i R).left_triangle_components G)
  infer_instance

/-- The canonical unit gives the epimorphism at the end of open-closed localization. -/
instance etalePushforwardClosed_unit_epi
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    Epi ((etalePullbackPushforwardAdjunction i R).unit.app G) := by
  classical
  apply (((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectEpimorphisms
    (ModuleCat.{u} R)).epi_iff _).mpr
  rintro ⟨_, ⟨x⟩⟩
  let tx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  let z : Spec (.of (SeparableClosure (X.residueField x))) := Classical.choice inferInstance
  change Epi ((Scheme.pointSmallEtale tx).sheafFiber.map
    ((etalePullbackPushforwardAdjunction i R).unit.app G))
  by_cases h : tx z ∈ Set.range i
  · have hrange : Set.range tx ⊆ Set.range i := by
      rintro y ⟨a, rfl⟩
      rwa [Subsingleton.elim a z]
    obtain ⟨s, hs⟩ := IsClosedImmersion.exists_lift_of_isReduced_of_range_subset i tx hrange
    rw [← hs]
    have := etalePushforwardClosed_unit_stalk_isIso i R s G
    infer_instance
  · exact (etalePushforward_stalk_isZero_of_not_mem_range i R tx z h
      ((etalePullback i R).obj G)).epi _

end EtaleCohomology
