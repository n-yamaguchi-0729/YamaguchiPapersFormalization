/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.ClosedAdjunction
import EtaleCohomology.Sites.ClosedImmersionStalks
import EtaleCohomology.Sites.ExtensionByZero
import EtaleCohomology.Sites.ExtensionByZeroStalks
import EtaleCohomology.Sites.OpenAdjunction
import EtaleCohomology.Sites.SheafFunctors
import EtaleCohomology.Sites.Stalks
import SchemeTheory.Morphisms.ClosedImmersionLift
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Open-closed localization for étale coefficient sheaves

For a closed immersion and its complementary open immersion, the actual
adjunction counit and unit give the short exact sequence
`0 ⟶ j_!j^*G ⟶ G ⟶ i_*i^*G ⟶ 0`.
The composite is zero and exactness is checked on all geometric stalks.
No base field, noetherian, finite-type, or constructibility hypothesis is used.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X Z U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  (hcompl : Set.range j = (Set.range i)ᶜ) (R : Type u) [CommRing R]

include hcompl in
/-- The adjunction maps in localization compose to zero. -/
lemma openClosed_counit_comp_unit
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (etaleExtensionByZeroAdjunction j R).counit.app G ≫
      (etalePullbackPushforwardAdjunction i R).unit.app G = 0 := by
  classical
  apply ((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyFaithful
    (ModuleCat.{u} R)).map_injective
  rintro ⟨_, ⟨x⟩⟩
  let tx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  let z : Spec (.of (SeparableClosure (X.residueField x))) := Classical.choice inferInstance
  change (Scheme.pointSmallEtale tx).sheafFiber.map _ = (Scheme.pointSmallEtale tx).sheafFiber.map _
  by_cases h : tx z ∈ Set.range i
  · have hj : tx z ∉ Set.range j := by
      rw [hcompl]
      exact fun hn => hn h
    exact (etaleExtensionByZero_stalk_isZero_of_not_mem_range j R tx z hj
      ((etalePullback j R).obj G)).eq_of_src _ _
  · exact (etalePushforward_stalk_isZero_of_not_mem_range i R tx z h
      ((etalePullback i R).obj G)).eq_of_tgt _ _

/-- The canonical three-term complex for an open and its closed complement. -/
def openClosedLocalizationComplex
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  ShortComplex.mk ((etaleExtensionByZeroAdjunction j R).counit.app G)
    ((etalePullbackPushforwardAdjunction i R).unit.app G)
    (openClosed_counit_comp_unit j i hcompl R G)

/-- Open-closed localization is a short exact sequence of étale coefficient sheaves. -/
lemma openClosedLocalization_shortExact
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (openClosedLocalizationComplex j i hcompl R G).ShortExact := by
  classical
  refine
    { exact := ?_
      mono_f := etaleExtensionByZero_counit_mono j R G
      epi_g := etalePushforwardClosed_unit_epi i R G }
  apply (exact_iff_residueStalk X R _).mpr
  intro x
  let tx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  let z : Spec (.of (SeparableClosure (X.residueField x))) := Classical.choice inferInstance
  let S := (openClosedLocalizationComplex j i hcompl R G).map
    (Scheme.pointSmallEtale tx).sheafFiber
  change S.Exact
  by_cases h : tx z ∈ Set.range i
  · have hj : tx z ∉ Set.range j := by
      rw [hcompl]
      exact fun hn => hn h
    have hz : IsZero S.X₁ := etaleExtensionByZero_stalk_isZero_of_not_mem_range j R tx z hj
      ((etalePullback j R).obj G)
    apply (S.exact_iff_mono (hz.eq_of_src _ _)).mpr
    change Mono ((Scheme.pointSmallEtale tx).sheafFiber.map
      ((etalePullbackPushforwardAdjunction i R).unit.app G))
    have hrange : Set.range tx ⊆ Set.range i := by
      rintro y ⟨a, rfl⟩
      rwa [Subsingleton.elim a z]
    obtain ⟨s, hs⟩ := IsClosedImmersion.exists_lift_of_isReduced_of_range_subset i tx hrange
    rw [← hs]
    have := etalePushforwardClosed_unit_stalk_isIso i R s G
    infer_instance
  · have hz : IsZero S.X₃ := etalePushforward_stalk_isZero_of_not_mem_range i R tx z h
      ((etalePullback i R).obj G)
    apply (S.exact_iff_epi (hz.eq_of_tgt _ _)).mpr
    change Epi ((Scheme.pointSmallEtale tx).sheafFiber.map
      ((etaleExtensionByZeroAdjunction j R).counit.app G))
    have hrange : Set.range tx ⊆ Set.range j := by
      rw [hcompl]
      rintro y ⟨a, rfl⟩
      change tx a ∉ Set.range i
      rwa [Subsingleton.elim a z]
    let s := IsOpenImmersion.lift j tx hrange
    have hs : s ≫ j = tx := IsOpenImmersion.lift_fac j tx hrange
    rw [← hs]
    have := etaleExtensionByZero_counit_stalk_isIso j R s G
    infer_instance

end EtaleCohomology
