/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.LocallyConstant
import EtaleCohomology.Sites.ClosedImmersionStalks
import EtaleCohomology.Sites.ExtensionByZeroStalks
import EtaleCohomology.Sites.PullbackStalks
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Sites.Point.Conservative
import EtaleCohomology.Sites.ExtensionByZero
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Vanishing away from the support

An inverse image disjoint from the image of an open or closed immersion
annihilates extension by zero or closed direct image, respectively. These
are statements about the actual sheaves, detected by geometric stalks.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits ZeroObject
namespace EtaleCohomology
variable {X Y U Z : Scheme.{u}} {R : Type u} [CommRing R]

/-- A zero sheaf has the zero finite type constant model. -/
lemma isEtaleFiniteTypeLocallyConstant_of_isZero
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (hG : IsZero G) :
    IsEtaleFiniteTypeLocallyConstant R G := by
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)
  have : PreservesFiniteLimits C := by
    change PreservesFiniteLimits
      (Functor.const X.Etaleᵒᵖ ⋙ presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R))
    infer_instance
  have : Subsingleton (0 : ModuleCat.{u} R) := ModuleCat.subsingleton_of_isZero (isZero_zero _)
  exact (IsEtaleLocallyConstantWith.constant (0 : ModuleCat.{u} R)
    (show Module.Finite R (0 : ModuleCat.{u} R) from inferInstance)).of_iso
    ((C.map_isZero (isZero_zero _)).iso hG)

/-- Pullback away from an open immersion's image annihilates its zero extension. -/
lemma etalePullback_extensionByZero_isZero_of_disjoint
    (f : Y ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (h : Disjoint (Set.range f) (Set.range j))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u} R)) :
    IsZero ((etalePullback f R).obj ((etaleExtensionByZero j R).obj G)) := by
  classical
  rw [IsZero.iff_id_eq_zero]
  apply ((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' Y).jointlyFaithful
    (ModuleCat.{u} R)).map_injective
  rintro ⟨_, ⟨y⟩⟩
  let s : Spec (.of (SeparableClosure (Y.residueField y))) ⟶ Y :=
    (Scheme.SpecToEquivOfField (SeparableClosure (Y.residueField y)) Y).symm
      ⟨y, CommRingCat.ofHom (algebraMap (Y.residueField y) _)⟩
  let z : Spec (.of (SeparableClosure (Y.residueField y))) := Classical.choice inferInstance
  have hn : (s ≫ f) z ∉ Set.range j :=
    fun hz => Set.disjoint_left.mp h ⟨s z, rfl⟩ hz
  have hz := (etaleExtensionByZero_stalk_isZero_of_not_mem_range j R (s ≫ f) z hn G).of_iso
    ((etalePullbackStalkIso f s R).app ((etaleExtensionByZero j R).obj G))
  change (Scheme.pointSmallEtale s).sheafFiber.map (𝟙 _) =
    (Scheme.pointSmallEtale s).sheafFiber.map 0
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz.eq_of_src _ _

/-- Pullback away from a closed immersion's image annihilates its direct image. -/
lemma etalePullback_closedPushforward_isZero_of_disjoint
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    (h : Disjoint (Set.range f) (Set.range i))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) :
    IsZero ((etalePullback f R).obj ((etalePushforward i R).obj G)) := by
  classical
  rw [IsZero.iff_id_eq_zero]
  apply ((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' Y).jointlyFaithful
    (ModuleCat.{u} R)).map_injective
  rintro ⟨_, ⟨y⟩⟩
  let s : Spec (.of (SeparableClosure (Y.residueField y))) ⟶ Y :=
    (Scheme.SpecToEquivOfField (SeparableClosure (Y.residueField y)) Y).symm
      ⟨y, CommRingCat.ofHom (algebraMap (Y.residueField y) _)⟩
  let z : Spec (.of (SeparableClosure (Y.residueField y))) := Classical.choice inferInstance
  have hn : (s ≫ f) z ∉ Set.range i :=
    fun hz => Set.disjoint_left.mp h ⟨s z, rfl⟩ hz
  have hz := (etalePushforward_stalk_isZero_of_not_mem_range i R (s ≫ f) z hn G).of_iso
    ((etalePullbackStalkIso f s R).app ((etalePushforward i R).obj G))
  change (Scheme.pointSmallEtale s).sheafFiber.map (𝟙 _) =
    (Scheme.pointSmallEtale s).sheafFiber.map 0
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hz.eq_of_src _ _

end EtaleCohomology
