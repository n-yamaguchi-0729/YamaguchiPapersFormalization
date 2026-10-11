/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.BaseChange
import EtaleCohomology.Sites.SheafFunctors
import EtaleCohomology.Sites.Stalks
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Geometric stalks of inverse image

The pullback adjunction for over categories identifies geometric lifts through
base change. This identifies the corresponding points of the small étale site
and supplies the smallness needed for their stalks.

Taking mates under the constructed inverse-image/direct-image adjunction and
the stalk/skyscraper adjunction gives the stalk formula for inverse image.
Geometric stalks then detect preservation of short exact sequences.
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- Geometric lifts through a base change are lifts of the composite geometric point. -/
def geometricFiberBaseChangeIso :
    etaleBaseChange f ⋙ (Scheme.pointSmallEtale s).fiber ≅
      (Scheme.pointSmallEtale (s ≫ f)).fiber :=
  (CategoryTheory.Functor.isoWhiskerLeft (Scheme.Etale.forget Y)
    ((CategoryTheory.Over.mapPullbackAdj f).compCoyonedaIso.app (op (Over.mk s)))).symm

instance : InitiallySmall.{u}
    (etaleBaseChange f ⋙ (Scheme.pointSmallEtale s).fiber).Elements := by
  let : InitiallySmall.{u}
      (CategoryTheory.Functor.elementsFunctor.obj (Scheme.pointSmallEtale (s ≫ f)).fiber) :=
    (Scheme.pointSmallEtale (s ≫ f)).initiallySmall
  let e := Cat.equivOfIso (CategoryTheory.Functor.elementsFunctor.mapIso
    (geometricFiberBaseChangeIso f s))
  let : e.inverse.Initial := CategoryTheory.Functor.initial_of_adjunction e.symm.toAdjunction
  -- Infer the bundled category from the equivalence before returning to Elements.
  have h := initiallySmall_of_initial_of_initiallySmall.{u} e.inverse
  exact h

local instance : RepresentablyFlat (etaleBaseChange f) := flat_of_preservesFiniteLimits _

/-- The inverse image of the site point is the composite geometric point. -/
def geometricPointComapIso :
    (Scheme.pointSmallEtale s).comap (etaleBaseChange f) (etaleBaseChange_coverPreserving f) ≅
      Scheme.pointSmallEtale (s ≫ f) where
  hom := ⟨(geometricFiberBaseChangeIso f s).inv⟩
  inv := ⟨(geometricFiberBaseChangeIso f s).hom⟩
  hom_inv_id := by
    apply GrothendieckTopology.Point.Hom.ext
    exact (geometricFiberBaseChangeIso f s).hom_inv_id
  inv_hom_id := by
    apply GrothendieckTopology.Point.Hom.ext
    exact (geometricFiberBaseChangeIso f s).inv_hom_id

variable (R : Type u) [CommRing R]

/-- The stalk at the comapped geometric point is the stalk at its composite point. -/
def geometricComapSheafFiberIso :
    ((Scheme.pointSmallEtale s).comap (etaleBaseChange f)
      (etaleBaseChange_coverPreserving f)).sheafFiber (A := ModuleCat.{u} R) ≅
      (Scheme.pointSmallEtale (s ≫ f)).sheafFiber where
  hom := (geometricPointComapIso f s).inv.sheafFiber
  inv := (geometricPointComapIso f s).hom.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]

/-- The geometric stalk of inverse image is the stalk at the composite geometric point. -/
def etalePullbackStalkIso :
    etalePullback f R ⋙ (Scheme.pointSmallEtale s).sheafFiber ≅
      (Scheme.pointSmallEtale (s ≫ f)).sheafFiber :=
  ((conjugateIsoEquiv
    ((etalePullbackPushforwardAdjunction f R).comp
      (Scheme.pointSmallEtale s).skyscraperSheafAdjunction)
    ((Scheme.pointSmallEtale s).comap (etaleBaseChange f)
      (etaleBaseChange_coverPreserving f)).skyscraperSheafAdjunction).symm
    ((Scheme.pointSmallEtale s).skyscraperSheafFunctorCompSheafPushforwardContinuous
      (etaleBaseChange f) (etaleBaseChange_coverPreserving f) (ModuleCat.{u} R))).symm ≪≫
    geometricComapSheafFiberIso f s R

/-- Inverse image on the small étale sites preserves short exact sequences. -/
lemma etalePullback_shortExact
    (S : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)))
    (hS : S.ShortExact) : (S.map (etalePullback f R)).ShortExact := by
  apply (shortExact_iff_residueStalk X R _).mpr
  intro x
  let sx : Spec (.of (SeparableClosure (X.residueField x))) ⟶ X :=
    (Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (etalePullbackStalkIso f sx R).symm)
    (hS.map_of_exact (Scheme.pointSmallEtale (sx ≫ f)).sheafFiber)

instance etalePullback_additive : (etalePullback f R).Additive := by
  let : PreservesBinaryBiproducts (etalePullback f R) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts (etalePullback f R)
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts (etalePullback f R)

instance etalePullback_preservesFiniteLimits : PreservesFiniteLimits (etalePullback f R) := by
  apply (CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (etalePullback f R)).mpr
  intro S hS
  have h := etalePullback_shortExact f R S hS
  exact ⟨h.exact, h.mono_f⟩

end EtaleCohomology
