/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Geometric stalks and exactness on the small étale site

At a point of a scheme, use the separable closure of its residue field to obtain
a geometric point and its filtered-colimit stalk functor. The existing
conservativity of this family of geometric points detects the vanishing of
homology, hence exactness of sequences of coefficient sheaves.
-/


noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The geometric stalk at the separable closure of the residue field of a point. -/
def residueStalk (x : X) : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  (Scheme.pointSmallEtale
    ((Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩)).sheafFiber

instance (x : X) : PreservesFiniteLimits (residueStalk X R x) :=
  inferInstanceAs (PreservesFiniteLimits (GrothendieckTopology.Point.sheafFiber _))

instance (x : X) : PreservesFiniteColimits (residueStalk X R x) :=
  inferInstanceAs (PreservesFiniteColimits (GrothendieckTopology.Point.sheafFiber _))

/-- Exactness of coefficient sheaves is detected on these geometric stalks. -/
lemma exact_iff_residueStalk (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :
    S.Exact ↔ ∀ x : X, (S.map (residueStalk X R x)).Exact := by
  constructor
  · intro h x
    exact h.map (residueStalk X R x)
  · intro h
    rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero]
    apply ((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyFaithful
      (ModuleCat.{u} R)).map_injective
    rintro ⟨_, ⟨x⟩⟩
    have hx : IsZero ((residueStalk X R x).obj S.leftHomologyData.H) :=
      (S.leftHomologyData.exact_map_iff (residueStalk X R x)).mp (h x)
    change (residueStalk X R x).map (𝟙 S.leftHomologyData.H) =
      (residueStalk X R x).map 0
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact hx.eq_of_src _ _

/-- Short exactness is likewise equivalent to short exactness at every geometric stalk. -/
lemma shortExact_iff_residueStalk
    (S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) :
    S.ShortExact ↔ ∀ x : X, (S.map (residueStalk X R x)).ShortExact := by
  constructor
  · intro h x
    exact h.map_of_exact (residueStalk X R x)
  · intro h
    refine
      { exact := (exact_iff_residueStalk X R S).mpr (fun x => (h x).exact)
        mono_f := ?_
        epi_g := ?_ }
    · apply (((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectMonomorphisms
        (ModuleCat.{u} R)).mono_iff S.f).mpr
      rintro ⟨_, ⟨x⟩⟩
      exact (h x).mono_f
    · apply (((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectEpimorphisms
        (ModuleCat.{u} R)).epi_iff S.g).mpr
      rintro ⟨_, ⟨x⟩⟩
      exact (h x).epi_g

end EtaleCohomology
