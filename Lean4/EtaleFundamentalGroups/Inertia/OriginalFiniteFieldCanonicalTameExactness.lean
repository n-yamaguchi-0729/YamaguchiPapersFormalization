/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertia
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationTameExactness
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Exactness of finite-field tame characters

Constructs the original finite-field canonical tame morphism and an independent principal-unit
wild subgroup. Proves surjectivity and identifies that subgroup as the kernel.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory

universe u v w

/-- The same intrinsic canonical character, evaluated on the actual
normalization action of the original finite field inertia. -/
def originalFiniteFieldCanonicalTameMorphism
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    actualNormalizationInertiaGroup A K F Q ⟶
      originalFiniteNormalizationTameRootsGroup A K F Q :=
  originalFiniteNormalizationInertiaMorphism A K F Q ≫
    originalFiniteNormalizationTameMorphism A K F Q

/-- The actual principal-unit wild subgroup, pulled back through the
prescribed normalization restriction. This definition is independent of
the canonical character. -/
def originalFiniteFieldWildSubgroup
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    Subgroup (actualNormalizationInertiaGroup A K F Q) :=
  (originalFiniteNormalizationWildSubgroup A K F Q).comap
    (originalFiniteNormalizationInertiaMorphism A K F Q).hom

/-- At one actual finite Galois stage, the original inertia maps onto the
full canonical residue-root group and has precisely the independently
defined principal-unit wild kernel. All comparison data are constructed. -/
theorem originalFiniteFieldCanonicalTameMorphism_exact
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal] :
    Function.Surjective (originalFiniteFieldCanonicalTameMorphism A K F Q).hom.toFun ∧
      (originalFiniteFieldCanonicalTameMorphism A K F Q).hom.ker =
        originalFiniteFieldWildSubgroup A K F Q := by
  have hcharacter := originalFiniteNormalizationTameMorphism_exact A K F Q
  constructor
  · exact hcharacter.1.comp
      (originalFiniteNormalizationInertiaMorphism_surjective A K F Q)
  · change ((originalFiniteNormalizationTameMorphism A K F Q).hom.comp
        (originalFiniteNormalizationInertiaMorphism A K F Q).hom).ker =
      (originalFiniteNormalizationWildSubgroup A K F Q).comap
        (originalFiniteNormalizationInertiaMorphism A K F Q).hom
    exact (MonoidHom.comap_ker
      (originalFiniteNormalizationTameMorphism A K F Q).hom
      (originalFiniteNormalizationInertiaMorphism A K F Q).hom).symm.trans
      (congrArg
        (fun H : Subgroup (commAlgIdealInertiaGroup A (normalizationCommAlgCat A F) Q) =>
          H.comap (originalFiniteNormalizationInertiaMorphism A K F Q).hom)
        hcharacter.2)

end EtaleFundamentalGroups.Inertia
