/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Restriction of constant module sheaves

For an étale morphism, inverse image of modules is actual restriction of
presheaves. The canonical map from the constant sheaf on the source to the
restriction of the constant sheaf on the target is constructed from the
sheafification unit. Cocontinuity proves that this map is an isomorphism and
the explicit unit formula keeps track of actual constant sections.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

namespace EtaleCohomology

variable {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] (R : Type u) [CommRing R]

/-- Étale postcomposition lifts covering sieves by its base-change adjunction. -/
instance etalePostcompose_isCocontinuous :
    (etalePostcompose f).IsCocontinuous U.smallEtaleTopology X.smallEtaleTopology :=
  ((etalePostcomposeBaseChangeAdjunction f).isCocontinuous_iff_coverPreserving
    U.smallEtaleTopology X.smallEtaleTopology).mpr
    (etaleBaseChange_coverPreserving f)

/-- Module inverse image along an étale morphism is ordinary presheaf restriction. -/
def etalePullbackRestrictionIso :
    etalePullback f R ≅ etaleRestriction f (ModuleCat.{u} R) :=
  (etalePullbackPushforwardAdjunction f R).leftAdjointUniq
    (etaleRestrictionPushforwardAdjunction f (ModuleCat.{u} R))

/-- The canonical constant-sheaf comparison, induced by the sheafification unit. -/
def etaleRestrictionConstantHom (M : ModuleCat.{u} R) :
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶
      (etaleRestriction f (ModuleCat.{u} R)).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) :=
  ⟨sheafifyLift U.smallEtaleTopology
    (whiskerLeft (etalePostcompose f).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)))
    ((etaleRestriction f (ModuleCat.{u} R)).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)).property⟩

/-- The comparison carries the source constant section to the same target constant section. -/
lemma etaleRestrictionConstantHom_fac (M : ModuleCat.{u} R) :
    toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj M) ≫
      (etaleRestrictionConstantHom f R M).hom =
    whiskerLeft (etalePostcompose f).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) :=
  toSheafify_sheafifyLift U.smallEtaleTopology _ _

instance etaleRestrictionConstantHom_isIso (M : ModuleCat.{u} R) :
    IsIso (etaleRestrictionConstantHom f R M) := by
  let η := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)
  have : Presheaf.IsLocallyInjective U.smallEtaleTopology
      (whiskerLeft (etalePostcompose f).op η) :=
    Presheaf.isLocallyInjective_whisker U.smallEtaleTopology X.smallEtaleTopology
      (etalePostcompose f) η
  have : Presheaf.IsLocallySurjective U.smallEtaleTopology
      (whiskerLeft (etalePostcompose f).op η) :=
    Presheaf.isLocallySurjective_whisker U.smallEtaleTopology X.smallEtaleTopology
      (etalePostcompose f) η
  apply (U.smallEtaleTopology.W_sheafToPresheaf_map_iff_isIso _).mp
  apply (U.smallEtaleTopology.W.precomp_iff _ _
    (U.smallEtaleTopology.W_toSheafify ((Functor.const U.Etaleᵒᵖ).obj M))).mp
  change U.smallEtaleTopology.W
    (toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj M) ≫
      (etaleRestrictionConstantHom f R M).hom)
  rw [etaleRestrictionConstantHom_fac f R M]
  exact U.smallEtaleTopology.W_of_isLocallyBijective (whiskerLeft (etalePostcompose f).op η)

/-- Restriction of a constant module sheaf has the same constant module,
with the canonical comparison on sections. -/
def etaleRestrictionConstantIso (M : ModuleCat.{u} R) :
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u} R)).obj M ≅
      (etaleRestriction f (ModuleCat.{u} R)).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) :=
  asIso (etaleRestrictionConstantHom f R M)

end EtaleCohomology
