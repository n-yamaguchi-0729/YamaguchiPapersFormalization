/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.FiniteNormalizationInertiaNativeLift
import EtaleFundamentalGroups.Inertia.CommAlgInertiaRingMaps
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import SchemeTheory.Normalization.AmbientNormalizationGroupMap
import SchemeTheory.Normalization.NativeAutomorphismRingMaps
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral

/-!
# Finite-field and normalization inertia equivalence

Constructs the normalization restriction on original finite-field inertia. Proves injectivity
and surjectivity and packages the resulting equivalence with intrinsic normalization inertia.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory

universe u v w

/-- The original field inertia acts on its actual normalization through
the original normalization restriction, with its proved inertia condition. -/
def originalFiniteNormalizationInertiaMorphism
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F).carrier) :
    GrpCat.Hom (actualNormalizationInertiaGroup A K F Q)
      (commAlgIdealInertiaGroup A (normalizationCommAlgCat A F) Q) where
  hom' :=
    { toFun := fun σ =>
        ⟨(normalizationGaloisGroupMap A K F).hom'.toFun
          (actualNormalizationInertiaElement A K F Q σ),
          actualNormalizationInertia_difference A K F Q σ⟩
      map_one' := Subtype.ext (normalizationGaloisGroupMap A K F).hom'.map_one'
      map_mul' := fun σ τ => Subtype.ext
        ((normalizationGaloisGroupMap A K F).hom'.map_mul' σ.val τ.val) }

/-- Its coefficient RingHom is exactly the original normalization action. -/
theorem originalFiniteNormalizationInertiaMorphism_ringHom
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F).carrier)
    (σ : (actualNormalizationInertiaGroup A K F Q).carrier) :
    commAlgIdealInertiaRingHom A (normalizationCommAlgCat A F) Q
        ((originalFiniteNormalizationInertiaMorphism A K F Q).hom'.toFun σ) =
      normalizationGaloisRingHom A K F (actualNormalizationInertiaElement A K F Q σ) := rfl

/-- Equality of actual normalization restrictions determines the original
finite field automorphism by fraction-field uniqueness. -/
theorem normalizationGaloisRingHom_injective
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] :
    Function.Injective (normalizationGaloisRingHom A K F) := by
  have : IsDomain A := (IsFractionRing.injective A K).isDomain
  have : IsFractionRing (integralClosure A F) F :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K F
  intro σ τ h
  have hcoeff :
      σ.toRingHom.comp (algebraMap (integralClosure A F) F) =
        τ.toRingHom.comp (algebraMap (integralClosure A F) F) := by
    exact (normalizationGaloisRingHom_commutes A K F σ).symm.trans
      ((congrArg
        (fun f : normalizationCommAlgCat A F →+* normalizationCommAlgCat A F =>
          (normalizationAmbientRingHom A (CommAlgCat.of A F)).comp f) h).trans
        (normalizationGaloisRingHom_commutes A K F τ))
  have hfield : σ.toRingHom = τ.toRingHom :=
    IsFractionRing.injective_comp_algebraMap
      (A := integralClosure A F) (K := F) (L := F) hcoeff
  apply AlgEquiv.ext
  intro x
  exact RingHom.congr_fun hfield x

/-- The proved finite field lift is a preimage under this actual morphism. -/
theorem originalFiniteNormalizationInertiaMorphism_surjective
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [IsGalois K F] [FiniteDimensional K F]
    (Q : Ideal (normalizationCommAlgCat A F).carrier) :
    Function.Surjective (originalFiniteNormalizationInertiaMorphism A K F Q).hom'.toFun := by
  intro τ
  obtain ⟨σ, hσ⟩ := finiteNormalization_inertia_exists_native_lift A K F Q τ
  refine ⟨σ, ?_⟩
  apply commAlgIdealInertiaRingHom_injective A (normalizationCommAlgCat A F) Q
  exact (originalFiniteNormalizationInertiaMorphism_ringHom A K F Q σ).trans hσ

/-- No original finite inertia element is lost on the normalization. -/
theorem originalFiniteNormalizationInertiaMorphism_injective
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [IsGalois K F] [FiniteDimensional K F]
    (Q : Ideal (normalizationCommAlgCat A F).carrier) :
    Function.Injective (originalFiniteNormalizationInertiaMorphism A K F Q).hom'.toFun := by
  intro σ τ h
  apply Subtype.ext
  apply normalizationGaloisRingHom_injective A K F
  have hcoeff := congrArg
    (commAlgIdealInertiaRingHom A (normalizationCommAlgCat A F) Q) h
  exact (originalFiniteNormalizationInertiaMorphism_ringHom A K F Q σ).symm.trans
    (hcoeff.trans (originalFiniteNormalizationInertiaMorphism_ringHom A K F Q τ))

/-- The actual original finite inertia and intrinsic normalization inertia
are isomorphic through the prescribed normalization restriction. -/
def originalFiniteNormalizationInertiaEquiv
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [IsGalois K F] [FiniteDimensional K F]
    (Q : Ideal (normalizationCommAlgCat A F).carrier) :
    (actualNormalizationInertiaGroup A K F Q).carrier ≃*
      (commAlgIdealInertiaGroup A (normalizationCommAlgCat A F) Q).carrier :=
  MulEquiv.ofBijective (originalFiniteNormalizationInertiaMorphism A K F Q).hom'
    ⟨originalFiniteNormalizationInertiaMorphism_injective A K F Q,
      originalFiniteNormalizationInertiaMorphism_surjective A K F Q⟩

end EtaleFundamentalGroups.Inertia
