/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFieldTower
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFraction
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkInertia
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Actual strict-generic Galois restriction has image original inertia

The two constructed field maps supply the coefficient actions and their
proved scalar tower. Restricting scalars along that actual tower embeds the
relative Galois group into the original one. The proved fixing criterion for
the actual stalk-fraction map gives its exact image, the original inertia.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] normalizationInertiaImageAction

/-- Restriction from the absolute Galois group of the actual strict-generic
field has image exactly the original normalization inertia subgroup. The
source action comes from its proved ambient embedding, not a chosen fixed-field model. -/
theorem geometricStalkAbsoluteGalois_restriction_range
    (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal] :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let : Algebra K (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) :=
      (normalizationStalkFractionBaseMap A K L Q).toAlgebra
    let : Algebra (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) L :=
      (geometricStalkFractionToNormalizationField A L Q).toAlgebra
    let : IsScalarTower K (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) L :=
      normalizationStalkFractionField_isScalarTower A K L Q
    (AlgEquiv.restrictScalarsHom K :
      (L ≃ₐ[FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))] L) →* Gal(L/K)).range = Q.inertia Gal(L/K) := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
    actualBaseAlgebra actualAmbientAlgebra actualTower
  apply Subgroup.ext
  intro σ
  constructor
  · rintro ⟨τ, rfl⟩
    apply (geometricStalkFractionToNormalizationField_comp_eq_self_iff A K L Q
      (AlgEquiv.restrictScalarsHom K τ)).mp
    apply RingHom.ext
    intro y
    exact τ.commutes y
  · intro hσ
    have hfixed :=
      (geometricStalkFractionToNormalizationField_comp_eq_self_iff A K L Q σ).mpr hσ
    let τ : L ≃ₐ[FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))] L :=
      { σ.toRingEquiv with commutes' := fun y => RingHom.congr_fun hfixed y }
    refine ⟨τ, ?_⟩
    apply AlgEquiv.ext
    intro y
    rfl

end EtaleFundamentalGroups.StrictHenselian
