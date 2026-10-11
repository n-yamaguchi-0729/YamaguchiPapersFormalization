/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeInertia
import SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import SchemeTheory.RingTheory.Ramification.InertiaLocalization
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual normalization-prime localization in the ambient Galois field

The shared integral-closure fraction supplier and the existing canonical
prime-localization lift construct the literal map into the original field.
The native coefficient equations prove injectivity, its base square, and
compatibility with each original inertia element. All scalar actions are
those of the existing owners; no action on the localization is introduced.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia

universe u v w

private def primeLocalizationFieldMap
    (B : Type u) (F : Type v) [CommRing B] [IsDomain B]
    [Field F] [Algebra B F] [IsFractionRing B F]
    (Q : Ideal B) [Q.IsPrime] : Localization.AtPrime Q →+* F := by
  letI : Algebra (Localization.AtPrime Q) F :=
    localizationAtPrimeToFractionFieldAlgebra (K := F) Q
  exact algebraMap (Localization.AtPrime Q) F

private theorem primeLocalizationFieldMap_comp
    (B : Type u) (F : Type v) [CommRing B] [IsDomain B]
    [Field F] [Algebra B F] [IsFractionRing B F]
    (Q : Ideal B) [Q.IsPrime] :
    (primeLocalizationFieldMap B F Q).comp (algebraMap B (Localization.AtPrime Q)) =
      algebraMap B F := by
  let : Algebra (Localization.AtPrime Q) F :=
    localizationAtPrimeToFractionFieldAlgebra (K := F) Q
  have : IsScalarTower B (Localization.AtPrime Q) F :=
    localizationAtPrimeToFractionField_isScalarTower (K := F) Q
  exact (IsScalarTower.algebraMap_eq B (Localization.AtPrime Q) F).symm

private theorem primeLocalizationFieldMap_injective
    (B : Type u) (F : Type v) [CommRing B] [IsDomain B]
    [Field F] [Algebra B F] [IsFractionRing B F]
    (Q : Ideal B) [Q.IsPrime] :
    Function.Injective (primeLocalizationFieldMap B F Q) := by
  let : Algebra (Localization.AtPrime Q) F :=
    localizationAtPrimeToFractionFieldAlgebra (K := F) Q
  have : IsFractionRing (Localization.AtPrime Q) F :=
    localizationAtPrimeToFractionField_isFractionRing (K := F) Q
  exact IsFractionRing.injective (Localization.AtPrime Q) F

private theorem integralClosure_subtype_comp
    (A : Type u) (L : Type v) [CommRing A] [Field L] [Algebra A L] :
    (integralClosure A L).toSubring.subtype.comp (algebraMap A (integralClosure A L)) =
      algebraMap A L := rfl

private def actionInertiaLocalizationRingHom
    (G : Type u) (B : Type v) [Group G] [CommRing B] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (σ : G) (hσ : σ ∈ Q.inertia G) :
    Localization.AtPrime Q →+* Localization.AtPrime Q :=
  (SchemeTheory.inertiaLocalizationRingEquiv B Q
    (MulSemiringAction.toRingEquiv G B σ) hσ).toRingHom

private theorem actionInertiaLocalizationRingHom_comp
    (G : Type u) (B : Type v) [Group G] [CommRing B] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (σ : G) (hσ : σ ∈ Q.inertia G) :
    (actionInertiaLocalizationRingHom G B Q σ hσ).comp
        (algebraMap B (Localization.AtPrime Q)) =
      (algebraMap B (Localization.AtPrime Q)).comp (MulSemiringAction.toRingHom G B σ) := by
  apply RingHom.ext
  intro b
  exact SchemeTheory.inertiaLocalizationRingEquiv_algebraMap B Q
    (MulSemiringAction.toRingEquiv G B σ) hσ b

private theorem primeLocalization_comp_eq_of_coefficients
    (B : Type u) (F : Type v) [CommRing B] [CommRing F]
    (Q : Ideal B) [Q.IsPrime]
    (i : B →+* F) (j : Localization.AtPrime Q →+* F)
    (τ : F →+* F) (s : B →+* B)
    (e : Localization.AtPrime Q →+* Localization.AtPrime Q)
    (hj : j.comp (algebraMap B (Localization.AtPrime Q)) = i)
    (he : e.comp (algebraMap B (Localization.AtPrime Q)) =
      (algebraMap B (Localization.AtPrime Q)).comp s)
    (hτ : τ.comp i = i.comp s) :
    τ.comp j = j.comp e := by
  apply IsLocalization.ringHom_ext Q.primeCompl
  calc
    (τ.comp j).comp (algebraMap B (Localization.AtPrime Q)) =
        τ.comp (j.comp (algebraMap B (Localization.AtPrime Q))) := RingHom.comp_assoc _ _ _
    _ = τ.comp i := congrArg (RingHom.comp τ) hj
    _ = i.comp s := hτ
    _ = (j.comp (algebraMap B (Localization.AtPrime Q))).comp s :=
      congrArg (fun k : B →+* F => k.comp s) hj.symm
    _ = j.comp ((algebraMap B (Localization.AtPrime Q)).comp s) := RingHom.comp_assoc _ _ _
    _ = j.comp (e.comp (algebraMap B (Localization.AtPrime Q))) :=
      congrArg (RingHom.comp j) he.symm
    _ = (j.comp e).comp (algebraMap B (Localization.AtPrime Q)) :=
      (RingHom.comp_assoc _ _ _).symm

section Algebraic

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [Algebra.IsAlgebraic K L]

/-- The prescribed prime-localization map into the original ambient field.
Its fraction-field input is supplied by the actual algebraic normalization. -/
def integralClosurePrimeToAmbientField
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] : Localization.AtPrime Q →+* L := by
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure_isFractionRing_of_fractionField_algebraic A K L
  exact primeLocalizationFieldMap (integralClosure A L) L Q

/-- The ambient map extends the literal integral-closure inclusion. -/
theorem integralClosurePrimeToAmbientField_comp_coefficient
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    (integralClosurePrimeToAmbientField A K L Q).comp
        (algebraMap (integralClosure A L) (Localization.AtPrime Q)) =
      (integralClosure A L).toSubring.subtype := by
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure_isFractionRing_of_fractionField_algebraic A K L
  exact primeLocalizationFieldMap_comp (integralClosure A L) L Q

/-- The literal normalization-prime map into the ambient field is injective. -/
theorem integralClosurePrimeToAmbientField_injective
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    Function.Injective (integralClosurePrimeToAmbientField A K L Q) := by
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure_isFractionRing_of_fractionField_algebraic A K L
  exact primeLocalizationFieldMap_injective (integralClosure A L) L Q

/-- The original base map is preserved by the actual ambient-field map. -/
theorem integralClosurePrimeToAmbientField_comp_baseMap
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    (integralClosurePrimeToAmbientField A K L Q).comp (integralClosurePrimeBaseMap A L Q) =
      algebraMap A L := by
  change (integralClosurePrimeToAmbientField A K L Q).comp
    ((algebraMap (integralClosure A L) (Localization.AtPrime Q)).comp
      (algebraMap A (integralClosure A L))) = algebraMap A L
  rw [← RingHom.comp_assoc, integralClosurePrimeToAmbientField_comp_coefficient]
  exact integralClosure_subtype_comp A L

end Algebraic

section Galois

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L]

attribute [local instance] normalizationInertiaImageAction

omit [IsDomain A] in
private theorem normalizationInertia_comp_coefficient
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (σ : Gal(L/K)) (hσ : σ ∈ Q.inertia Gal(L/K)) :
    (normalizationPrimeInertiaRingEquiv A K L Q σ hσ).toRingHom.comp
        (algebraMap (integralClosure A L) (Localization.AtPrime Q)) =
      (algebraMap (integralClosure A L) (Localization.AtPrime Q)).comp
        (MulSemiringAction.toRingHom Gal(L/K) (integralClosure A L) σ) := by
  exact actionInertiaLocalizationRingHom_comp Gal(L/K) (integralClosure A L) Q σ hσ

/-- The actual inclusion into the ambient field intertwines each original
inertia element with its native automorphism of the literal prime localization. -/
theorem integralClosurePrimeToAmbientField_comp_inertia
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (σ : Gal(L/K)) (hσ : σ ∈ Q.inertia Gal(L/K)) :
    σ.toRingHom.comp (integralClosurePrimeToAmbientField A K L Q) =
      (integralClosurePrimeToAmbientField A K L Q).comp
        (normalizationPrimeInertiaRingEquiv A K L Q σ hσ).toRingHom := by
  exact primeLocalization_comp_eq_of_coefficients (integralClosure A L) L Q
    (integralClosure A L).toSubring.subtype (integralClosurePrimeToAmbientField A K L Q)
    σ.toRingHom (MulSemiringAction.toRingHom Gal(L/K) (integralClosure A L) σ)
    (normalizationPrimeInertiaRingEquiv A K L Q σ hσ).toRingHom
    (integralClosurePrimeToAmbientField_comp_coefficient A K L Q)
    (normalizationInertia_comp_coefficient A K L Q σ hσ)
    (normalizationInertiaImageAction_comp_inclusion A K L σ)

end Galois

end EtaleFundamentalGroups.StrictHenselian
