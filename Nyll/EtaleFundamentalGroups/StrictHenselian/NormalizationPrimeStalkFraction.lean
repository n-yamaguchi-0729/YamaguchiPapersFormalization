/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrime
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeInertia
import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeInertiaFixedImage
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Algebra.Algebra.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The actual strict-stalk fraction field inside the original ambient field

The constructed stalk embedding and the prescribed normalization-localization
map form an injective ring map into L. The native fraction-ring lift extends
that actual map. Native localization extensionality then transports the
already proved inertia fixedness to the fraction ring. The geometric
construction uses the reduced A/L inputs; the original Galois inputs supply
those properties, and the two prescribed ambient maps agree literally.
No reverse fixed-image equality or field comparison is assumed.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia

universe u v w

private def injectiveFractionLift
    {R : Type u} {F : Type v} [CommRing R] [Field F]
    (f : R →+* F) (hf : Function.Injective f) : FractionRing R →+* F := by
  have : IsDomain R := hf.isDomain f
  exact IsFractionRing.lift (K := FractionRing R) hf

private theorem injectiveFractionLift_injective
    {R : Type u} {F : Type v} [CommRing R] [Field F]
    (f : R →+* F) (hf : Function.Injective f) :
    Function.Injective (injectiveFractionLift f hf) := by
  have : IsDomain R := hf.isDomain f
  exact (injectiveFractionLift f hf).injective

private theorem injectiveFractionLift_comp
    {R : Type u} {F : Type v} [CommRing R] [Field F]
    (f : R →+* F) (hf : Function.Injective f) :
    (injectiveFractionLift f hf).comp (algebraMap R (FractionRing R)) = f := by
  have : IsDomain R := hf.isDomain f
  apply RingHom.ext
  intro r
  exact IsFractionRing.lift_algebraMap (K := FractionRing R) hf r

private theorem injectiveFractionLift_comp_endomorphism
    {R : Type u} {F : Type v} [CommRing R] [Field F]
    (f : R →+* F) (hf : Function.Injective f)
    (τ : F →+* F) (hτ : τ.comp f = f) :
    τ.comp (injectiveFractionLift f hf) = injectiveFractionLift f hf := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  calc
    (τ.comp (injectiveFractionLift f hf)).comp (algebraMap R (FractionRing R)) =
        τ.comp ((injectiveFractionLift f hf).comp (algebraMap R (FractionRing R))) :=
      RingHom.comp_assoc _ _ _
    _ = τ.comp f := congrArg (RingHom.comp τ) (injectiveFractionLift_comp f hf)
    _ = f := hτ
    _ = (injectiveFractionLift f hf).comp (algebraMap R (FractionRing R)) :=
      (injectiveFractionLift_comp f hf).symm

private def normalizationPrimeAmbientMap
    (A : Type u) (L : Type v) [CommRing A] [IsDomain A] [Field L]
    [Algebra A L] [FaithfulSMul A L] [Algebra.IsAlgebraic A L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] : Localization.AtPrime Q →+* L := by
  letI : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  have : IsScalarTower A (FractionRing A) L := inferInstance
  have : Algebra.IsAlgebraic (FractionRing A) L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A) (C := L)).mp
      inferInstance
  exact integralClosurePrimeToAmbientField A (FractionRing A) L Q

private theorem normalizationPrimeAmbientMap_injective
    (A : Type u) (L : Type v) [CommRing A] [IsDomain A] [Field L]
    [Algebra A L] [FaithfulSMul A L] [Algebra.IsAlgebraic A L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    Function.Injective (normalizationPrimeAmbientMap A L Q) := by
  let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  have : IsScalarTower A (FractionRing A) L := inferInstance
  have : Algebra.IsAlgebraic (FractionRing A) L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A) (C := L)).mp
      inferInstance
  exact integralClosurePrimeToAmbientField_injective A (FractionRing A) L Q

/- Both definitions use the same C→L inclusion and the same prescribed
localization lift. Their different fraction-field suppliers are proofs of
the same Prop, so no scalar-map comparison hypothesis is required. -/
private theorem normalizationPrimeAmbientMap_eq
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    [FaithfulSMul A L] [Algebra.IsAlgebraic A L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    normalizationPrimeAmbientMap A L Q = integralClosurePrimeToAmbientField A K L Q := by
  rfl

section Geometric

variable (A L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field L] [Algebra A L] [FaithfulSMul A L] [Algebra.IsAlgebraic A L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]

omit [IsIntegrallyClosed A] [IsLocalRing A] in
private def normalizationStalkAmbientMap :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue (Localization.AtPrime Q)).comp (integralClosurePrimeBaseMap A L Q))))
      →+* L := by
  intro actualHenselian actualSepClosed
  exact (normalizationPrimeAmbientMap A L Q).comp
    (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q))

private theorem normalizationStalkAmbientMap_injective
    (hQ : Q.under A = IsLocalRing.maximalIdeal A) :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    Function.Injective (normalizationStalkAmbientMap A L Q) := by
  intro actualHenselian actualSepClosed
  exact (normalizationPrimeAmbientMap_injective A L Q).comp
    (geometricStalkToIntegralClosurePrime_injective A L Q hQ)

end Geometric

section MaximalGeometric

variable (A L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field L] [Algebra A L] [FaithfulSMul A L] [Algebra.IsAlgebraic A L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsMaximal]

/-- The actual fraction ring of the geometric stalk embeds in the original
ambient field, through the already constructed normalization-prime embedding. -/
def geometricStalkFractionToNormalizationField :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue (Localization.AtPrime Q)).comp (integralClosurePrimeBaseMap A L Q)))))
      →+* L := by
  intro actualHenselian actualSepClosed
  exact injectiveFractionLift (normalizationStalkAmbientMap A L Q)
    (normalizationStalkAmbientMap_injective A L Q (integralClosure_maximalPrime_under A L Q))

/-- The constructed fraction-ring map is injective, by the native field-map
injectivity theorem applied to the actual injective stalk map. -/
theorem geometricStalkFractionToNormalizationField_injective :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    Function.Injective (geometricStalkFractionToNormalizationField A L Q) := by
  intro actualHenselian actualSepClosed
  exact injectiveFractionLift_injective (normalizationStalkAmbientMap A L Q)
    (normalizationStalkAmbientMap_injective A L Q (integralClosure_maximalPrime_under A L Q))

private theorem geometricStalkFractionToNormalizationField_comp_endomorphism
    (τ : L →+* L) :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    τ.comp (normalizationStalkAmbientMap A L Q) = normalizationStalkAmbientMap A L Q →
      τ.comp (geometricStalkFractionToNormalizationField A L Q) =
        geometricStalkFractionToNormalizationField A L Q := by
  intro actualHenselian actualSepClosed hτ
  exact injectiveFractionLift_comp_endomorphism (normalizationStalkAmbientMap A L Q)
    (normalizationStalkAmbientMap_injective A L Q (integralClosure_maximalPrime_under A L Q)) τ hτ

end MaximalGeometric

section Galois

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]

attribute [local instance] normalizationInertiaImageAction

omit [IsIntegrallyClosed A] in
private theorem normalizationStalkAmbientMap_comp_inertia
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (σ : Gal(L/K)) (hσ : σ ∈ Q.inertia Gal(L/K)) :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    σ.toRingHom.comp (normalizationStalkAmbientMap A L Q) =
      normalizationStalkAmbientMap A L Q := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  change σ.toRingHom.comp ((normalizationPrimeAmbientMap A L Q).comp
      (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q))) =
    (normalizationPrimeAmbientMap A L Q).comp
      (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q))
  rw [normalizationPrimeAmbientMap_eq A K L Q]
  rw [← RingHom.comp_assoc,
    integralClosurePrimeToAmbientField_comp_inertia A K L Q σ hσ,
    RingHom.comp_assoc, normalizationPrimeInertia_comp_geometricStalkMap A K L Q σ hσ]

/-- The actual geometric-stalk fraction-field map extends the literal
stalk map into the original ambient field. Both maps are the existing
constructed maps, and the equality is their original localization computation. -/
theorem geometricStalkFractionToNormalizationField_comp_stalk
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
    (geometricStalkFractionToNormalizationField A L Q).comp
        (algebraMap
          (geometricStalk (Spec.map (CommRingCat.ofHom
            ((IsLocalRing.residue (Localization.AtPrime Q)).comp
              (integralClosurePrimeBaseMap A L Q)))))
          (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
            ((IsLocalRing.residue (Localization.AtPrime Q)).comp
              (integralClosurePrimeBaseMap A L Q))))))) =
      (integralClosurePrimeToAmbientField A K L Q).comp
        (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q)) := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  exact (injectiveFractionLift_comp (normalizationStalkAmbientMap A L Q)
    (normalizationStalkAmbientMap_injective A L Q
      (integralClosure_maximalPrime_under A L Q))).trans
        (congrArg
          (fun j : Localization.AtPrime Q →+* L =>
            j.comp (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q)))
          (normalizationPrimeAmbientMap_eq A K L Q))

/-- Every original inertia element fixes the constructed image of the
actual geometric-stalk fraction field in L. This is the forward fixed-field
inclusion; the reverse inclusion is not a premise or conclusion here. -/
theorem geometricStalkFractionToNormalizationField_comp_inertia
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal]
    (σ : Gal(L/K)) (hσ : σ ∈ Q.inertia Gal(L/K)) :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    σ.toRingHom.comp (geometricStalkFractionToNormalizationField A L Q) =
      geometricStalkFractionToNormalizationField A L Q := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  exact geometricStalkFractionToNormalizationField_comp_endomorphism A L Q σ.toRingHom
    (normalizationStalkAmbientMap_comp_inertia A K L Q σ hσ)

end Galois

end EtaleFundamentalGroups.StrictHenselian
