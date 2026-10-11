/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeAbsoluteResidueFields
import EtaleFundamentalGroups.Inertia.NativeSeparableResidueGroup
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidueClosure
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The original strict-stalk residue is the actual separable normalization residue

The literal maximal quotient of the normalization is canonically isomorphic
to the residue field of its prime localization. Its coefficient equation
makes this an isomorphism over the original local residue field. Transporting
the proved actual stalk-residue image through this concrete isomorphism gives
the same separable field used in the original decomposition/inertia sequence.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory

universe u v w

/-- The original maximal normalization quotient and the residue of its prime
localization agree over the original local residue field. -/
def normalizationResidueLocalizationAlgEquiv
    (A : Type u) (L : Type w) [CommRing A] [IsLocalRing A] [Field L] [Algebra A L]
    (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal] :
    let nativeQ : Ideal (normalizationCommAlgCat A L).carrier := Q
    let : nativeQ.IsMaximal := hQmax
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q (integralClosure_maximalPrime_under A L Q)
    let : Algebra (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L nativeQ).α :=
      normalizationResidueFieldAlgebra A L nativeQ
    let : Algebra (IsLocalRing.ResidueField A) Q.ResidueField :=
      (IsLocalRing.ResidueField.map (integralClosurePrimeBaseMap A L Q)).toAlgebra
    (normalizationResidueFieldObject A L nativeQ).α ≃ₐ[
      IsLocalRing.ResidueField A] Q.ResidueField := by
  intro nativeQ actualNativeMax actualLocal actualQuotientAlgebra actualLocalizationAlgebra
  let e : ((integralClosure A L) ⧸ Q) ≃+* Q.ResidueField :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal Q (Localization.AtPrime Q)).toRingEquiv
  refine { e with commutes' := ?_ }
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) x
  change e (Ideal.Quotient.mk Q (algebraMap A (integralClosure A L) a)) =
    IsLocalRing.residue (Localization.AtPrime Q) (integralClosurePrimeBaseMap A L Q a)
  exact IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk Q (Localization.AtPrime Q)
    (algebraMap A (integralClosure A L) a)

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal]

/-- The residue of the actual original strict stalk is the separable part of
the same literal normalization quotient used by the original residue action. -/
def normalizationPrimeStalkResidueEquiv :
    let nativeQ : Ideal (normalizationCommAlgCat A L).carrier := Q
    let : nativeQ.IsMaximal := hQmax
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed Q.ResidueField :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q (integralClosure_maximalPrime_under A L Q)
    let : Algebra (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L nativeQ).α :=
      normalizationResidueFieldAlgebra A L nativeQ
    let : Algebra (IsLocalRing.ResidueField A) Q.ResidueField :=
      (IsLocalRing.ResidueField.map (integralClosurePrimeBaseMap A L Q)).toAlgebra
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ≃ₐ[
      IsLocalRing.ResidueField A]
        separableClosure (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A L nativeQ).α := by
  intro nativeQ actualNativeMax actualAlgebraic actualFaithful actualHenselian
    actualSepClosed actualLocal
    actualQuotientAlgebra actualLocalizationAlgebra φ actualStructureAlgebra actualStructureLocal
  let : MulAction (IsLocalRing.ResidueField A) Q.ResidueField :=
    (Algebra.toModule (R := IsLocalRing.ResidueField A) (A := Q.ResidueField)
      ).toDistribMulAction.toMulAction
  let eStalk : IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ≃ₐ[
      IsLocalRing.ResidueField A] separableClosure (IsLocalRing.ResidueField A) Q.ResidueField :=
    geometricStalkResidueSeparableClosureEquiv A Q.ResidueField
  let eQuotient : (normalizationResidueFieldObject A L nativeQ).α ≃ₐ[
      IsLocalRing.ResidueField A] Q.ResidueField := normalizationResidueLocalizationAlgEquiv A L Q
  exact eStalk.trans (separableClosure.algEquivOfAlgEquiv eQuotient.symm)

/-- The residue equivalence preserves the original literal embedding into
κ(B_Q); it is not only an abstract isomorphism of residue fields. -/
theorem normalizationPrimeStalkResidueEquiv_comp :
    let nativeQ : Ideal (normalizationCommAlgCat A L).carrier := Q
    let : nativeQ.IsMaximal := hQmax
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed Q.ResidueField :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q (integralClosure_maximalPrime_under A L Q)
    let : Algebra (IsLocalRing.ResidueField A) (normalizationResidueFieldObject A L nativeQ).α :=
      normalizationResidueFieldAlgebra A L nativeQ
    let : Algebra (IsLocalRing.ResidueField A) Q.ResidueField :=
      (IsLocalRing.ResidueField.map (integralClosurePrimeBaseMap A L Q)).toAlgebra
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    ∀ x : IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ))),
      normalizationResidueLocalizationAlgEquiv A L Q
        (nativeSeparableResidueScalar (IsLocalRing.ResidueField A)
          (normalizationResidueFieldObject A L nativeQ)
          (normalizationResidueFieldAlgebra A L nativeQ)
          (normalizationPrimeStalkResidueEquiv A K L Q x)) =
        geometricStalkResidueEmbedding (Spec.map (CommRingCat.ofHom φ)) x := by
  intro nativeQ actualNativeMax actualAlgebraic actualFaithful actualHenselian
    actualSepClosed actualLocal
    actualQuotientAlgebra actualLocalizationAlgebra φ actualStructureAlgebra actualStructureLocal x
  let : MulAction (IsLocalRing.ResidueField A) Q.ResidueField :=
    (Algebra.toModule (R := IsLocalRing.ResidueField A) (A := Q.ResidueField)
      ).toDistribMulAction.toMulAction
  let e := normalizationResidueLocalizationAlgEquiv A L Q
  change e (e.symm
      ((geometricStalkResidueSeparableClosureEquiv A Q.ResidueField x :
        separableClosure (IsLocalRing.ResidueField A) Q.ResidueField) : Q.ResidueField)) = _
  exact (e.apply_symm_apply _).trans
    (geometricStalkResidueSeparableClosureEquiv_apply A Q.ResidueField x)

end EtaleFundamentalGroups.StrictHenselian
