/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Localization.Basic
import Mathlib.RingTheory.Etale.Basic

/-!
# Localizing a normalization at a base prime

This file identifies the localization of a global normalization at the image
of a base-prime complement with the normalization after localizing the base.
The equivalence is over the localized base itself, so it transports the local
etaleness statements produced by the height-one branch arguments directly to
the target required by dimension-two purity.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The localization of the normalization of `A` in `L` at the image of
`Pᶜ` is canonically equivalent, as an `A_P`-algebra, to the normalization
of `A_P` in `L`.

The algebra structure `A_P → L` is the canonical factorization through the
chosen fraction field `K`. -/
noncomputable def localizationIntegralClosureAtPrimeAlgEquiv
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := L) P
    letI := integralClosureLocalizationAlgebra (L := L) P
    Localization
        (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl) ≃ₐ[
          Localization.AtPrime P]
      integralClosure (Localization.AtPrime P) L := by
  letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  letI : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  letI := integralClosureLocalizationAlgebra (L := L) P
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  letI : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower A (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      Subtype.ext <|
        IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L x
  let e := IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
    (Localization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl))
    (integralClosure (Localization.AtPrime P) L)
  refine
    { toRingEquiv := e.toRingEquiv
      commutes' := fun z ↦ ?_ }
  apply DFunLike.congr_fun (f :=
      e.toRingHom.comp (algebraMap (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid
          (integralClosure A L) P.primeCompl))))
    (g := algebraMap (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L)) ?_ z
  apply IsLocalization.ringHom_ext P.primeCompl
  ext x
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid
        (integralClosure A L) P.primeCompl)),
    ← IsScalarTower.algebraMap_apply A (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L),
    IsScalarTower.algebraMap_apply A (integralClosure A L)
      (Localization (Algebra.algebraMapSubmonoid
        (integralClosure A L) P.primeCompl)),
    IsScalarTower.algebraMap_apply A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L)]
  exact congrArg Subtype.val (e.commutes (algebraMap A (integralClosure A L) x))

omit [IsDomain A] [IsScalarTower A K L] in
/-- Etaleness of the normalization after localizing the base gives exactly
the localized-normalization target used by the height-one input of purity. -/
theorem localization_integralClosure_etale_of_local_integralClosure_etale
    [IsScalarTower A K L]
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := L) P
    letI := integralClosureLocalizationAlgebra (L := L) P
    Algebra.Etale (Localization.AtPrime P)
        (integralClosure (Localization.AtPrime P) L) →
      Algebra.Etale (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid
          (integralClosure A L) P.primeCompl)) := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  intro h
  let : Algebra.Etale (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) := h
  exact Algebra.Etale.of_equiv
    (localizationIntegralClosureAtPrimeAlgEquiv
      (K := K) (L := L) P).symm

end EtaleFundamentalGroups

end
