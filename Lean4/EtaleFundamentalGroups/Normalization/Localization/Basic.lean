/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Normalization after localization at a prime

This file uses the canonical fraction-field factorization from
`FractionFieldLocalization` to relate a prime localization to the
normalization in a field extension.  The normalization inclusion is obtained
by base-changing integrality, after which we specialize mathlib's theorem that
integral closure commutes with localization.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The underlying inclusion of the original normalization into the
normalization after localizing the base at `P`. -/
noncomputable def integralClosureLocalizationRingHom
    (P : Ideal A) [P.IsPrime]
    [Algebra (Localization.AtPrime P) L]
    [IsScalarTower A (Localization.AtPrime P) L] :
    integralClosure A L →+*
      integralClosure (Localization.AtPrime P) L := by
  exact
    { toFun := fun x ↦ ⟨x, x.2.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The canonical algebra structure induced by
`integralClosureLocalizationRingHom`. -/
noncomputable abbrev integralClosureLocalizationAlgebra
    (P : Ideal A) [P.IsPrime]
    [Algebra (Localization.AtPrime P) L]
    [IsScalarTower A (Localization.AtPrime P) L] :
    Algebra (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) := by
  exact (integralClosureLocalizationRingHom (L := L) P).toAlgebra

/-- The canonical inclusion from the original normalization into the
normalization after localizing the base at `P`. -/
noncomputable def integralClosureLocalizationAlgHom
    (P : Ideal A) [P.IsPrime]
    [Algebra (Localization.AtPrime P) L]
    [IsScalarTower A (Localization.AtPrime P) L] :
    letI := integralClosureLocalizationAlgebra (L := L) P
    integralClosure A L →ₐ[A]
      integralClosure (Localization.AtPrime P) L := by
  letI := integralClosureLocalizationAlgebra (L := L) P
  refine
    { toRingHom := integralClosureLocalizationRingHom (L := L) P
      commutes' := fun x ↦ Subtype.ext ?_ }
  rfl

omit [IsDomain A] in
/-- The normalization of the prime localization inside `L` is the localization
of the original normalization at the image of `Pᶜ`. -/
theorem isLocalization_integralClosure_localizationAtPrime
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    letI := integralClosureLocalizationAlgebra (L := L) P
    IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let hALocL : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L := hALocL
  let := integralClosureLocalizationAlgebra (L := L) P
  let hAB : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) := hAB
  let hBL : IsScalarTower (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) L := hBL
  let : IsLocalization
      (Algebra.algebraMapSubmonoid L P.primeCompl) L :=
    IsLocalization.of_le_isUnit fun y hy ↦ by
      rcases hy with ⟨x, hx, rfl⟩
      change IsUnit (algebraMap A L x)
      rw [isUnit_iff_ne_zero, IsScalarTower.algebraMap_apply A K L,
        map_ne_zero_iff _ (algebraMap K L).injective,
        map_ne_zero_iff _ (IsFractionRing.injective A K)]
      exact fun h ↦ hx (h ▸ P.zero_mem)
  have hLocal : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    @IsLocalization.integralClosure
      A _ L _ _ (Localization.AtPrime P) L _ _ _ _ _ _ _ hALocL
      P.primeCompl _ _ (integralClosureLocalizationAlgebra (L := L) P) hBL hAB
  exact hLocal

omit [IsDomain A] in
/-- Finiteness of a normalization is preserved when the base is localized
at a prime.  The target normalization is identified with the corresponding
localization of the original normalization, so no finiteness assumption on
the localized ring is needed. -/
theorem moduleFinite_integralClosure_localizationAtPrime
    [Module.Finite A (integralClosure A L)]
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := L) P
    Module.Finite (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      Subtype.ext <|
        IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L x
  exact Module.Finite.of_isLocalization
    A (integralClosure A L) P.primeCompl

end EtaleFundamentalGroups
