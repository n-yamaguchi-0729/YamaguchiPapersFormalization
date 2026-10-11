/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Away.GenericTensor.HeightOneBaseChange
import SchemeTheory.Normalization.Localization.IntegralClosureAwayEquiv

/-!
# Literal away maps for fixed generic tensor components

An algebra which is finite etale on an original boundary complement remains
finite etale after arbitrary normal base change and passage to a specified
generic tensor component.  This file returns the result for the literal away
localization of the component's normalization, rather than only at a
height-one localization.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uA uC uD uF uE uK

/-- A fixed generic component after normal base change inherits the original
finite-etale boundary complement as the literal away map of its
normalization.  The maximal tensor ideal `m` is preserved throughout. -/
theorem
    localization_away_integralClosure_genericTensorFieldComponent_etale_of_base_away
    {A : Type uA} {C : Type uC} {D : Type uD}
    {F : Type uF} {E : Type uE} {K : Type uK}
    [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C] [FaithfulSMul A C]
    (f : A)
    [Algebra (Localization.Away f)
      (Localization.Away (algebraMap A C f))]
    [Module.Finite (Localization.Away f)
      (Localization.Away (algebraMap A C f))]
    [Algebra.Etale (Localization.Away f)
      (Localization.Away (algebraMap A C f))]
    [Field F] [Algebra (Localization.Away f) F]
    [IsFractionRing (Localization.Away f) F]
    [Algebra A F] [IsScalarTower A (Localization.Away f) F]
    [Field E] [Algebra (Localization.Away (algebraMap A C f)) E]
    [IsFractionRing (Localization.Away (algebraMap A C f)) E]
    [Algebra (Localization.Away f) E]
    [IsScalarTower (Localization.Away f)
      (Localization.Away (algebraMap A C f)) E]
    [Algebra F E] [IsScalarTower (Localization.Away f) F E]
    [CommRing D] [IsDomain D] [IsIntegrallyClosed D] [Algebra A D]
    [Field K] [Algebra D K] [IsFractionRing D K]
    [Algebra A K] [IsScalarTower A D K]
    [Algebra F K] [IsScalarTower A F K]
    (m : Ideal (K ⊗[F] E)) [m.IsMaximal] :
    let M := GenericTensorFieldComponent m
    letI : Algebra D M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := D) m
    letI : SMul D M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
    letI : IsScalarTower D K M :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    (Localization.awayMap (algebraMap D (integralClosure D M))
      (algebraMap A D f)).Etale := by
  dsimp only
  let S := Localization.Away f
  let fD : D := algebraMap A D f
  have hfS : algebraMap A S f ≠ 0 := by
    let : Nontrivial S := (algebraMap S F).domain_nontrivial
    exact (IsLocalization.Away.algebraMap_isUnit f).ne_zero
  have hfAF : algebraMap A F f ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A S F]
    simpa using (IsFractionRing.injective S F).ne hfS
  have hfAK : algebraMap A K f ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A F K]
    simpa using (algebraMap F K).injective.ne hfAF
  have hfD : fD ≠ 0 := by
    intro hfDzero
    apply hfAK
    calc
      algebraMap A K f = algebraMap D K (algebraMap A D f) :=
        IsScalarTower.algebraMap_apply A D K f
      _ = algebraMap D K fD := by rfl
      _ = algebraMap D K 0 := congrArg (algebraMap D K) hfDzero
      _ = 0 := map_zero (algebraMap D K)
  let B := Localization.Away fD
  let : IsDomain B := IsLocalization.Away.isDomain B hfD
  let : Algebra B K :=
    localizationAwayToExtensionAlgebra
      (A := D) (K := K) (L := K) fD hfD
  let : IsScalarTower D B K :=
    localizationAwayToExtension_isScalarTower
      (A := D) (K := K) (L := K) fD hfD
  let : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers fD) B K
  let : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B (Submonoid.powers fD)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hfD))
  let : IsScalarTower A D B := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : IsScalarTower A B K := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap A K x = algebraMap D K (algebraMap A D x) :=
        IsScalarTower.algebraMap_apply A D K x
      _ = algebraMap B K (algebraMap D B (algebraMap A D x)) :=
        IsScalarTower.algebraMap_apply D B K (algebraMap A D x)
      _ = algebraMap B K (algebraMap A B x) := rfl
  have hfB : IsUnit (algebraMap A B f) := by
    change IsUnit (algebraMap D B fD)
    exact IsLocalization.Away.algebraMap_isUnit fD
  let M := GenericTensorFieldComponent m
  have hlocalOld :=
    integralClosure_genericTensorFieldComponent_etale_of_away_isUnit
      (R := A) (C := C) (B := B) (F := F) (E := E) (K := K)
      f hfB m
  let : Algebra D M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := D) m
  let : SMul D M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
  let : IsScalarTower D K M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let quotientBM : Algebra B M :=
    Ideal.instAlgebraQuotient B m
  let canonicalBM : Algebra B M :=
    localizationAwayToExtensionAlgebra
      (A := D) (K := K) (L := M) fD hfD
  have hAlgebra : quotientBM = canonicalBM := by
    have hmaps :
        @algebraMap B M _ _ quotientBM =
          @algebraMap B M _ _ canonicalBM := by
      apply IsLocalization.ringHom_ext (Submonoid.powers fD)
      apply DFunLike.ext _ _
      intro x
      change algebraMap K M (algebraMap B K (algebraMap D B x)) =
        (IsLocalization.Away.lift fD
          (show IsUnit (algebraMap D M fD) by
            rw [IsScalarTower.algebraMap_apply D K M]
            exact (algebraMap K M).isUnit_map
              (isUnit_iff_ne_zero.mpr
                (by simpa using (IsFractionRing.injective D K).ne hfD))))
          (algebraMap D B x)
      rw [IsLocalization.Away.lift_eq]
      calc
        algebraMap K M (algebraMap B K (algebraMap D B x)) =
            algebraMap K M (algebraMap D K x) := by
          rw [IsScalarTower.algebraMap_apply D B K]
        _ = algebraMap D M x :=
          (IsScalarTower.algebraMap_apply D K M x).symm
    apply Algebra.algebra_ext
    intro z
    exact DFunLike.congr_fun hmaps z
  have hlocalCanonical :
      @Algebra.Etale B
        (@integralClosure B M _ _ canonicalBM)
        _ _
        (@integralClosure B M _ _ canonicalBM).algebra := by
    exact hAlgebra ▸ hlocalOld
  let : Algebra B M := canonicalBM
  let : SMul B M := canonicalBM.toSMul
  let : IsScalarTower D B M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap D M x =
      (IsLocalization.Away.lift fD _) (algebraMap D B x)
    rw [IsLocalization.Away.lift_eq]
  exact localization_integralClosure_away_etale_of_local_integralClosure_etale
    (A := D) (K := K) (L := M) fD hfD hlocalCanonical

/-- The fixed-component away theorem with all localization fraction fields
and scalar towers constructed from the unlocalized fraction-field tower.

This is the form used by a full radical cover: `D` is the normal cover,
`K` is its fraction field, and `m` is the already selected maximal ideal of
`K ⊗[F] E`.  The only away input is the literal map obtained from the
original finite normalization. -/
theorem
    localization_away_integralClosure_genericTensorFieldComponent_etale_of_awayMap
    {A : Type uA} {C : Type uC} {D : Type uD}
    {F : Type uF} {E : Type uE} {K : Type uK}
    [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C] [FaithfulSMul A C]
    [Module.Finite A C]
    (f : A) (hf : f ≠ 0)
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra C E] [IsFractionRing C E]
    [Algebra A E] [IsScalarTower A C E]
    [Algebra F E] [IsScalarTower A F E]
    [CommRing D] [IsDomain D] [IsIntegrallyClosed D] [Algebra A D]
    [Field K] [Algebra D K] [IsFractionRing D K]
    [Algebra A K] [IsScalarTower A D K]
    [Algebra F K] [IsScalarTower A F K]
    (hAway : (Localization.awayMap (algebraMap A C) f).Etale)
    (m : Ideal (K ⊗[F] E)) [m.IsMaximal] :
    let M := GenericTensorFieldComponent m
    letI : Algebra D M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := D) m
    letI : SMul D M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
    letI : IsScalarTower D K M :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    (Localization.awayMap (algebraMap D (integralClosure D M))
      (algebraMap A D f)).Etale := by
  let S := Localization.Away f
  let fC : C := algebraMap A C f
  let T := Localization.Away fC
  have hfC : fC ≠ 0 := by
    simpa [fC] using (FaithfulSMul.algebraMap_injective A C).ne hf
  let mapST : S →+* T := Localization.awayMap (algebraMap A C) f
  let : Algebra S T := mapST.toAlgebra
  let : IsScalarTower A C T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : IsScalarTower A S T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap A T x = mapST (algebraMap A S x)
    rw [IsScalarTower.algebraMap_apply A C T]
    simp [mapST, S, T, fC, IsLocalization.Away.map]
  let : Module.Finite S T :=
    Module.Finite.of_isLocalization A C (Submonoid.powers f)
  let : Algebra.Etale S T := hAway.toAlgebra
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let : IsDomain T := IsLocalization.Away.isDomain T hfC
  let : Algebra S F :=
    localizationAwayToExtensionAlgebra
      (A := A) (K := F) (L := F) f hf
  let : IsScalarTower A S F :=
    localizationAwayToExtension_isScalarTower
      (A := A) (K := F) (L := F) f hf
  let : IsFractionRing S F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers f) S F
  let : Algebra T E :=
    localizationAwayToExtensionAlgebra
      (A := C) (K := E) (L := E) fC hfC
  let : IsScalarTower C T E :=
    localizationAwayToExtension_isScalarTower
      (A := C) (K := E) (L := E) fC hfC
  let : IsFractionRing T E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers fC) T E
  let : Algebra S E :=
    ((algebraMap T E).comp (algebraMap S T)).toAlgebra
  let : IsScalarTower S T E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower S F E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    have hmaps :
        (algebraMap F E).comp (algebraMap S F) = algebraMap S E := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      ext a
      change algebraMap F E (algebraMap S F (algebraMap A S a)) =
        algebraMap T E (mapST (algebraMap A S a))
      calc
        algebraMap F E (algebraMap S F (algebraMap A S a)) =
            algebraMap F E (algebraMap A F a) := by
          rw [← IsScalarTower.algebraMap_apply A S F]
        _ = algebraMap A E a :=
          (IsScalarTower.algebraMap_apply A F E a).symm
        _ = algebraMap C E (algebraMap A C a) :=
          IsScalarTower.algebraMap_apply A C E a
        _ = algebraMap T E (algebraMap C T (algebraMap A C a)) :=
          IsScalarTower.algebraMap_apply C T E (algebraMap A C a)
        _ = algebraMap T E (mapST (algebraMap A S a)) := by
          congr 1
          calc
            algebraMap C T (algebraMap A C a) = algebraMap A T a :=
              (IsScalarTower.algebraMap_apply A C T a).symm
            _ = algebraMap S T (algebraMap A S a) :=
              IsScalarTower.algebraMap_apply A S T a
            _ = mapST (algebraMap A S a) := rfl
    exact (DFunLike.congr_fun hmaps x).symm
  exact
    localization_away_integralClosure_genericTensorFieldComponent_etale_of_base_away
      (A := A) (C := C) (D := D) (F := F) (E := E) (K := K)
      f m

end EtaleFundamentalGroups

end
