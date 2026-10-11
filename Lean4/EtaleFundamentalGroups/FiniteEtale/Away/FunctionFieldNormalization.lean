/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
import SchemeTheory.Normalization.Localization.IntegralClosureAwayEquiv

/-!
# A finite-etale function-field normalization on an away open

A connected finite-etale cover of `Spec (A[1/f])` determines a canonical
extension of the fraction field of `A`.  This file identifies the algebra
structure supplied by the cover with the canonical localization algebra and
returns finite etaleness for the literal away map of the normalization over
`A`.
-/

noncomputable section

open AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- The canonical `A`-algebra structure on the function field of
`Spec (A[1/f])`, obtained by composing the localization map with germs at the
generic point. -/
@[reducible] noncomputable def localizationAwaySpecFunctionFieldAlgebra
    {A : Type u} [CommRing A] [IsDomain A]
    (f : A) (hf : f ≠ 0) :
    let S := Localization.Away f
    letI : IsDomain S := IsLocalization.Away.isDomain S hf
    Algebra A (Spec (.of S)).functionField := by
  dsimp only
  letI : IsDomain (Localization.Away f) :=
    IsLocalization.Away.isDomain (Localization.Away f) hf
  letI : Algebra (Localization.Away f)
      (Spec (.of (Localization.Away f))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
      (.of (Localization.Away f))
  exact ((algebraMap (Localization.Away f)
    (Spec (.of (Localization.Away f))).functionField).comp
      (algebraMap A (Localization.Away f))).toAlgebra

/-- The function field of `Spec (A[1/f])` is also a fraction field of `A`
for the composite algebra structure. -/
theorem localizationAwaySpecFunctionField_isFractionRing
    {A : Type u} [CommRing A] [IsDomain A]
    (f : A) (hf : f ≠ 0) :
    let S := Localization.Away f
    let X := Spec (.of S)
    letI : IsDomain S := IsLocalization.Away.isDomain S hf
    letI : Algebra A X.functionField :=
      localizationAwaySpecFunctionFieldAlgebra f hf
    IsFractionRing A X.functionField := by
  dsimp only
  let S := Localization.Away f
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let K : Type u := (Spec (.of S)).functionField
  let : Algebra S K :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of S)
  let : Algebra A K := localizationAwaySpecFunctionFieldAlgebra f hf
  let : IsScalarTower A S K := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  let : IsFractionRing S K :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine (.of S)
  have hpow : Submonoid.powers f ≤ nonZeroDivisors A :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf)
  have hsub :
      IsLocalization.localizationLocalizationSubmodule
          (Submonoid.powers f) (nonZeroDivisors S) =
        nonZeroDivisors A := by
    ext x
    rw [IsLocalization.mem_localizationLocalizationSubmodule,
      mem_nonZeroDivisors_iff_ne_zero]
    constructor
    · rintro ⟨y, z, hxyz⟩ hx
      subst x
      have hy : (y : S) ≠ 0 := by
        exact mem_nonZeroDivisors_iff_ne_zero.mp y.property
      have hz : algebraMap A S (z : A) ≠ 0 :=
        (IsLocalization.map_units S z).ne_zero
      exact (mul_ne_zero hy hz) (by simpa using hxyz.symm)
    · intro hx
      refine ⟨⟨algebraMap A S x, ?_⟩, 1, ?_⟩
      · rw [mem_nonZeroDivisors_iff_ne_zero]
        simpa using (IsLocalization.injective S hpow).ne hx
      · simp
  have hloc :
      IsLocalization
        (IsLocalization.localizationLocalizationSubmodule
          (Submonoid.powers f) (nonZeroDivisors S)) K :=
    IsLocalization.localization_localization_isLocalization
      (Submonoid.powers f) (nonZeroDivisors S) K
  change IsLocalization (nonZeroDivisors A) K
  rw [← hsub]
  exact hloc

/-- The canonical `A`-algebra structure on the function field of a connected
finite-etale cover of `Spec (A[1/f])`. -/
@[reducible] noncomputable def finiteEtaleAwayFunctionFieldAlgebra
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A]
    (f : A) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y] :
    let S := Localization.Away f
    letI : IsDomain S := IsLocalization.Away.isDomain S hf
    letI : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    Algebra A Y.left.functionField := by
  dsimp only
  let S := Localization.Away f
  letI : IsDomain S := IsLocalization.Away.isDomain S hf
  letI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Algebra S Y.left.functionField :=
    finiteEtaleSpecFunctionFieldAlgebra (.of S) Y
  exact ((algebraMap S Y.left.functionField).comp (algebraMap A S)).toAlgebra

/-- The canonical `A`-algebra structure on the cover's function field
factors through the function field of `Spec (A[1/f])`. -/
theorem finiteEtaleAway_functionField_isScalarTower
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A]
    (f : A) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y] :
    let S := Localization.Away f
    let X := Spec (.of S)
    letI : IsDomain S := IsLocalization.Away.isDomain S hf
    letI : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra A X.functionField :=
      localizationAwaySpecFunctionFieldAlgebra f hf
    letI : Algebra A Y.left.functionField :=
      finiteEtaleAwayFunctionFieldAlgebra f hf Y
    IsScalarTower A X.functionField Y.left.functionField := by
  dsimp only
  let S := Localization.Away f
  let X := Spec (.of S)
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K : Type u := X.functionField
  let L : Type u := Y.left.functionField
  let : Algebra S K :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of S)
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra A K := localizationAwaySpecFunctionFieldAlgebra f hf
  let : Algebra S L := finiteEtaleSpecFunctionFieldAlgebra (.of S) Y
  let : Algebra A L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
  let : IsScalarTower A S K := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  let : IsScalarTower S K L :=
    finiteEtaleSpec_functionField_isScalarTower (.of S) Y
  apply IsScalarTower.of_algebraMap_eq
  intro x
  calc
    algebraMap A L x = algebraMap S L (algebraMap A S x) := rfl
    _ = algebraMap K L (algebraMap S K (algebraMap A S x)) :=
      IsScalarTower.algebraMap_apply S K L (algebraMap A S x)
    _ = algebraMap K L (algebraMap A K x) := by
      rw [IsScalarTower.algebraMap_apply A S K]

/-- A connected finite-etale cover of `Spec (A[1/f])` makes the literal
normalization of `A` finite etale after inverting `f`.

This uses only normality and Noetherianity of `A`; it has no finite-type,
Nagata, or arithmetic-base hypothesis. -/
theorem localization_away_integralClosure_functionField_etale_of_finiteEtale
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A]
    (f : A) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y] :
    let S := Localization.Away f
    let X := Spec (.of S)
    letI : IsDomain S := IsLocalization.Away.isDomain S hf
    letI : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra A X.functionField :=
      localizationAwaySpecFunctionFieldAlgebra f hf
    letI : Algebra A Y.left.functionField :=
      finiteEtaleAwayFunctionFieldAlgebra f hf Y
    (Localization.awayMap
      (algebraMap A (integralClosure A Y.left.functionField)) f).Etale := by
  dsimp only
  let S := Localization.Away f
  let X := Spec (.of S)
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K : Type u := X.functionField
  let L : Type u := Y.left.functionField
  let : Algebra S K :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of S)
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra A K := localizationAwaySpecFunctionFieldAlgebra f hf
  let coverSL : Algebra S L :=
    finiteEtaleSpecFunctionFieldAlgebra (.of S) Y
  let : Algebra S L := coverSL
  let : Algebra A L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
  let : IsScalarTower A S K := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  let : IsScalarTower S K L :=
    finiteEtaleSpec_functionField_isScalarTower (.of S) Y
  let : IsScalarTower A K L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap A L x = algebraMap S L (algebraMap A S x) := rfl
      _ = algebraMap K L (algebraMap S K (algebraMap A S x)) :=
        IsScalarTower.algebraMap_apply S K L (algebraMap A S x)
      _ = algebraMap K L (algebraMap A K x) := by
        rw [IsScalarTower.algebraMap_apply A S K]
  let : IsFractionRing S K :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine (.of S)
  let : IsFractionRing A K :=
    localizationAwaySpecFunctionField_isFractionRing f hf
  have hSKL (z : S) :
      (@algebraMap S L _ _ coverSL) z =
        algebraMap K L (algebraMap S K z) :=
    IsScalarTower.algebraMap_apply S K L z
  have hAKL (x : A) :
      algebraMap A L x = algebraMap K L (algebraMap A K x) :=
    IsScalarTower.algebraMap_apply A K L x
  let canonicalSL : Algebra S L :=
    localizationAwayToExtensionAlgebra (A := A) (K := K) (L := L) f hf
  have hAlgebra : coverSL = canonicalSL := by
    have hmaps :
        (@algebraMap S L _ _ coverSL) =
          (@algebraMap S L _ _ canonicalSL) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      apply DFunLike.ext _ _
      intro x
      calc
        (@algebraMap S L _ _ coverSL) (algebraMap A S x) =
            algebraMap K L (algebraMap S K (algebraMap A S x)) :=
          hSKL (algebraMap A S x)
        _ = algebraMap K L (algebraMap A K x) := by
          rw [IsScalarTower.algebraMap_apply A S K]
        _ = algebraMap A L x :=
          (hAKL x).symm
        _ = (@algebraMap S L _ _ canonicalSL) (algebraMap A S x) := by
          change algebraMap A L x =
            (IsLocalization.Away.lift f _) (algebraMap A S x)
          rw [IsLocalization.Away.lift_eq]
    apply Algebra.algebra_ext
    intro z
    exact DFunLike.congr_fun hmaps z
  have hCover :=
    integralClosure_functionField_etale_of_finiteEtale_spec (.of S) Y
  have hCanonical :
      @Algebra.Etale S (@integralClosure S L _ _ canonicalSL) _ _
        (@integralClosure S L _ _ canonicalSL).algebra := by
    exact hAlgebra ▸ hCover
  let : Algebra S L := canonicalSL
  let : IsScalarTower A S L :=
    localizationAwayToExtension_isScalarTower (K := K) f hf
  exact localization_integralClosure_away_etale_of_local_integralClosure_etale
    (A := A) (K := K) (L := L) f hf hCanonical

end EtaleFundamentalGroups

end
