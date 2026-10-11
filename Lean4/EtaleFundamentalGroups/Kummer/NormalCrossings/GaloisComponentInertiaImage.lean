/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PullbackComponentQuotient
import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeNormalCrossingsComponentInertia

/-!
# Inertia images from Galois pullback components

The pointed quotient ideal-inertia subgroup of a Galois pullback component
maps injectively into the deck group of the original cover.  Consequently,
the local normal-crossings coprimality statement remains true for its actual
image in the original finite quotient.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory IsLocalRing
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- Local pointed quotient ideal inertia remains prime to `p` after mapping
from an actual Galois pullback component to the original cover deck group. -/
theorem galoisPullbackComponent_mappedQuotientIdealInertia_coprime
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsRegularRing V] [IsIntegrallyClosed V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r)
    (qV : Ideal V) (p : ℕ)
    {U : Scheme.{u}} [ConnectedSpace U]
    (c : Spec (.of (Localization.Away (boundaryProduct t r))) ⟶ U)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶
      Spec (.of (Localization.Away (boundaryProduct t r))))
    (W : FiniteEtale U)
    (hW : CategoryTheory.PreGaloisCategory.IsGalois W)
    (w : (FiniteEtale.fiber (xi ≫ c)).obj W)
    (Z : FiniteEtale
      (Spec (.of (Localization.Away (boundaryProduct t r)))))
    (i : Z ⟶ (FiniteEtale.pullback c).obj W)
    (z : (FiniteEtale.fiber xi).obj Z)
    (hiz : (FiniteEtale.fiber xi).map i z =
      transportedPointOfCompIso
        (FiniteEtale.pullback c) (FiniteEtale.pullbackFiberIso c xi) W w)
    (hi : Mono i) :
    let f := boundaryProduct t r
    let hf :=
      EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
        hNC
    let S := Localization.Away f
    letI : IsDomain S := IsLocalization.Away.isDomain S hf
    letI : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    ∀ (hZ : CategoryTheory.PreGaloisCategory.IsGalois Z),
    letI : CategoryTheory.PreGaloisCategory.IsGalois Z := hZ
    letI : IsIntegral Z.left :=
      isIntegral_left_of_isConnected_finiteEtale Z
    let K := (Spec (.of S)).functionField
    let L := Z.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Z
    letI : Algebra V K := localizationAwaySpecFunctionFieldAlgebra f hf
    letI : Algebra V L := finiteEtaleAwayFunctionFieldAlgebra f hf Z
    letI : IsScalarTower V K L :=
      finiteEtaleAway_functionField_isScalarTower f hf Z
    letI : IsFractionRing V K :=
      localizationAwaySpecFunctionField_isFractionRing f hf
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected Z
    letI : _root_.IsGalois K L :=
      isGalois_functionField_of_isGalois_finiteEtale Z hZ
    let B := integralClosure V L
    letI : IsFractionRing B L :=
      IsIntegralClosure.isFractionRing_of_finite_extension V K L B
    letI : MulSemiringAction Gal(L/K) B :=
      IsIntegralClosure.MulSemiringAction V K L B
    letI : MulSemiringAction (Aut Z)ᵐᵒᵖ B :=
      EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
        Z hZ V B
    GaloisCoverQuotientIdealInertiaCoprime hNC qV Z p →
    ∀ (Q : Ideal B) (_ : Q.IsPrime), Q.LiesOver qV →
      let qZ := finiteEtaleGaloisCoverQuotientMonoidHom xi Z hZ z
      let H := Subgroup.map qZ
        (Subgroup.comap qZ (Q.toAddSubgroup.inertia (Aut Z)ᵐᵒᵖ))
      Nat.Coprime
        (Nat.card (H.map
          (FiniteEtale.galoisPullbackComponentQuotientMonoidHom
            c xi W hW w Z i z hiz hZ hi))) p := by
  dsimp only
  let f := boundaryProduct t r
  have hf : f ≠ 0 :=
    EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hNC
  let S := Localization.Away f
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  intro hZ
  let : CategoryTheory.PreGaloisCategory.IsGalois Z := hZ
  let : IsIntegral Z.left :=
    isIntegral_left_of_isConnected_finiteEtale Z
  let K := (Spec (.of S)).functionField
  let L := Z.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Z
  let : Algebra V K := localizationAwaySpecFunctionFieldAlgebra f hf
  let : Algebra V L := finiteEtaleAwayFunctionFieldAlgebra f hf Z
  let : IsScalarTower V K L :=
    finiteEtaleAway_functionField_isScalarTower f hf Z
  let : IsFractionRing V K :=
    localizationAwaySpecFunctionField_isFractionRing f hf
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Z
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Z hZ
  let B := integralClosure V L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L B
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction V K L B
  let : MulSemiringAction (Aut Z)ᵐᵒᵖ B :=
    EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
      Z hZ V B
  intro hLocal Q hQprime hQ
  let : Q.IsPrime := hQprime
  let qZ := finiteEtaleGaloisCoverQuotientMonoidHom xi Z hZ z
  let H := Subgroup.map qZ
    (Subgroup.comap qZ (Q.toAddSubgroup.inertia (Aut Z)ᵐᵒᵖ))
  have hH : Nat.Coprime (Nat.card H) p := by
    exact hLocal hZ xi z Q inferInstance hQ
  exact
    (FiniteEtale.galoisPullbackComponentQuotientMonoidHom_map_coprime_iff
      c xi W hW w Z i z hiz hZ hi H p).2 hH

end AlgebraicGeometry.Scheme.IdealSheafData

end
