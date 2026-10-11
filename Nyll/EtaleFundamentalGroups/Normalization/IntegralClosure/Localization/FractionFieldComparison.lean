/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.Integral
import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization

/-!
# The fraction field of a chosen normalization localization

Let `M` be a finite extension of the fraction field of a domain `B`.  The
integral closure `C` of `B` in `M` has fraction field `M`; localizing `C` at
any prime does not change that fraction field.  Consequently the literal
`FractionRing (Localization.AtPrime q)` of a chosen local normalization
factor is canonically equivalent to the *same supplied field* `M`.

This is the comparison needed for a completed chosen generic factor.  In
that application `M` is the already selected quotient of the original
fraction-field tensor product.  No embedding into an unrelated full-root
field and no right-coordinate bijectivity hypothesis is introduced.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uB uK uM

/-- The fraction field of a chosen prime localization of a normalization is
the original finite fraction-field component.

Both algebra structures are source-produced: first `M` is made the fraction
field of `integralClosure B M`, then the canonical localization lift gives
the action of the chosen local factor on `M`. -/
noncomputable def
    integralClosureLocalizationFractionRingAlgEquiv
    {B : Type uB} {K : Type uK} {M : Type uM}
    [CommRing B] [IsDomain B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Field M] [Algebra B M] [Algebra K M]
    [IsScalarTower B K M] [FiniteDimensional K M]
    (q : Ideal (integralClosure B M)) [q.IsPrime] :
    let C := integralClosure B M
    letI : IsFractionRing C M :=
      IsIntegralClosure.isFractionRing_of_finite_extension B K M C
    let D := Localization.AtPrime q
    letI : Algebra D M :=
      localizationAtPrimeToFractionFieldAlgebra (K := M) q
    FractionRing D ≃ₐ[D] M := by
  dsimp only
  let C := integralClosure B M
  letI : IsFractionRing C M :=
    IsIntegralClosure.isFractionRing_of_finite_extension B K M C
  let D := Localization.AtPrime q
  letI : Algebra D M :=
    localizationAtPrimeToFractionFieldAlgebra (K := M) q
  letI : IsFractionRing D M :=
    localizationAtPrimeToFractionField_isFractionRing (K := M) q
  exact FractionRing.algEquiv D M

@[simp]
theorem integralClosureLocalizationFractionRingAlgEquiv_algebraMap
    {B : Type uB} {K : Type uK} {M : Type uM}
    [CommRing B] [IsDomain B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    [Field M] [Algebra B M] [Algebra K M]
    [IsScalarTower B K M] [FiniteDimensional K M]
    (q : Ideal (integralClosure B M)) [q.IsPrime]
    (x : Localization.AtPrime q) :
    let C := integralClosure B M
    letI : IsFractionRing C M :=
      IsIntegralClosure.isFractionRing_of_finite_extension B K M C
    let D := Localization.AtPrime q
    letI : Algebra D M :=
      localizationAtPrimeToFractionFieldAlgebra (K := M) q
    integralClosureLocalizationFractionRingAlgEquiv
        (B := B) (K := K) (M := M) q
        (algebraMap D (FractionRing D) x) =
      algebraMap D M x := by
  dsimp only
  let C := integralClosure B M
  let : IsFractionRing C M :=
    IsIntegralClosure.isFractionRing_of_finite_extension B K M C
  let D := Localization.AtPrime q
  let : Algebra D M :=
    localizationAtPrimeToFractionFieldAlgebra (K := M) q
  exact
    (integralClosureLocalizationFractionRingAlgEquiv
      (B := B) (K := K) (M := M) q).commutes x

end EtaleFundamentalGroups

end
