/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Localization.Away.Basic
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenLocalization
import Nyll.SchemeTheory.Normalization.IntegralClosure.IntegralBase.Equiv

/-!
# A chosen local factor of one normalization after an integral base change

Let `A → B` be finite, with `B` Henselian local, and let both rings act on
one ambient field `L`.  The integral closures over `A` and `B` are the same
subring of `L`; `IntegralClosureIntegralBaseEquiv` equips that literal
`A`-normalization with its canonical `B`-algebra structure.

If the normalization is etale over `B`, localization at a chosen prime over
the closed point is a finite etale local factor.  Its maximal ideal is the
unique prime over the closed point.  This file also transports an independently
given primitive `A`-away hypothesis from the original normalization to this
chosen factor.  Thus the away hypothesis below is source data from the
original finite normalization, not an etaleness assumption on the desired
chosen factor.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe uA uB uC uD uL

/-- A finite formally-etale extension of an algebra already etale away from
`f` remains etale after applying the literal away map from the original
base.  This is the map-level composition needed after selecting a finite
local factor of a normalization. -/
theorem localization_awayMap_etale_of_finite_formallyEtale_extension
    {A : Type uA} {C : Type uC} {D : Type uD}
    [CommRing A] [CommRing C] [CommRing D]
    [IsNoetherianRing A]
    [Algebra A C] [Algebra C D] [Algebra A D]
    [IsScalarTower A C D]
    [Module.Finite A D] [Algebra.FormallyEtale C D]
    (f : A)
    (hAway : (Localization.awayMap (algebraMap A C) f).Etale) :
    (Localization.awayMap (algebraMap A D) f).Etale := by
  let fC : C := algebraMap A C f
  let fD : D := algebraMap A D f
  let S := Localization.Away f
  let T := Localization.Away fC
  let U := Localization.Away fD
  let mapST : S →+* T := Localization.awayMap (algebraMap A C) f
  let mapCDU : C →+* U := algebraMap C U
  have hfCUnit : IsUnit (mapCDU fC) := by
    change IsUnit (algebraMap D U (algebraMap C D (algebraMap A C f)))
    rw [← IsScalarTower.algebraMap_apply A C D f]
    exact IsLocalization.Away.algebraMap_isUnit fD
  let mapTU : T →+* U := Localization.awayLift mapCDU fC hfCUnit
  let mapSU : S →+* U := Localization.awayMap (algebraMap A D) f
  let : Algebra S T := mapST.toAlgebra
  let : Algebra T U := mapTU.toAlgebra
  let : IsScalarTower C T U :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change mapCDU c = mapTU (algebraMap C T c)
      simp [mapTU]
  let : IsLocalization
      ((Submonoid.powers fC).map (algebraMap C D)) U := by
    rw [Submonoid.map_powers, show algebraMap C D fC = fD by
      exact (IsScalarTower.algebraMap_apply A C D f).symm]
    infer_instance
  let : Algebra.FormallyEtale T U :=
    Algebra.FormallyEtale.localization_map
      (R := C) (S := D) (Rₘ := T) (Sₘ := U)
      (Submonoid.powers fC)
  have hcomp : mapTU.comp mapST = mapSU := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    calc
      mapTU (mapST (algebraMap A S a)) =
          mapTU (algebraMap C T (algebraMap A C a)) := by
        rw [show mapST (algebraMap A S a) =
            algebraMap C T (algebraMap A C a) by
          simp [mapST, S, T, fC, IsLocalization.Away.map]]
      _ = mapCDU (algebraMap A C a) := by simp [mapTU]
      _ = algebraMap D U (algebraMap C D (algebraMap A C a)) := rfl
      _ = algebraMap D U (algebraMap A D a) := by
        rw [IsScalarTower.algebraMap_apply A C D a]
      _ = mapSU (algebraMap A S a) := by
        simp [mapSU, S, U, fD, IsLocalization.Away.map]
  let : Algebra S U := mapSU.toAlgebra
  let : IsScalarTower S T U :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (DFunLike.congr_fun hcomp x).symm
  let : Algebra.Etale S T := hAway.toAlgebra
  let : Algebra.FormallyEtale S U :=
    Algebra.FormallyEtale.comp S T U
  let : IsScalarTower A S U :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A U a = mapSU (algebraMap A S a)
      rw [show mapSU (algebraMap A S a) =
          algebraMap D U (algebraMap A D a) by
        simp [mapSU, S, U, fD, IsLocalization.Away.map]]
      exact IsScalarTower.algebraMap_apply A D U a
  let : IsLocalization
      ((Submonoid.powers f).map (algebraMap A D)) U := by
    rw [Submonoid.map_powers]
    exact (inferInstance : IsLocalization.Away fD U)
  let : Module.Finite S U :=
    Module.Finite.of_isLocalization A D (Submonoid.powers f)
  let : Module.FinitePresentation S U :=
    Module.finitePresentation_of_finite S U
  let : Algebra.FinitePresentation S U :=
    Algebra.FinitePresentation.of_finitePresentation S U
  exact (show Algebra.Etale S U from
    { formallyEtale := inferInstance
      finitePresentation := inferInstance })

/-- The chosen localization of the common normalization is a finite etale
factor over the integral Henselian base, has one prime over the closed point,
and retains the literal primitive `A`-away map.

The input `hAway` is exactly the boundary-complement hypothesis on the
original `A`-normalization `integralClosure A L`.  Etaleness, finiteness,
closed-prime uniqueness, and the away property of the selected factor are
all produced here; no comparison equivalence or endpoint property is an
input. -/
theorem integralClosure_integralBase_chosenLocalization_finiteEtale_unique_away
    {A : Type uA} {B : Type uB} {L : Type uL}
    [CommRing A] [CommRing B] [Field L]
    [IsNoetherianRing A]
    [HenselianLocalRing B]
    [Algebra A B] [Module.Finite A B]
    [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    (hEtale : Algebra.Etale B (integralClosure B L))
    (f : A)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A L)) f).Etale) :
    let C := integralClosure A L
    letI : Algebra B C := integralClosureIntegralBaseAlgebra
    letI : IsScalarTower A B C :=
      integralClosureIntegralBase_isScalarTower
    ∀ (q : Ideal C) [q.IsPrime]
      [q.LiesOver (maximalIdeal B)],
      let D := Localization.AtPrime q
      Module.Finite B D ∧
        Algebra.Etale B D ∧
        (maximalIdeal D).LiesOver (maximalIdeal B) ∧
        (∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (maximalIdeal B) → Q = maximalIdeal D) ∧
        @Algebra.Etale
          (Localization.Away f)
          (Localization.Away
            (algebraMap A D f))
          _ _
          (Localization.awayMap
            (algebraMap A D) f).toAlgebra := by
  dsimp only
  let C := integralClosure A L
  let : Algebra B C := integralClosureIntegralBaseAlgebra
  let : IsScalarTower A B C :=
    integralClosureIntegralBase_isScalarTower
  let : Algebra.Etale B C :=
    integralClosure_etale_of_integralBase hEtale
  intro q _ _
  let D := Localization.AtPrime q
  /- The canonical localization algebras make `A → D` the localization of
  the original normalization map, and make it agree with `A → B → D`. -/
  let : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq
      (R := A) (S := B) (A := D) fun a ↦ by
        calc
          algebraMap A D a = algebraMap C D (algebraMap A C a) :=
            IsScalarTower.algebraMap_apply A C D a
          _ = algebraMap C D
              (algebraMap B C (algebraMap A B a)) := by
            rw [IsScalarTower.algebraMap_apply A B C a]
          _ = algebraMap B D (algebraMap A B a) :=
            (IsScalarTower.algebraMap_apply B C D
              (algebraMap A B a)).symm
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let : Module.Finite B D :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale q
  have hEtaleD : Algebra.Etale B D := by
    let : Module.FinitePresentation B D :=
      Module.finitePresentation_of_finite B D
    let : Algebra.FinitePresentation B D :=
      Algebra.FinitePresentation.of_finitePresentation B D
    exact
      { formallyEtale := inferInstance
        finitePresentation := inferInstance }
  let : Algebra.Etale B D := hEtaleD
  let : Module.Finite A D := Module.Finite.trans B D
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal q
  have hclosedOver : (maximalIdeal D).LiesOver (maximalIdeal B) :=
    inferInstance
  have hunique : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver (maximalIdeal B) → Q = maximalIdeal D := by
    intro Q hQPrime hQOver
    let : Q.IsPrime := hQPrime
    let : Q.LiesOver (maximalIdeal B) := hQOver
    let : Algebra.IsIntegral B D := Algebra.IsIntegral.of_finite B D
    have hQMaximal : Q.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap B D)
        (fun x ↦ Algebra.IsIntegral.isIntegral x) Q <| by
          rw [← Ideal.under_def, ← Q.over_def (maximalIdeal B)]
          exact IsLocalRing.maximalIdeal.isMaximal B
    exact IsLocalRing.eq_maximalIdeal hQMaximal
  have hAwayD :=
    localization_awayMap_etale_of_finite_formallyEtale_extension
      (A := A) (C := C) (D := D) f hAway
  exact ⟨inferInstance, hEtaleD, hclosedOver, hunique, hAwayD⟩

end EtaleFundamentalGroups

end
