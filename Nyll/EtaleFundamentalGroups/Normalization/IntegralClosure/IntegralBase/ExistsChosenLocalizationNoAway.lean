/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenLocalization
import Nyll.SchemeTheory.Normalization.IntegralClosure.IntegralBase.Equiv

/-!
# Existence of a finite etale local normalization factor

For a finite integral enlargement `A → B` with `B` Henselian local, a prime
of the common normalization over the closed point exists by lying over.  If
the normalization is etale over `B`, localization at that prime is finite
etale over `B`; its maximal ideal is the unique prime over the closed point.

Unlike the boundary-away refinement, this construction has no away-map input.
It can therefore be used to choose the local factor before a boundary-away
property has been produced for it.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe uA uB uL

/-- The common normalization has a finite etale local factor over the closed
point of the integral Henselian base.  The chosen factor has exactly one prime
over that closed point. -/
theorem
    exists_integralClosure_integralBase_chosenLocalization_finiteEtale_unique
    {A : Type uA} {B : Type uB} {L : Type uL}
    [CommRing A] [CommRing B] [Field L]
    [IsNoetherianRing A]
    [HenselianLocalRing B]
    [Algebra A B] [Module.Finite A B]
    [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    (hEtale : Algebra.Etale B (integralClosure B L)) :
    let C := integralClosure A L
    letI : Algebra B C := integralClosureIntegralBaseAlgebra
    letI : IsScalarTower A B C :=
      integralClosureIntegralBase_isScalarTower
    ∃ (q : Ideal C) (_ : q.IsPrime)
      (_ : q.LiesOver (maximalIdeal B)),
      let D := Localization.AtPrime q
      Module.Finite B D ∧
        Algebra.Etale B D ∧
        (maximalIdeal D).LiesOver (maximalIdeal B) ∧
        (∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (maximalIdeal B) → Q = maximalIdeal D) := by
  dsimp only
  let C := integralClosure A L
  let : Algebra B C := integralClosureIntegralBaseAlgebra
  let : IsScalarTower A B C :=
    integralClosureIntegralBase_isScalarTower
  let : Algebra.IsIntegral A C :=
    IsIntegralClosure.isIntegral_algebra A L
  let : Algebra.IsIntegral B C :=
    Algebra.IsIntegral.tower_top A
  have hker : RingHom.ker (algebraMap B C) ≤ maximalIdeal B :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap B C))
  obtain ⟨q, hqMaximal, hqComap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal B) hker
  let : q.IsPrime := hqMaximal.isPrime
  let : q.LiesOver (maximalIdeal B) :=
    (Ideal.liesOver_iff q (maximalIdeal B)).mpr hqComap.symm
  let : Algebra.Etale B C :=
    integralClosure_etale_of_integralBase hEtale
  let D := Localization.AtPrime q
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
  exact ⟨q, inferInstance, inferInstance,
    inferInstance, hEtaleD, hclosedOver, hunique⟩

end EtaleFundamentalGroups

end
