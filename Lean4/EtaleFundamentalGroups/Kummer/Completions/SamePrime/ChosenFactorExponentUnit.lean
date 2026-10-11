/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.FiniteEtale.SamePrimeBoundaryAway
import SchemeTheory.FiniteEtale.Henselian.ChosenLocalizationEtale
import EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.ExponentUnit.BoundaryAway
import EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.ExponentUnit.PrimeOrUnit

/-!
# Exponent units from the literal same-prime completion factor

Suppose that a finite etale algebra over a finite radical cover has been
localized at a chosen closed prime, and that its boundary Away map is etale.
After a Henselian faithfully-flat pushout, the exact mapped prime in the
base-changed algebra has a finite etale localization.  That literal
localization is already a valid chosen factor for the complete-factor
exponent obstruction.

In particular, one does not need to identify it with an independently
selected normalization prime or generic-fibre component.  The only prime
used below is the mapped source prime, and the only local factor is its
localization.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing

universe uA₀ uB₀ uA uE

/-- The literal localization at the mapped prime after a finite Henselian
pushout detects all exponents of the target iterated radical.

`A₀ → B₀` is the finite cover before the faithfully-flat base change,
`A` is the new boundary base, and the target pushout ring is the explicit
iterated radical `B`.  The finite etale algebra `E / B₀` is localized first
at `p`; its primitive boundary Away map is transported to the exact mapped
prime in `B ⊗[B₀] E` by
`finiteEtale_samePrime_boundaryAway_of_finite_henselianPushout`.

The conclusion has no comparison with an independently chosen completed
factor, tensor component, or normalization prime. -/
theorem
all_exponents_isUnit_of_finiteEtale_samePrime_boundaryAway_primeOrUnit_of_finite_henselianPushout
    {A₀ : Type uA₀} {B₀ : Type uB₀}
    {A : Type uA} {E : Type uE}
    [CommRing A₀] [CommRing B₀] [CommRing A] [CommRing E]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalRing B₀]
    [Algebra A₀ B₀] [Algebra A₀ A]
    [Module.Finite A₀ B₀]
    [Algebra B₀ E] [Algebra A₀ E] [IsScalarTower A₀ B₀ E]
    [Module.Finite B₀ E] [Algebra.Etale B₀ E]
    (p : Ideal E) [p.IsMaximal]
    [p.LiesOver (maximalIdeal B₀)]
    {r b : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i, a i ∈ maximalIdeal A ∨ n i = 1)
    (s : Fin b → A)
    (hsPrimeOrUnit : ∀ i, Prime (s i) ∨ IsUnit (s i))
    (hCharZero : ∀ i, Prime (s i) →
      CharZero (A ⧸ Ideal.span {s i}))
    (f₀ : A₀)
    (hAssoc : Associated (algebraMap A₀ A f₀) (∏ i, s i))
    (hAway :
      (Localization.awayMap
        (algebraMap A₀ (Localization.AtPrime p)) f₀).Etale) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    ∀ [HenselianLocalRing B]
      [Algebra A₀ B] [Algebra B₀ B]
      [IsScalarTower A₀ B₀ B] [IsScalarTower A₀ A B]
      [Algebra.IsPushout A₀ B₀ A B]
      [IsLocalHom (algebraMap B₀ B)]
      [Module.FaithfullyFlat B₀ B],
      ((maximalIdeal B₀).map (algebraMap B₀ B) = maximalIdeal B) →
      Function.Bijective
          (IsLocalRing.ResidueField.map (algebraMap B₀ B)) →
      ∀ i, IsUnit (n i : A) := by
  dsimp only
  intro _ _ _ _ _ _ _ _ hmax hres
  let B := iteratedRadical A r n a
  let T := B ⊗[B₀] E
  let : Algebra B T := Algebra.TensorProduct.leftAlgebra
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B₀ B T := inferInstance
  let : IsScalarTower B₀ E T :=
    Algebra.TensorProduct.right_isScalarTower
  let p' := p.map (algebraMap E T)
  have hgeometry :=
    tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R := B₀) (R' := B) (S := E) p hmax hres
  let : p'.IsPrime := hgeometry.1.isPrime
  let : p'.LiesOver (maximalIdeal B) := hgeometry.2
  let D := Localization.AtPrime p'
  let : Algebra T D := OreLocalization.instAlgebra
  let : Algebra B D := OreLocalization.instAlgebra
  let : IsScalarTower B T D := OreLocalization.instIsScalarTower
  let aDAlgebra : Algebra A D :=
    ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  let : Algebra A D := aDAlgebra
  have hAwayCompleted :=
    finiteEtale_samePrime_boundaryAway_of_finite_henselianPushout
      (A := A₀) (B := B₀) (A' := A) (B' := B) (E := E)
      p hmax hres f₀ hAway
  let : Module.Finite B D :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale p'
  let : Algebra.Etale B D :=
    etale_localizationAtPrime_of_henselian_of_etale p'
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal p'
  let qD := maximalIdeal D
  let : qD.IsPrime := (maximalIdeal.isMaximal D).isPrime
  let : qD.LiesOver (maximalIdeal B) := inferInstance
  have hunique : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver (maximalIdeal B) → Q = qD := by
    intro Q hQPrime hQOver
    let : Q.IsPrime := hQPrime
    let : Q.LiesOver (maximalIdeal B) := hQOver
    let : Algebra.IsIntegral B D := Algebra.IsIntegral.of_finite B D
    have hQMaximal : Q.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap B D)
        (fun x ↦ Algebra.IsIntegral.isIntegral x) Q <| by
          rw [← Ideal.under_def, ← Q.over_def (maximalIdeal B)]
          exact maximalIdeal.isMaximal B
    exact IsLocalRing.eq_maximalIdeal hQMaximal
  let : SMul A D := aDAlgebra.toSMul
  let : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    all_exponents_isUnit_of_completeChosenFactor_boundaryAway_primeOrUnit_universe
      (A := A) n a hn hstage s hsPrimeOrUnit hCharZero
      (algebraMap A₀ A f₀) hAssoc (D := D) qD hunique hAwayCompleted

/-- Compatibility wrapper for callers whose completed boundary factors are
all prime. -/
theorem
    all_exponents_isUnit_of_finiteEtale_samePrime_boundaryAway_of_finite_henselianPushout
    {A₀ : Type uA₀} {B₀ : Type uB₀}
    {A : Type uA} {E : Type uE}
    [CommRing A₀] [CommRing B₀] [CommRing A] [CommRing E]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalRing B₀]
    [Algebra A₀ B₀] [Algebra A₀ A]
    [Module.Finite A₀ B₀]
    [Algebra B₀ E] [Algebra A₀ E] [IsScalarTower A₀ B₀ E]
    [Module.Finite B₀ E] [Algebra.Etale B₀ E]
    (p : Ideal E) [p.IsMaximal]
    [p.LiesOver (maximalIdeal B₀)]
    {r b : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i, a i ∈ maximalIdeal A ∨ n i = 1)
    (s : Fin b → A)
    (hsPrime : ∀ i, Prime (s i))
    (hCharZero : ∀ i, CharZero (A ⧸ Ideal.span {s i}))
    (f₀ : A₀)
    (hAssoc : Associated (algebraMap A₀ A f₀) (∏ i, s i))
    (hAway :
      (Localization.awayMap
        (algebraMap A₀ (Localization.AtPrime p)) f₀).Etale) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    ∀ [HenselianLocalRing B]
      [Algebra A₀ B] [Algebra B₀ B]
      [IsScalarTower A₀ B₀ B] [IsScalarTower A₀ A B]
      [Algebra.IsPushout A₀ B₀ A B]
      [IsLocalHom (algebraMap B₀ B)]
      [Module.FaithfullyFlat B₀ B],
      ((maximalIdeal B₀).map (algebraMap B₀ B) = maximalIdeal B) →
      Function.Bijective
          (IsLocalRing.ResidueField.map (algebraMap B₀ B)) →
      ∀ i, IsUnit (n i : A) := by
  exact
    (
all_exponents_isUnit_of_finiteEtale_samePrime_boundaryAway_primeOrUnit_of_finite_henselianPushout
      (A₀ := A₀) (B₀ := B₀) (A := A) (E := E)
      p n a hn hstage s (fun i ↦ Or.inl (hsPrime i))
        (fun i _ ↦ hCharZero i) f₀ hAssoc hAway)

end EtaleFundamentalGroups.Kummer

end
