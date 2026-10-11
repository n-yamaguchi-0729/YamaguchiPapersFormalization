/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Completions.SamePrime.ChosenFactorExponentUnit
import EtaleFundamentalGroups.Kummer.Completions.Conditional.IteratedRadical
import EtaleFundamentalGroups.Kummer.LocalGeometry.HeightTwo.MaximalAdicCompletionGeometry

/-!
# Conditional radical exponents from the same prime after completion

This leaf installs all completion plumbing around the literal same-prime
terminal.  A finite-etale algebra and one closed prime are chosen before
completion.  The exact mapped prime after completion then detects the
exponents of the completed conditional radical, and locality of the
completion map descends the resulting units to the original base.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing

universe uA uE

/-- Complete a conditional iterated radical at its closed point and apply
the literal same-prime chosen-factor obstruction.

The only completion geometry left as data is that the completed base is a
domain and that every prime boundary factor remains prime.  In the
height-two strict-normal-crossings application both statements are produced
by `maximalAdicCompletion_regularPair_geometry`; unit boundary factors are
preserved automatically. -/
theorem
    all_exponents_isUnit_of_conditionalIteratedRadical_samePrime_completion
    {A : Type uA} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A]
    {r b : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i, a i ∈ maximalIdeal A ∨ n i = 1)
    (s : Fin b → A)
    (hsPrimeOrUnit : ∀ i, Prime (s i) ∨ IsUnit (s i))
    (hCharZero : ∀ i, Prime (s i) →
      CharZero (A ⧸ Ideal.span {s i}))
    (f : A) (hAssoc : Associated f (∏ i, s i))
    (hAhatDomain :
      IsDomain (AdicCompletion (maximalIdeal A) A))
    (hAhatNoetherian :
      IsNoetherianRing (AdicCompletion (maximalIdeal A) A))
    (hPrimeMap : ∀ i, Prime (s i) →
      Prime (algebraMap A (AdicCompletion (maximalIdeal A) A) (s i)))
    {E : Type uE} [CommRing E]
    [Algebra (iteratedRadical A r n a) E]
    [Algebra A E]
    [IsScalarTower A (iteratedRadical A r n a) E]
    [Module.Finite (iteratedRadical A r n a) E]
    [Algebra.Etale (iteratedRadical A r n a) E]
    (p : Ideal E) [p.IsMaximal]
    [hpOver :
      letI : IsLocalRing (iteratedRadical A r n a) :=
        isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
      p.LiesOver (maximalIdeal (iteratedRadical A r n a))]
    (hAway :
      (Localization.awayMap
        (algebraMap A (Localization.AtPrime p)) f).Etale) :
    ∀ i, IsUnit (n i : A) := by
  let Ahat := AdicCompletion (maximalIdeal A) A
  let aHat : Fin r → Ahat := fun i ↦ algebraMap A Ahat (a i)
  let sHat : Fin b → Ahat := fun i ↦ algebraMap A Ahat (s i)
  let B₀ := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n aHat
  have hstageHat : ∀ i,
      aHat i ∈ maximalIdeal Ahat ∨ n i = 1 := by
    intro i
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  let : IsDomain Ahat := hAhatDomain
  let : IsNoetherianRing Ahat := hAhatNoetherian
  let : IsLocalRing B₀ :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n aHat hn hstageHat
  let : Module.Finite A B₀ := finite_iteratedRadical n a hn
  let : Algebra B₀ Bhat := iteratedRadicalCompletionAlgebra n a
  let aBhatAlgebra : Algebra A Bhat :=
    ((algebraMap Ahat Bhat).comp (algebraMap A Ahat)).toAlgebra
  let : Algebra A Bhat := aBhatAlgebra
  let : IsScalarTower A Ahat Bhat :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B₀ Bhat :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap Ahat Bhat (algebraMap A Ahat x) =
        algebraMap B₀ Bhat (algebraMap A B₀ x)
      exact (iteratedRadicalCompletion_algebraMap_comp_apply n a x).symm
  let : Module.FaithfullyFlat B₀ Bhat :=
    faithfullyFlat_iteratedRadicalCompletion n a
  have hclosed :=
    iteratedRadicalCompletion_closedPointGeometry_of_mem_or_eq_one
      n a hn hstage
  have hmax : (maximalIdeal B₀).map (algebraMap B₀ Bhat) =
      maximalIdeal Bhat := by
    simpa only [Ahat, B₀, Bhat, aHat] using hclosed.1
  have hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap B₀ Bhat)) := by
    simpa only [Ahat, B₀, Bhat, aHat] using hclosed.2
  let : IsLocalHom (algebraMap B₀ Bhat) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap B₀ Bhat)).out 3 1).mp <| by
      rw [hmax]
  let tensor := Ahat ⊗[A] B₀
  let : Algebra B₀ tensor := Algebra.TensorProduct.rightAlgebra
  let ePush : tensor ≃ₐ[B₀] Bhat :=
    iteratedRadicalCompletionRightAlgEquiv n a
  let : Algebra.IsPushout A B₀ Ahat Bhat := by
    apply Algebra.IsPushout.of_equiv ePush
    ext x
    change (iteratedRadicalCompletionBaseChangeAlgEquiv n a)
        (algebraMap Ahat tensor x) = algebraMap Ahat Bhat x
    exact (iteratedRadicalCompletionBaseChangeAlgEquiv n a).commutes x
  have hmaxFG : (maximalIdeal Ahat).FG := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.FG.map
      (maximalIdeal A).fg_of_isNoetherianRing (algebraMap A Ahat)
  let : HenselianLocalRing Bhat :=
    henselianLocalRing_iteratedRadical_of_isAdicComplete_of_fg_of_mem_or_eq_one
      hmaxFG n aHat hn hstageHat
  have hsHat : ∀ i, Prime (sHat i) ∨ IsUnit (sHat i) := by
    intro i
    rcases hsPrimeOrUnit i with hsPrime | hsUnit
    · exact Or.inl (hPrimeMap i hsPrime)
    · exact Or.inr (hsUnit.map (algebraMap A Ahat))
  have hCharZeroHat : ∀ i, Prime (sHat i) →
      CharZero (Ahat ⧸ Ideal.span {sHat i}) := by
    intro i hsHatPrime
    rcases hsPrimeOrUnit i with hsPrime | hsUnit
    · have hzero :=
        charZero_quotient_mappedIdeal_maximalAdicCompletion
          (Ideal.span ({s i} : Set A)) (hCharZero i hsPrime)
      have hmap :
          (Ideal.span ({s i} : Set A)).map (algebraMap A Ahat) =
            Ideal.span ({algebraMap A Ahat (s i)} : Set Ahat) := by
        rw [Ideal.map_span]
        congr 1
        simp
      rw [← hmap]
      exact hzero
    · exact (hsHatPrime.not_isUnit
        (hsUnit.map (algebraMap A Ahat))).elim
  have hAssocHat : Associated (algebraMap A Ahat f)
      (∏ i, sHat i) := by
    simpa only [sHat] using
      associated_fintypeProduct_maximalAdicCompletion f s hAssoc
  have hunitHat : ∀ i, IsUnit (n i : Ahat) := by
    exact
      (
all_exponents_isUnit_of_finiteEtale_samePrime_boundaryAway_primeOrUnit_of_finite_henselianPushout
        (A₀ := A) (B₀ := B₀) (A := Ahat) (E := E)
        p n aHat hn hstageHat sHat hsHat hCharZeroHat
          f hAssocHat hAway hmax hres)
  intro i
  apply (isUnit_map_iff (algebraMap A Ahat) (n i : A)).mp
  simpa using hunitHat i

end EtaleFundamentalGroups.Kummer

end
