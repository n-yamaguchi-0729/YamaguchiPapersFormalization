/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.Conditional.SamePrimeExponentUnit
import Nyll.EtaleFundamentalGroups.Kummer.Completions.MaximalAdic.RegularPairNoetherian
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightTwo.PrimeRootCover
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Intermediate.ExponentUnit

/-!
# Same-prime completion from a global primitive Away map

The earlier same-prime completion bridge starts with a primitive Away map
to the localization `E_p` of a finite-etale algebra.  Such a localization
need not be finite before completion when the source local ring is not
Henselian.

For the normalization applications the naturally produced statement is
instead the global map to `E`.  This file base-changes that global map first
and localizes only after passing to the Henselian completed root cover.  The
localization at the mapped closed prime is then finite, so it is an honest
target for the complete chosen-factor obstruction.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing

universe uA₀ uB₀ uA uE

/-- A global primitive Away map survives a finite Henselian pushout and
localization at the exact mapped closed prime.

Unlike `finiteEtale_samePrime_boundaryAway_of_finite_henselianPushout`, the
input is the map to the global finite-etale algebra `E`, not to `E_p`.
Consequently no finiteness or etaleness assertion for the non-Henselian
localization `E_p` is needed. -/
theorem
    finiteEtale_samePrime_boundaryAway_of_global_finite_henselianPushout
    {A₀ : Type uA₀} {B₀ : Type uB₀}
    {A : Type uA} {B : Type*} {E : Type uE}
    [CommRing A₀] [CommRing B₀] [CommRing A] [CommRing B]
    [CommRing E]
    [IsNoetherianRing A]
    [IsLocalRing B₀] [HenselianLocalRing B]
    [Algebra A₀ B₀] [Algebra A₀ A]
    [Algebra A₀ B] [Algebra A B] [Algebra B₀ B]
    [IsScalarTower A₀ B₀ B] [IsScalarTower A₀ A B]
    [Algebra.IsPushout A₀ B₀ A B]
    [IsLocalHom (algebraMap B₀ B)]
    [Module.FaithfullyFlat B₀ B]
    [Module.Finite A₀ B₀]
    [Algebra B₀ E] [Algebra A₀ E]
    [IsScalarTower A₀ B₀ E]
    [Module.Finite B₀ E] [Algebra.Etale B₀ E]
    (p : Ideal E) [p.IsMaximal]
    [p.LiesOver (maximalIdeal B₀)]
    (hmax : (maximalIdeal B₀).map (algebraMap B₀ B) =
      maximalIdeal B)
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap B₀ B)))
    (f : A₀)
    (hAway :
      (Localization.awayMap (algebraMap A₀ E) f).Etale) :
    let T := B ⊗[B₀] E
    letI : Algebra E T := Algebra.TensorProduct.rightAlgebra
    let p' := p.map (algebraMap E T)
    let hp' : p'.IsMaximal :=
      (tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
        (R := B₀) (R' := B) (S := E) p hmax hres).1
    letI : p'.IsPrime := hp'.isPrime
    let hp'Over : p'.LiesOver (maximalIdeal B) :=
      (tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
        (R := B₀) (R' := B) (S := E) p hmax hres).2
    letI : p'.LiesOver (maximalIdeal B) := hp'Over
    let D := Localization.AtPrime p'
    letI : CommRing D := OreLocalization.instCommRing
    @Algebra.Etale
      (Localization.Away (algebraMap A₀ A f))
      (Localization.Away (algebraMap A D (algebraMap A₀ A f)))
      (OreLocalization.instCommRing (R := A))
      (OreLocalization.instCommRing (R := D))
      (Localization.awayMap
        (algebraMap A D) (algebraMap A₀ A f)).toAlgebra := by
  dsimp only
  let T := B ⊗[B₀] E
  let : Algebra B T := Algebra.TensorProduct.leftAlgebra
  let : Algebra E T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B₀ B T := inferInstance
  let : IsScalarTower B₀ E T :=
    Algebra.TensorProduct.right_isScalarTower
  let : Algebra A T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower A B T :=
    TensorProduct.isScalarTower_left
  let : Module.Finite A (A ⊗[A₀] B₀) :=
    Module.Finite.base_change A₀ A B₀
  let : Algebra.IsPushout A₀ A B₀ B :=
    Algebra.IsPushout.symm
      (inferInstance : Algebra.IsPushout A₀ B₀ A B)
  let : Module.Finite A B :=
    Module.Finite.equiv
      (Algebra.IsPushout.equiv A₀ A B₀ B).toLinearEquiv
  let p' := p.map (algebraMap E T)
  have hgeometry :=
    tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R := B₀) (R' := B) (S := E) p hmax hres
  let : p'.IsPrime := hgeometry.1.isPrime
  let : p'.LiesOver (maximalIdeal B) := hgeometry.2
  let D := Localization.AtPrime p'
  let : Algebra T D := inferInstance
  let : IsScalarTower B T D :=
    OreLocalization.instIsScalarTower
  have hTowerABD : IsScalarTower A B D :=
    IsScalarTower.to₁₂₄ A B T D
  let : Algebra A₀ T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower A₀ A T :=
    IsScalarTower.to₁₂₄ A₀ A B T
  let : IsScalarTower A₀ E T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap A₀ T x = algebraMap B T (algebraMap A₀ B x) :=
        IsScalarTower.algebraMap_apply A₀ B T x
      _ = algebraMap B T (algebraMap B₀ B (algebraMap A₀ B₀ x)) := by
        rw [IsScalarTower.algebraMap_apply A₀ B₀ B]
      _ = algebraMap B₀ T (algebraMap A₀ B₀ x) :=
        (IsScalarTower.algebraMap_apply B₀ B T _).symm
      _ = algebraMap E T (algebraMap B₀ E (algebraMap A₀ B₀ x)) :=
        IsScalarTower.algebraMap_apply B₀ E T _
      _ = algebraMap E T (algebraMap A₀ E x) := by
        rw [IsScalarTower.algebraMap_apply A₀ B₀ E]
  have hSecondPushout : Algebra.IsPushout B₀ E B T :=
    (inferInstance : Algebra.IsPushout B₀ B E T).symm
  have hTotalPushout : Algebra.IsPushout A₀ E A T :=
    (Algebra.IsPushout.comp_iff A₀ B₀ A B).2 hSecondPushout
  let : Algebra.IsPushout A₀ E A T := hTotalPushout
  have hAwayBaseChange :
      (Localization.awayMap
        (algebraMap A T) (algebraMap A₀ A f)).Etale :=
    localization_awayMap_etale_of_isPushout
      (A := A₀) (B := E) (C := A) (D := T) f hAway
  let : IsScalarTower A T D :=
    IsScalarTower.to₁₃₄ A B T D
  let : IsLocalization p'.primeCompl D := inferInstance
  let : Algebra.FormallyEtale T D :=
    Algebra.FormallyEtale.of_isLocalization p'.primeCompl
  let : Module.Finite B D :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale p'
  have hFiniteAD : Module.Finite A D :=
    @Module.Finite.trans A B D _ _ _ _ _ _ hTowerABD
      inferInstance inferInstance
  let : Module.Finite A D := hFiniteAD
  exact
    localization_awayMap_etale_of_finite_formallyEtale_extension
      (A := A) (C := T) (D := D)
      (algebraMap A₀ A f) hAwayBaseChange

/-- The complete chosen-factor exponent obstruction with a global primitive
Away input on the precompletion finite-etale algebra. -/
theorem
    all_exponents_isUnit_of_global_samePrime_boundaryAway_henselianPushout
    {A₀ : Type uA₀} {B₀ : Type uB₀}
    {A : Type uA} {E : Type uE}
    [CommRing A₀] [CommRing B₀] [CommRing A] [CommRing E]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalRing B₀]
    [Algebra A₀ B₀] [Algebra A₀ A]
    [Module.Finite A₀ B₀]
    [Algebra B₀ E] [Algebra A₀ E]
    [IsScalarTower A₀ B₀ E]
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
      (Localization.awayMap (algebraMap A₀ E) f₀).Etale) :
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
  let : Algebra A T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower A B T :=
    TensorProduct.isScalarTower_left
  let p' := p.map (algebraMap E T)
  have hgeometry :=
    tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R := B₀) (R' := B) (S := E) p hmax hres
  let : p'.IsPrime := hgeometry.1.isPrime
  let : p'.LiesOver (maximalIdeal B) := hgeometry.2
  let D := Localization.AtPrime p'
  let : Algebra T D := inferInstance
  let : IsScalarTower B T D :=
    OreLocalization.instIsScalarTower
  let : IsScalarTower A B D :=
    IsScalarTower.to₁₂₄ A B T D
  have hAwayCompleted :=
    finiteEtale_samePrime_boundaryAway_of_global_finite_henselianPushout
      (A₀ := A₀) (B₀ := B₀) (A := A) (B := B) (E := E)
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
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
        (algebraMap B D) (fun x ↦ Algebra.IsIntegral.isIntegral x) Q <| by
          rw [← Ideal.under_def, ← Q.over_def (maximalIdeal B)]
          exact maximalIdeal.isMaximal B
    exact IsLocalRing.eq_maximalIdeal hQMaximal
  exact
    all_exponents_isUnit_of_completeChosenFactor_boundaryAway_primeOrUnit_universe
      (A := A) n a hn hstage s hsPrimeOrUnit hCharZero
      (algebraMap A₀ A f₀) hAssoc (D := D) qD hunique hAwayCompleted

/-- Maximal-adic completion of a conditional radical, starting from a
global primitive Away map on its finite-etale factor. -/
theorem
    all_exponents_isUnit_of_conditionalIteratedRadical_samePrime_global_completion
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
    (hAhatDomain : IsDomain (AdicCompletion (maximalIdeal A) A))
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
    (hAway : (Localization.awayMap (algebraMap A E) f).Etale) :
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
      all_exponents_isUnit_of_global_samePrime_boundaryAway_henselianPushout
        (A₀ := A) (B₀ := B₀) (A := Ahat) (E := E)
        p n aHat hn hstageHat sHat hsHat hCharZeroHat
          f hAssocHat hAway hmax hres
  intro i
  apply (isUnit_map_iff (algebraMap A Ahat) (n i : A)).mp
  simpa using hunitHat i

/-- One-root specialization of the global-Away same-prime terminal. -/
theorem exponent_isUnit_of_oneRoot_samePrime_global_completion
    {A : Type uA} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    {N : ℕ} (hN : 0 < N) {y : A} (hy : Prime y)
    (hyQuot : IsRegularLocalRing (A ⧸ Ideal.span ({y} : Set A)))
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A)))
    {E : Type uE} [CommRing E]
    [Algebra
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    [Algebra A E]
    [IsScalarTower A
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    [Module.Finite
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    [Algebra.Etale
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) E]
    (p : Ideal E) [p.IsMaximal]
    [hpOver :
      letI : IsLocalRing
          (iteratedRadical A 1
            (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)) :=
        isLocalRing_iteratedRadical
          (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)
          (fun _ ↦ hN) (fun _ ↦ by
            rw [mem_maximalIdeal]
            exact hy.not_isUnit)
      p.LiesOver
        (maximalIdeal
          (iteratedRadical A 1
            (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ y)))]
    (hAway : (Localization.awayMap (algebraMap A E) y).Etale) :
    IsUnit (N : A) := by
  obtain ⟨z, hreg, hgen⟩ :=
    exists_regular_pair_of_prime_regular_quotient_dimension_two
      hy hyQuot hdim
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → A := fun _ ↦ y
  let s : Fin 1 → A := fun _ ↦ y
  have hn : ∀ i, 0 < n i := by
    intro i
    simpa [n] using hN
  have hstage : ∀ i, a i ∈ maximalIdeal A ∨ n i = 1 := by
    intro i
    left
    rw [mem_maximalIdeal]
    simpa [a] using hy.not_isUnit
  let : IsLocalRing (iteratedRadical A 1 n a) :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  have hsPrimeOrUnit : ∀ i, Prime (s i) ∨ IsUnit (s i) := by
    intro i
    exact Or.inl (by simpa [s] using hy)
  have hCharZeroS : ∀ i, Prime (s i) →
      CharZero (A ⧸ Ideal.span {s i}) := by
    intro i _
    simpa [s] using hCharZero
  have hAssoc : Associated y (∏ i, s i) := by
    simp [s]
  have hcompletion :=
    maximalAdicCompletion_regularPair_geometry hreg hgen
  have hall :=
    all_exponents_isUnit_of_conditionalIteratedRadical_samePrime_global_completion
      (A := A) n a hn hstage s hsPrimeOrUnit hCharZeroS
        y hAssoc hcompletion.1
        (maximalAdicCompletion_isNoetherianRing_of_regularPair hreg hgen)
        (fun i _ ↦ by simpa [s] using hcompletion.2.2.2.1)
        (E := E) p hAway
  simpa [n] using hall (0 : Fin 1)

/-- `AdjoinRoot` presentation of the global-Away one-root terminal. -/
theorem exponent_isUnit_of_adjoinRoot_samePrime_global_completion
    {A : Type uA} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    {N : ℕ} (hN : 0 < N) {y : A} (hy : Prime y)
    (hyQuot : IsRegularLocalRing (A ⧸ Ideal.span ({y} : Set A)))
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A)))
    {E : Type uE} [CommRing E]
    [Algebra (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Algebra A E]
    [IsScalarTower A
      (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Module.Finite (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [Algebra.Etale (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)) E]
    [IsLocalRing (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y))]
    (p : Ideal E) [p.IsMaximal]
    [p.LiesOver
      (maximalIdeal
        (AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)))]
    (hAway : (Localization.awayMap (algebraMap A E) y).Etale) :
    IsUnit (N : A) := by
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → A := fun _ ↦ y
  let B := iteratedRadical A 1 n a
  let D := AdjoinRoot (Polynomial.X ^ N - Polynomial.C y)
  have hn : ∀ i, 0 < n i := by
    intro i
    simpa [n] using hN
  have ha : ∀ i, a i ∈ maximalIdeal A := by
    intro i
    rw [mem_maximalIdeal]
    simpa [a] using hy.not_isUnit
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let e : B ≃ₐ[A] D := by
    simpa only [B, D, n, a] using oneIteratedRadicalAlgEquiv A N y
  let bDAlgebra : Algebra B D := e.toRingEquiv.toRingHom.toAlgebra
  let : Algebra B D := bDAlgebra
  let : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (e.commutes z).symm
  let bEAlgebra : Algebra B E :=
    ((algebraMap D E).comp (algebraMap B D)).toAlgebra
  let : Algebra B E := bEAlgebra
  let : IsScalarTower B D E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B E := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    calc
      algebraMap A E z = algebraMap D E (algebraMap A D z) :=
        IsScalarTower.algebraMap_apply A D E z
      _ = algebraMap D E (algebraMap B D (algebraMap A B z)) := by
        rw [← IsScalarTower.algebraMap_apply A B D]
      _ = algebraMap B E (algebraMap A B z) := rfl
  let eB : B ≃ₐ[B] D :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun _ ↦ rfl)
  let : Module.Finite B D :=
    Module.Finite.of_surjective eB.toLinearMap eB.surjective
  let : Module.Finite B E := Module.Finite.trans D E
  let : Algebra.Etale B D := Algebra.Etale.of_equiv eB
  let : Algebra.Etale B E := Algebra.Etale.comp B D E
  let : IsLocalHom (algebraMap B D) :=
    IsLocalHom.of_surjective (algebraMap B D) e.surjective
  let : (maximalIdeal D).LiesOver (maximalIdeal B) :=
    Ideal.LiesOver.mk
      (IsLocalRing.maximalIdeal_comap (algebraMap B D)).symm
  let : p.LiesOver (maximalIdeal B) :=
    Ideal.LiesOver.trans p (maximalIdeal D) (maximalIdeal B)
  exact
    exponent_isUnit_of_oneRoot_samePrime_global_completion
      (A := A) hN hy hyQuot hdim hCharZero (E := E) p hAway

end EtaleFundamentalGroups.Kummer

end
