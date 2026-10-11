/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.CategoryTheory.CommAlgRingMap
import EtaleFundamentalGroups.Inertia.FiniteIdealRadicalTameDivisibility
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import SchemeTheory.Normalization.IntegralClosureAutomorphisms
import SchemeTheory.Normalization.NativeNormalizationPrime

/-!
# Radical exponents and finite normalization tame orders

The actual finite Galois normalization supplies the finite-action hypotheses
used to compare a uniformizer radical exponent with its tame inertia order.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Actual finite Galois normalization supplies all finite-action facts
before the prime and radical are introduced. The resulting divisibility
refers to its intrinsic tame character and its original coefficient map. -/
theorem finiteNormalization_radical_exponent_dvd_tameOrder
    (A : Type u) (K : Type v) (C : Type w)
    [rA : CommRing A] [dA : IsDomain A] [vA : IsDiscreteValuationRing A]
    [fK : Field K] [fC : Field C]
    [aAK : Algebra A K] [fAK : IsFractionRing A K]
    [aKC : Algebra K C] [aAC : Algebra A C] [tAKC : IsScalarTower A K C]
    [fKC : FiniteDimensional K C] [gKC : IsGalois K C] :
    let : IsDedekindDomain (normalizationCommAlgCat A C) :=
      integralClosure.isDedekindDomain A K C
    ∀ (Q : Ideal (normalizationCommAlgCat A C)) [Q.IsPrime] (hQ : Q ≠ ⊥)
      (n : ℕ), IsUnit (n : A) → ∀ (π : A), Irreducible π →
      ∀ (γ : normalizationCommAlgCat A C),
      γ ^ n = (commAlgCoefficientMap (normalizationCommAlgCat A C)).toFun π →
      n ∣ commAlgIdealTameOrder A (normalizationCommAlgCat A C) Q hQ := by
  let B : CommAlgCat.{w} A := normalizationCommAlgCat A C
  have dB : IsDedekindDomain B := integralClosure.isDedekindDomain A K C
  have tAC : Module.IsTorsionFree A C := .trans_faithfulSMul A K C
  have tAB : Module.IsTorsionFree A B :=
    inferInstanceAs (Module.IsTorsionFree A (integralClosure A C))
  have fAB : Module.Finite A B :=
    nativeNormalization_finite A K (CommAlgCat.of A C) (Field.toIsField C)
  have gAB : IsGaloisGroup (B ≃ₐ[A] B) A B :=
    integralClosure_automorphisms_isGaloisGroup A K C
  change ∀ (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (n : ℕ), IsUnit (n : A) → ∀ (π : A), Irreducible π → ∀ (γ : B),
    γ ^ n = (commAlgCoefficientMap B).toFun π → n ∣ commAlgIdealTameOrder A B Q hQ
  clear_value B
  clear tAC gKC fKC tAKC aAC aKC fAK aAK fC C fK K
  intro Q qPrime hQ n hn π hπ γ hγ
  have hmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
  have hbaseMax : (Q.under A).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  have hover : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal hbaseMax).symm⟩
  exact radical_exponent_dvd_finiteIdealTameOrder A B Q hQ n hn π hπ γ hγ

end EtaleFundamentalGroups.Inertia

end
